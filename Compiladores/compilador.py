import xml.etree.ElementTree as ET
import csv

arquivo_tokens = list(open('configuracao/tks.txt'))
codigo_programador  = list(open('configuracao/codigo.txt'))
arvore = ET.parse('configuracao/parsing.xml')
root = arvore.getroot()

block, vivos, alcan, regras_finais, fita, escopo, simbolos, estados, tabela_simbolos, fita_saida = [], [], [], [], [], [], [], [], [], []
epTransicao, gramatica, simbolo_redu, tabela = {}, {}, {}, {}
repeticao = 0


def eliminar_mortos():
    mortos = []
    for x in tabela:
        if x not in vivos and x != '€': #adiciona a regra aos mortos caso não esteja em vivos e não seja €
            mortos.append(x)

    for x in mortos:
        del tabela[x]   #deleta da tabela os mortos


def buscar_vivos():
    mudou = False

    for regra in tabela:
        for simbolo in tabela[regra]:
            if tabela[regra][simbolo][0] in vivos and regra not in vivos:
                vivos.append(regra) # se o simbolo esta em vivos e a regra não está, add em vivos a regra
                mudou = True

    if mudou:
        buscar_vivos()  #chama novamente, mudando a flag no inicio da funcao


def eliminar_inalcansaveis():
    loop = {}
    loop.update(tabela)
    for regra in loop:
        if regra not in alcan:  #remove regra da tabela se não estiverem em alcan
            del tabela[regra]


def buscar_alcansaveis(estado):
    if estado not in alcan: #adiciona estado no alcan caso n esteja
        alcan.append(estado)
        for simbolo in tabela[estado]: #passa por cada simbolo de estado da tabela 
            if tabela[estado][simbolo] and tabela[estado][simbolo][0] not in alcan: #continua adicionando os simbolos em alcan
                buscar_alcansaveis(tabela[estado][simbolo][0])


def encontrar_eps_set(e_transicoes):    #encontra os estados que possuem o epsilon
    for x in e_transicoes:
        for y in tabela[x]['&']:
            if y not in e_transicoes:
                e_transicoes.append(y)
    return e_transicoes


def eliminar_et():
    for regra in tabela:
        et_set = encontrar_eps_set(tabela[regra]['&'])
        for estado in et_set:
            if estado in regras_finais: #verifica se o estado que possui & está nos regras_finais, se não está add
                regras_finais.append(regra)
            for simbolo in tabela[estado]:
                for transicao in tabela[estado][simbolo]:   #verifica a transicao do estado e add na tabela caso ela não esteja
                    if transicao not in tabela[regra][simbolo]:
                        tabela[regra][simbolo].append(transicao)
        tabela[regra]['&'] = []


def criar_novos(nstates):
    for x in nstates:
        tabela[x] = {}
        estados.append(x)   #salva o novo estado na tabela de estados
        for y in simbolos:
            tabela[x][y] = []
        tabela[x]['&'] = []

    for state in nstates:
        estadosjuntar = sorted(state.split(':'))
        for x in estadosjuntar:
            if x in regras_finais and state not in regras_finais: #faz uma nova verificação se está nos regras_finais, caso não esteja adiciona
                regras_finais.append(state)
            for simbolo in simbolos:
                for transition in tabela[x][simbolo]:
                    if not tabela[state][simbolo].__contains__(transition): #verifica se existe na tabela e add caso não esteja
                        tabela[state][simbolo].append(transition)
    determizinar() #verifica novamente


def determizinar():
    novosestados = []
    for regra in tabela:
        for producao in tabela[regra]:
            if len(tabela[regra][producao]) > 1:    #busca pela regra com mais de 1 producao
                novo = []
                for estado in tabela[regra][producao]:
                    if ':' in estado:
                        for aux in estado.split(':'):   #verifica e divide se tem mais regra
                            if aux not in novo:
                                novo.append(aux)    #adiciona na variavel nova
                    else:
                        if estado not in novo:
                            novo.append(estado) #adiciona na varivel nova

                if novo:
                    novo = sorted(novo)
                    novo = ':'.join(novo)   #cria nova regra
                if novo and novo not in novosestados and novo not in list(tabela.keys()):
                    novosestados.append(novo)
                tabela[regra][producao] = novo.split() #salva na tabela a nova regra
    if novosestados:
        criar_novos(novosestados)


def criar_automato_finitos(): #cria automato finito
    for x in gramatica:
        tabela[x] = {}
        estados.append(x)   #pega todos estados da lista de gramatica
        for y in simbolos:
            tabela[x][y] = []
        tabela[x]['&'] = [] #limpado o estado do &
    

    for regra in gramatica:
        for producao in gramatica[regra]:
            if len(producao) == 1 and producao.islower() and regra not in regras_finais:
                regras_finais.append(regra)    #adiciona a regra nas regras regras_finais caso seja = 1, minuscula e já n esteja nas regras_finais
            elif producao == '&' and regra not in regras_finais:
                regras_finais.append(regra)    #adiciona $ nas regras_finais
            elif producao[0] == '<':
                tabela[regra]['&'].append(producao.split('<')[1][:-1]) #remove <> da regra e adiciona o que tem entre eles
            elif producao != '&':
                tabela[regra][producao[0]].append(producao.split('<')[1][:-1])  #remove <> da regra e inicial


def criar_sn(s):
    global repeticao
    if 'S' + str(repeticao) in gramatica:
        return
    gramatica['S' + str(repeticao)] = s.replace('\n', '').split(' ::= ')[1].replace('>', str(repeticao) + '>').split(' | ')


def tratar_gramatica(gram, s):
    global repeticao #aux numero de repetições
    gram = gram.replace('\n', '')
    for x in gram.split(' ::= ')[1].replace('<', '').replace('>', '').split(' | '): #separa letra da regra na posicao 0
        if x[0] not in simbolos and not x[0].isupper(): #verifica se não esta em simbolos e se não é maiuscula 
            simbolos.append(x[0])   #salva em simbolos
    regra = gram.split(' ::= ')[0].replace('>', str(repeticao)).replace('<', '') #concatena letra da regra + número da repetição
    
    if regra[0] == 'S': #se a regra for S, repeticao+1
        repeticao += 1
        gramatica['S'] += gram.split(' ::= ')[1].replace('>', str(repeticao) + '>').split(' | ')    #concatena na linha as próximas regras, ex: S0::=aS1
    else:
        gramatica[regra] = gram.split(' ::= ')[1].replace('>', str(repeticao)+'>').split(' | ')  

    if '<S>' in gram.split(' ::= ')[1]:
        criar_sn(s)


def tratar_token(token):
    token = token.replace('\n', '') #replace a cada \n pra pegar o token
    cp_token = token
    token = list(token) #quebra o token em caracteres
    for x in range(len(token)):
        if token[x] not in simbolos and not token[x].isupper(): #joga os caracteres dos tokens pra dentro de simbolos
            simbolos.append(token[x])

        if len(token) == 1:
            iniregra = '<' + cp_token.upper() + '>'
            gramatica['S'] += str(token[x] + iniregra).split() #salva na gramatica as regras de tamanho 1
            gramatica[cp_token.upper()] = []
            regras_finais.append(cp_token.upper()) #salva na lista os tokens de tamanho 1
        elif x == 0 and x != len(token)-1:
            iniregra = '<' + cp_token.upper() + '1>'
            gramatica['S'] += str(token[x] + iniregra).split()  #salva na gramatica as regras de tamanho maior que 1 / o inicio deles
        elif x == len(token)-1:
            finregra = '<' + cp_token.upper() + '>'
            gramatica[cp_token.upper() + str(x)] = str(token[x] + finregra).split() #salva na gramatica as regras de tamanho maior que 1 / o fim deles
            gramatica[cp_token.upper()] = []
            regras_finais.append(cp_token.upper()) #salva na lista os tokens de tamanho maior que 1
        else:
            proxregra = '<' + cp_token.upper() + str(x+1) + '>'
            gramatica[cp_token.upper() + str(x)] = str(token[x] + proxregra).split() #salva na gramatica as regras de tamanho maior que 1 / o meio fim deles


def criar_csv():
    with open('afnd.csv', 'w', newline='') as f:
        w = csv.writer(f)
        copydict = {}
        copydict.update(tabela)
        w.writerow(list(copydict['S'].keys()) + ['regra'])
        for x in copydict:
            if x in regras_finais:
                copydict[x]['nomeregra'] = x + '&' #adiciona nome da regra concatenado com o epsilon
            else:
                copydict[x]['nomeregra'] = x #se não for final, não concatena com o epsilon
            w.writerow(copydict[x].values())


def estado_erro():
    tabela['€'] = {}
    for y in simbolos:
        tabela['€'][y] = [] #adiciona todos os simbolos no € como posição
    tabela['€']['&'] = []   #epsilon também
    for regra in tabela:
        for simbolo in tabela[regra]:
            if not tabela[regra][simbolo]:
                tabela[regra][simbolo] = ['€']  #adicona € nas posições do simbolo da regra com valor nulo


def analisador_lexico():
    separadores = [' ', '\n', '\t', '+', '-', '{', '}', '#', ';']
    espacadores = [' ', '\n', '\t']
    operadores  = ['+', '-', '#', ';']
    id = 0
    for idx, linha in enumerate(codigo_programador): #pega numero da linha e código de cada linha
        E = 'S'
        string = ''
        for char in linha:
            if char in operadores and string:   #caso lemos um operador e a string não está vazia
                if string[-1] not in operadores:    #se o ultimo caracter não é um operador
                    if E in regras_finais: #a regra do caracter lido é um dos regras_finais
                        tabela_simbolos.append({'Line': idx, 'State': E, 'Label': string}) 
                        fita_saida.append(E) #adicionamos a regra na fita de saida
                    else:
                        tabela_simbolos.append({'Line': idx, 'State': 'Error', 'Label': string})
                        fita_saida.append('Error')
                    E = tabela['S'][char][0]    #mapeamento para a próxima estrutura de operadores
                    string = char
                    id += 1
                else:   #se o último caractere é um operador
                    string += char  #adiciona na string o caracter e continua normalmente
                    if char not in simbolos:
                        E = '€'
                    else:
                        E = tabela[E][char][0]
            elif char in separadores and string:
                if E in regras_finais:
                    tabela_simbolos.append({'Line': idx, 'State': E, 'Label': string}) #adiciona em tabela_simbolos linha, estado e descricao
                    fita_saida.append(E) #caso seja um final, adiciona na fita de saida
                else:
                    tabela_simbolos.append({'Line': idx, 'State': 'Error', 'Label': string})
                    fita_saida.append('Error')
                E = 'S'
                string = ''
                id += 1
            else:
                if char in espacadores: #se for um espaçador, continua
                    continue
                if char not in separadores and char not in operadores and string:   #caso n seja um separador, operador e já exista algo na string
                    if string[-1] in operadores:    #caso não seja um separador ele somente incrementa na string
                        if E in regras_finais: #operado é um final
                            tabela_simbolos.append({'Line': idx, 'State': E, 'Label': string})
                            fita_saida.append(E)
                        else:
                            tabela_simbolos.append({'Line': idx, 'State': 'Error', 'Label': string})
                            fita_saida.append('Error')
                        E = 'S'
                        string = ''
                        id += 1
                string += char
                if char not in simbolos:    #caso o caracter não esteja na tabela de simbolos
                    E = '€'
                else:
                    E = tabela[E][char][0]  #o E recebe a regra do caracter 
    tabela_simbolos.append({'Line': idx, 'State': 'EOF', 'Label': ''})
    fita_saida.append('EOF')
    erro = False
    for linha in tabela_simbolos:
        if linha['State'] == 'Error':   #caso exita erro léxico, imprime
            erro = True
            print('Erro léxico: linha {}, sentença "{}" não reconhecida!'.format(linha['Line']+1, linha['Label']))
    if erro:
        exit()  #finaliza caso exista erro


def mapeamento(symbols):
    symbols_indexes = {}    #é feito um reverso com o index x name
    for index, symbol in enumerate(symbols):
        symbols_indexes[symbol['Name']] = str(index)
        simbolo_redu[str(index)] = symbol['Name']
    for fta in fita_saida: #nos estados que eram nomes, sao alterados pelo indice para ser reconhecido sintaticamente
        if fta == 'S1' or fta == 'ENQUANTO1:S1' or fta == 'IGUAL1:S1': 
            fta = 'VAR' 
        elif fta == 'S2':
            fta = 'NUM'
        elif fta == '$':
            fta = 'EOF'
        fita.append(symbols_indexes[fta])

    for line in tabela_simbolos: #troca S1 e S2 na fita_saida por VAR e NUM
        if line['State'] == 'S1' or line['State'] == 'ENQUANTO1:S1' or line['State'] == 'IGUAL1:S1':
            line['State'] = 'VAR'
        elif line['State'] == 'S2':
            line['State'] = 'NUM'
        elif line['State'] == '$':
            line['State'] = 'EOF'


def analisador_sintatico(): #aqui é lido o arquivo_tokens xml pelas suas tags, nome, type, etc
    redux_symbol, symbols, productions, lalr_table, pilha  = [], [], [], [], ['0']

    def charge():
        xml_symbols = root.iter('Symbol')
        for symbol in xml_symbols:
            symbols.append({
                'Index': symbol.attrib['Index'],
                'Name': symbol.attrib['Name'],
                'Type': symbol.attrib['Type']
            })

        xml_productions = root.iter('Production')
        for production in xml_productions:
            productions.append({
                'NonTerminalIndex': production.attrib['NonTerminalIndex'],
                'SymbolCount': int(production.attrib['SymbolCount']),
            })

        lalr_states = root.iter('LALRState')
        for state in lalr_states:
            lalr_table.append({})
            for action in state:
                lalr_table[int(state.attrib['Index'])][str(action.attrib['SymbolIndex'])] = {
                    'Action': action.attrib['Action'],
                    'Value': action.attrib['Value']
                }

    def parser():
        idx = 0
        while True:
            ultimo_fita = fita[0]
            try:
                action = lalr_table[int(pilha[0])][ultimo_fita] #busca pelas acoes e valores
            except:
                print('Erro sintático: linha {}, sentença "{}" não reconhecida!'.format(tabela_simbolos[idx]['Line']+1, tabela_simbolos[idx]['Label']))
                exit()  #apresente o erro caso exista
                break

            if action['Action'] == '1':
                pilha.insert(0, fita.pop(0))    #remove da fita e add na pilha
                pilha.insert(0, action['Value'])
                idx += 1
            elif action['Action'] == '2':
                size = productions[int(action['Value'])]['SymbolCount'] * 2
                while size:
                    pilha.pop(0)
                    size -= 1
                redux_symbol.append(productions[int(action['Value'])]['NonTerminalIndex']) #adiciona não terminal na lista
                pilha.insert(0, productions[int(action['Value'])]['NonTerminalIndex'])  #insere na pilha tbm
                pilha.insert(0, lalr_table[int(pilha[1])][pilha[0]]['Value'])   
            elif action['Action'] == '3':
                print('salto')
            elif action['Action'] == '4':
                break

    def catch_statements(): #aqui é pego as declarações
        pilha_aux = [1]
        id = 1
        for symbol in redux_symbol:
            if simbolo_redu[symbol] == 'CONDS':
                id += 1
                pilha_aux.insert(0, id)
                block.append(pilha_aux[1])
            elif simbolo_redu[symbol] == 'REP' or simbolo_redu[symbol] == 'COND':
                pilha_aux.pop(0)
            elif simbolo_redu[symbol] == 'RVAR':
                escopo.append(pilha_aux[0])

    def complete_ts():  #completa a tabela de simbolos
        for token in tabela_simbolos:
            if token['State'] == 'VAR': #se o token for VAR
                token['Scope'] = escopo.pop(0)  # adiciona o escopo em que ela está

    charge()
    mapeamento(symbols)
    parser()
    catch_statements()
    complete_ts()


def analisador_semantico():
    var_scope = {}
    error = False

    def check_scope(scope_use, scope_dec):  #verifica se o escopo utilizado é o mesmo do escopo declarado
        if scope_use == scope_dec:
            return True
        elif scope_use == 1:
            return False
        else:
            return check_scope(block[scope_use-2], scope_dec)


    for index, token in enumerate(tabela_simbolos):
        if token['State'] == 'VAR' and tabela_simbolos[index-1]['State'] == 'DEF':
            if token['Label'] in var_scope: #caso a variável já esteja declarada
                error = True
                print('Erro semântico: linha {}, variável "{}" já declarada!'.format(token['Line']+1, token['Label']))
            else:
                var_scope[token['Label']] = token['Scope']  #adiciona o scopo da variavel

        if token['State'] == 'VAR' and tabela_simbolos[index-1]['State'] != 'DEF':
            if token['Label'] in var_scope:
                if not check_scope(token['Scope'], var_scope[token['Label']]):  #se o escopo n for o mesmo do declarado, erro
                    error = True
                    print('Erro semântico: linha {}, variável "{}" escopo inválido!'.format(token['Line']+1, token['Label']))
            else:
                error = True
                print('Erro semântico: linha {}, variável "{}" não declarada!'.format(token['Line']+1, token['Label']))
    if error:
        exit()

def codigo_intermediario():
    ts_code = []
    int_code = []

    def encontra_operacoes():
        flag = False
        operacao = []
        for idx, token in enumerate(tabela_simbolos):
            if token['State'] == 'VAR' and tabela_simbolos[idx+1]['State'] == '#' and tabela_simbolos[idx+1]['State'] != ';':  #se for atribuicao de variavel, VAR # 1 ;
                operacao.append(token['Label'])
                flag = True
            elif token['State'] == ';' and tabela_simbolos[idx-2]['State'] != 'DEF': #verifica se for definicao de variavel, def VAR;
                ts_code.append(operacao)
                operacao = []
                flag = False
            elif flag:
                operacao.append(token['Label'])


    def gera_temp(operacao, temp):
        flag = False
        cod, copy = [], []
        copy.extend(operacao)

        for idx in range(len(operacao)-1):  #pega inicio e fim da linha
            if operacao[idx+1] == '~' or operacao[idx+1] == '/':    #se for multiplicacao ou divisao
                for i in range(-1, 2):
                    cod.insert(0, copy[idx])    #salva em cod as proximas contas, a # 0 "~b/1" por exemplo
                    copy.pop(idx)
                copy.insert(idx, 'T' + str(temp))
                flag = True
                break

        if not flag:
            for idx in range(len(operacao)-1):
                if operacao[idx+1] == '+' or operacao[idx+1] == '-':    #caso seja soma ou subtracao
                    for i in range(-1, 2):
                        cod.insert(0, copy[idx])    #salva em cod as proximas contas
                        copy.pop(idx)
                    copy.insert(idx, 'T' + str(temp))
                    break

        cod.insert(0, '#')
        cod.insert(0, 'T'+str(temp))    #insere em T+numero qtd chamada da funcao as contas
        return copy, cod

    def gera_codigo():
        temp = 1
        for operacao in ts_code:
            while True:
                if len(operacao) == 3:  #se for uma operacao simples, a # 0;
                    cod = []
                    for x in range(len(operacao)):
                        cod.append(operacao[x]) #adiciona em cod a operacao 

                    int_code.append(cod)
                    break

                operacao, cod = gera_temp(operacao, temp)   #passa a operacao e o variavel aux parar se colocada em T1, T2, etc
                temp += 1
                int_code.append(cod) #salva no código intermediario

    def exporta_codigo():
        file = open('configuracao/codigo_intermediario.txt', 'w+')
        for x in int_code:  #exporta codigo intermediario para cada linha do arquivo_tokens
            file.write(str(x).replace('[','').replace(']','').replace("'",'').replace(',','') +'\n')

    encontra_operacoes()
    gera_codigo()
    exporta_codigo()


def main():
    gramatica['S'] = []
    estadoinicial = ''
    for x in arquivo_tokens: #le o arquivo_tokens
        if '<S> ::=' in x:
            estadoinicial = x
        if '::=' in x:
            tratar_gramatica(x, estadoinicial) #funcao que trata a gramatica
        else:
            tratar_token(x) #trata os tokens e salva na regra da gramatica
    criar_automato_finitos()  
    eliminar_et()
    determizinar()
    buscar_alcansaveis('S')
    eliminar_inalcansaveis()
    estado_erro()
    vivos.extend(regras_finais)    #adiciona as regras regras_finais ao vivos
    buscar_vivos()
    eliminar_mortos()
    criar_csv()
    analisador_lexico()
    analisador_sintatico()
    analisador_semantico()
    codigo_intermediario()
    print('Compilado com sucesso!')

print('\n')
main()