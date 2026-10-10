import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData1
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData2
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData0

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge32 : Integer.Sparse Master := [(Sum.inl 0, 164651885408747520000), (Sum.inl 1, 389238053905612800000), (Sum.inl 2, 128652226349875200000), (Sum.inl 5, -306643764820377600000), (Sum.inl 6, -113192044561612800000), (Sum.inl 9, -34848095875891200000), (Sum.inl 58, -113192044561612800000), (Sum.inl 70, 1192457960954265600000), (Sum.inl 256, 315825855528960000000), (Sum.inl 495, 689772938880614400000)]

def originalMerge32 : Integer.Sparse OriginalKey := originalMerge30 ++ originalMerge31

theorem reducedMerge32Check : reducedMerge32 = Integer.Sparse.mergeBy masterLess reducedMerge30 reducedMerge31 := by decide +kernel

def reducedMerge33 : Integer.Sparse Master := [(Sum.inl 0, 49033798420561920000), (Sum.inl 1, 206535144182169600000), (Sum.inl 2, 283419202590720000000), (Sum.inl 5, -173669991609139200000), (Sum.inl 6, -141932583681638400000), (Sum.inl 7, 478088048148480000000), (Sum.inl 8, 53807044696473600000), (Sum.inl 9, 288580528786636800000), (Sum.inl 35, 229924312960204800000), (Sum.inl 58, -127562314121625600000), (Sum.inl 69, 478088048148480000000), (Sum.inl 70, 1670546009102745600000), (Sum.inl 71, 107614089392947200000), (Sum.inl 256, 315825855528960000000), (Sum.inl 257, 229924312960204800000), (Sum.inl 495, 919697251840819200000)]

def originalMerge33 : Integer.Sparse OriginalKey := originalMerge29 ++ originalMerge32

theorem reducedMerge33Check : reducedMerge33 = Integer.Sparse.mergeBy masterLess reducedMerge29 reducedMerge32 := by decide +kernel

def reducedMerge34 : Integer.Sparse Master := [(Sum.inl 0, -5181342679941120000), (Sum.inl 1, 188329256943206400000), (Sum.inl 2, -2556334345420800000), (Sum.inl 9, 10225337381683200000), (Sum.inl 69, 619014162028953600000), (Sum.inl 71, -578112812502220800000)]

def originalMerge34 : Integer.Sparse OriginalKey := originalTerm36 ++ originalTerm37

theorem reducedMerge34Check : reducedMerge34 = Integer.Sparse.mergeBy masterLess reducedTerm36 reducedTerm37 := by decide +kernel

def reducedMerge35 : Integer.Sparse Master := [(Sum.inl 0, -543688205598720000), (Sum.inl 1, -31035127482777600000), (Sum.inl 2, -8381778318950400000), (Sum.inl 9, -78833811603456000000), (Sum.inl 58, -25371790191820800000), (Sum.inl 257, 90613396655308800000)]

def originalMerge35 : Integer.Sparse OriginalKey := originalTerm38 ++ originalTerm39

theorem reducedMerge35Check : reducedMerge35 = Integer.Sparse.mergeBy masterLess reducedTerm38 reducedTerm39 := by decide +kernel

def reducedMerge36 : Integer.Sparse Master := [(Sum.inl 0, -5725030885539840000), (Sum.inl 1, 157294129460428800000), (Sum.inl 2, -10938112664371200000), (Sum.inl 9, -68608474221772800000), (Sum.inl 58, -25371790191820800000), (Sum.inl 69, 619014162028953600000), (Sum.inl 71, -578112812502220800000), (Sum.inl 257, 90613396655308800000)]

def originalMerge36 : Integer.Sparse OriginalKey := originalMerge34 ++ originalMerge35

theorem reducedMerge36Check : reducedMerge36 = Integer.Sparse.mergeBy masterLess reducedMerge34 reducedMerge35 := by decide +kernel

def reducedMerge37 : Integer.Sparse Master := [(Sum.inl 0, -294175141714944000000), (Sum.inl 1, -178545505388544000000), (Sum.inl 2, -319843501479936000000), (Sum.inl 3, 1852663925145600000000), (Sum.inl 5, -1880194909630464000000), (Sum.inl 6, 231582990643200000000), (Sum.inl 7, 926331962572800000000), (Sum.inl 9, -592722968850432000000), (Sum.inl 13, 3705327850291200000000), (Sum.inl 35, 7410655700582400000000), (Sum.inl 52, 7002551688265728000000), (Sum.inl 58, 32389246891008000000), (Sum.inl 60, 4631659812864000000000), (Sum.inl 69, 926331962572800000000), (Sum.inl 70, 926331962572800000000), (Sum.inl 128, 3297223837974528000000), (Sum.inl 257, 1852663925145600000000), (Sum.inl 260, -2778995887718400000000), (Sum.inl 495, 2370891875401728000000)]

def originalMerge37 : Integer.Sparse OriginalKey := originalTerm40 ++ originalTerm41

theorem reducedMerge37Check : reducedMerge37 = Integer.Sparse.mergeBy masterLess reducedTerm40 reducedTerm41 := by decide +kernel

def reducedMerge38 : Integer.Sparse Master := [(Sum.inl 0, 144182987543347200000), (Sum.inl 1, -37169806528512000000), (Sum.inl 2, -160261861036032000000), (Sum.inl 5, 446037678342144000000), (Sum.inl 6, -49721202155520000000), (Sum.inl 7, 193072244391936000000), (Sum.inl 8, -787789148848128000000), (Sum.inl 9, -293483409408000000000), (Sum.inl 35, 386144488783872000000), (Sum.inl 52, -200822330032128000000), (Sum.inl 58, 12309205450752000000), (Sum.inl 60, 193072244391936000000), (Sum.inl 69, -3875042820096000000), (Sum.inl 70, 193072244391936000000), (Sum.inl 71, -787789148848128000000), (Sum.inl 257, 193072244391936000000), (Sum.inl 260, -579216733175808000000)]

def originalMerge38 : Integer.Sparse OriginalKey := originalTerm42 ++ originalTerm43

theorem reducedMerge38Check : reducedMerge38 = Integer.Sparse.mergeBy masterLess reducedTerm42 reducedTerm43 := by decide +kernel

def reducedMerge39 : Integer.Sparse Master := [(Sum.inl 0, -149992154171596800000), (Sum.inl 1, -215715311917056000000), (Sum.inl 2, -480105362515968000000), (Sum.inl 3, 1852663925145600000000), (Sum.inl 5, -1434157231288320000000), (Sum.inl 6, 181861788487680000000), (Sum.inl 7, 1119404206964736000000), (Sum.inl 8, -787789148848128000000), (Sum.inl 9, -886206378258432000000), (Sum.inl 13, 3705327850291200000000), (Sum.inl 35, 7796800189366272000000), (Sum.inl 52, 6801729358233600000000), (Sum.inl 58, 44698452341760000000), (Sum.inl 60, 4824732057255936000000), (Sum.inl 69, 922456919752704000000), (Sum.inl 70, 1119404206964736000000), (Sum.inl 71, -787789148848128000000), (Sum.inl 128, 3297223837974528000000), (Sum.inl 257, 2045736169537536000000), (Sum.inl 260, -3358212620894208000000), (Sum.inl 495, 2370891875401728000000)]

def originalMerge39 : Integer.Sparse OriginalKey := originalMerge37 ++ originalMerge38

theorem reducedMerge39Check : reducedMerge39 = Integer.Sparse.mergeBy masterLess reducedMerge37 reducedMerge38 := by decide +kernel

def reducedMerge40 : Integer.Sparse Master := [(Sum.inl 0, -155717185057136640000), (Sum.inl 1, -58421182456627200000), (Sum.inl 2, -491043475180339200000), (Sum.inl 3, 1852663925145600000000), (Sum.inl 5, -1434157231288320000000), (Sum.inl 6, 181861788487680000000), (Sum.inl 7, 1119404206964736000000), (Sum.inl 8, -787789148848128000000), (Sum.inl 9, -954814852480204800000), (Sum.inl 13, 3705327850291200000000), (Sum.inl 35, 7796800189366272000000), (Sum.inl 52, 6801729358233600000000), (Sum.inl 58, 19326662149939200000), (Sum.inl 60, 4824732057255936000000), (Sum.inl 69, 1541471081781657600000), (Sum.inl 70, 1119404206964736000000), (Sum.inl 71, -1365901961350348800000), (Sum.inl 128, 3297223837974528000000), (Sum.inl 257, 2136349566192844800000), (Sum.inl 260, -3358212620894208000000), (Sum.inl 495, 2370891875401728000000)]

def originalMerge40 : Integer.Sparse OriginalKey := originalMerge36 ++ originalMerge39

theorem reducedMerge40Check : reducedMerge40 = Integer.Sparse.mergeBy masterLess reducedMerge36 reducedMerge39 := by decide +kernel

def reducedMerge41 : Integer.Sparse Master := [(Sum.inl 0, -106683386636574720000), (Sum.inl 1, 148113961725542400000), (Sum.inl 2, -207624272589619200000), (Sum.inl 3, 1852663925145600000000), (Sum.inl 5, -1607827222897459200000), (Sum.inl 6, 39929204806041600000), (Sum.inl 7, 1597492255113216000000), (Sum.inl 8, -733982104151654400000), (Sum.inl 9, -666234323693568000000), (Sum.inl 13, 3705327850291200000000), (Sum.inl 35, 8026724502326476800000), (Sum.inl 52, 6801729358233600000000), (Sum.inl 58, -108235651971686400000), (Sum.inl 60, 4824732057255936000000), (Sum.inl 69, 2019559129930137600000), (Sum.inl 70, 2789950216067481600000), (Sum.inl 71, -1258287871957401600000), (Sum.inl 128, 3297223837974528000000), (Sum.inl 256, 315825855528960000000), (Sum.inl 257, 2366273879153049600000), (Sum.inl 260, -3358212620894208000000), (Sum.inl 495, 3290589127242547200000)]

def originalMerge41 : Integer.Sparse OriginalKey := originalMerge33 ++ originalMerge40

theorem reducedMerge41Check : reducedMerge41 = Integer.Sparse.mergeBy masterLess reducedMerge33 reducedMerge40 := by decide +kernel

def reducedMerge42 : Integer.Sparse Master := [(Sum.inl 0, 23713486234583040000), (Sum.inl 1, -66191616084787200000), (Sum.inl 2, -105132774013747200000), (Sum.inl 3, 215622706102272000000), (Sum.inl 5, 159336070432358400000), (Sum.inl 6, 892859679129600000), (Sum.inl 9, 53905676525568000000), (Sum.inl 13, 215622706102272000000), (Sum.inl 35, 646868118306816000000), (Sum.inl 52, 220384624390963200000), (Sum.inl 58, -6887019512217600000), (Sum.inl 60, 431245412204544000000), (Sum.inl 69, -105430393906790400000), (Sum.inl 128, 215622706102272000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 495, 215622706102272000000)]

def originalMerge42 : Integer.Sparse OriginalKey := originalTerm45 ++ originalTerm46

theorem reducedMerge42Check : reducedMerge42 = Integer.Sparse.mergeBy masterLess reducedTerm45 reducedTerm46 := by decide +kernel

def reducedMerge43 : Integer.Sparse Master := [(Sum.inl 0, -33614290452234240000), (Sum.inl 1, -26655218369740800000), (Sum.inl 2, 112317413419008000000), (Sum.inl 3, 1164496251263385600000), (Sum.inl 5, -315100702148198400000), (Sum.inl 6, 60197456251699200000), (Sum.inl 7, 948873545161113600000), (Sum.inl 9, 212051267385753600000), (Sum.inl 13, 215622706102272000000), (Sum.inl 35, 1595741663467929600000), (Sum.inl 52, 1169258169552076800000), (Sum.inl 58, -16771118940979200000), (Sum.inl 60, 431245412204544000000), (Sum.inl 69, 369006378673766400000), (Sum.inl 70, 316291181720371200000), (Sum.inl 128, 215622706102272000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 495, 215622706102272000000)]

def originalMerge43 : Integer.Sparse OriginalKey := originalTerm44 ++ originalMerge42

theorem reducedMerge43Check : reducedMerge43 = Integer.Sparse.mergeBy masterLess reducedTerm44 reducedMerge42 := by decide +kernel

def reducedMerge44 : Integer.Sparse Master := [(Sum.inl 0, -67236917413478400000), (Sum.inl 1, -238111486341120000000), (Sum.inl 2, -150534853926912000000), (Sum.inl 3, 43908479071027200000), (Sum.inl 5, 174993047676518400000), (Sum.inl 6, -2744279941939200000), (Sum.inl 7, 87816958142054400000), (Sum.inl 8, -393894574424064000000), (Sum.inl 9, -76519404070502400000), (Sum.inl 35, 87816958142054400000), (Sum.inl 52, 43908479071027200000), (Sum.inl 69, 43908479071027200000), (Sum.inl 70, 43908479071027200000), (Sum.inl 71, -393894574424064000000)]

def originalMerge44 : Integer.Sparse OriginalKey := originalTerm47 ++ originalTerm48

theorem reducedMerge44Check : reducedMerge44 = Integer.Sparse.mergeBy masterLess reducedTerm47 reducedTerm48 := by decide +kernel

def reducedMerge45 : Integer.Sparse Master := [(Sum.inl 0, 7668470038118400000), (Sum.inl 1, 16189312798310400000), (Sum.inl 2, 166151866761216000000), (Sum.inl 5, -81797975226777600000), (Sum.inl 6, 23857782836428800000), (Sum.inl 9, -57940192390348800000), (Sum.inl 35, -136329638215680000000), (Sum.inl 58, -5964445709107200000), (Sum.inl 70, -136329638215680000000)]

def originalMerge45 : Integer.Sparse OriginalKey := originalTerm49 ++ originalTerm50

theorem reducedMerge45Check : reducedMerge45 = Integer.Sparse.mergeBy masterLess reducedTerm49 reducedTerm50 := by decide +kernel

def reducedMerge46 : Integer.Sparse Master := [(Sum.inl 0, -59568447375360000000), (Sum.inl 1, -221922173542809600000), (Sum.inl 2, 15617012834304000000), (Sum.inl 3, 43908479071027200000), (Sum.inl 5, 93195072449740800000), (Sum.inl 6, 21113502894489600000), (Sum.inl 7, 87816958142054400000), (Sum.inl 8, -393894574424064000000), (Sum.inl 9, -134459596460851200000), (Sum.inl 35, -48512680073625600000), (Sum.inl 52, 43908479071027200000), (Sum.inl 58, -5964445709107200000), (Sum.inl 69, 43908479071027200000), (Sum.inl 70, -92421159144652800000), (Sum.inl 71, -393894574424064000000)]

def originalMerge46 : Integer.Sparse OriginalKey := originalMerge44 ++ originalMerge45

theorem reducedMerge46Check : reducedMerge46 = Integer.Sparse.mergeBy masterLess reducedMerge44 reducedMerge45 := by decide +kernel

def reducedMerge47 : Integer.Sparse Master := [(Sum.inl 0, -93182737827594240000), (Sum.inl 1, -248577391912550400000), (Sum.inl 2, 127934426253312000000), (Sum.inl 3, 1208404730334412800000), (Sum.inl 5, -221905629698457600000), (Sum.inl 6, 81310959146188800000), (Sum.inl 7, 1036690503303168000000), (Sum.inl 8, -393894574424064000000), (Sum.inl 9, 77591670924902400000), (Sum.inl 13, 215622706102272000000), (Sum.inl 35, 1547228983394304000000), (Sum.inl 52, 1213166648623104000000), (Sum.inl 58, -22735564650086400000), (Sum.inl 60, 431245412204544000000), (Sum.inl 69, 412914857744793600000), (Sum.inl 70, 223870022575718400000), (Sum.inl 71, -393894574424064000000), (Sum.inl 128, 215622706102272000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 495, 215622706102272000000)]

def originalMerge47 : Integer.Sparse OriginalKey := originalMerge43 ++ originalMerge46

theorem reducedMerge47Check : reducedMerge47 = Integer.Sparse.mergeBy masterLess reducedMerge43 reducedMerge46 := by decide +kernel

def reducedMerge48 : Integer.Sparse Master := [(Sum.inl 0, -11742588710092800000), (Sum.inl 1, 37054043512012800000), (Sum.inl 2, 32159841354547200000), (Sum.inl 5, -4748198289408000000), (Sum.inl 6, -3597649684070400000), (Sum.inl 9, 14390598736281600000), (Sum.inl 35, -18992793157632000000), (Sum.inl 52, 76555188102758400000), (Sum.inl 60, -18992793157632000000), (Sum.inl 69, 76555188102758400000), (Sum.inl 257, -18992793157632000000)]

def originalMerge48 : Integer.Sparse OriginalKey := originalTerm51 ++ originalTerm52

theorem reducedMerge48Check : reducedMerge48 = Integer.Sparse.mergeBy masterLess reducedTerm51 reducedTerm52 := by decide +kernel

def reducedMerge49 : Integer.Sparse Master := [(Sum.inl 1, -1677951313920000000), (Sum.inl 2, -8389756569600000000), (Sum.inl 5, 6711805255680000000), (Sum.inl 6, -6711805255680000000), (Sum.inl 7, 26847221022720000000), (Sum.inl 9, 26847221022720000000), (Sum.inl 35, 26847221022720000000), (Sum.inl 54, -80541663068160000000), (Sum.inl 259, -241624989204480000000), (Sum.inl 260, -80541663068160000000)]

def originalMerge49 : Integer.Sparse OriginalKey := originalTerm53 ++ originalTerm54

theorem reducedMerge49Check : reducedMerge49 = Integer.Sparse.mergeBy masterLess reducedTerm53 reducedTerm54 := by decide +kernel

def reducedMerge50 : Integer.Sparse Master := [(Sum.inl 0, -11742588710092800000), (Sum.inl 1, 35376092198092800000), (Sum.inl 2, 23770084784947200000), (Sum.inl 5, 1963606966272000000), (Sum.inl 6, -10309454939750400000), (Sum.inl 7, 26847221022720000000), (Sum.inl 9, 41237819759001600000), (Sum.inl 35, 7854427865088000000), (Sum.inl 52, 76555188102758400000), (Sum.inl 54, -80541663068160000000), (Sum.inl 60, -18992793157632000000), (Sum.inl 69, 76555188102758400000), (Sum.inl 257, -18992793157632000000), (Sum.inl 259, -241624989204480000000), (Sum.inl 260, -80541663068160000000)]

def originalMerge50 : Integer.Sparse OriginalKey := originalMerge48 ++ originalMerge49

theorem reducedMerge50Check : reducedMerge50 = Integer.Sparse.mergeBy masterLess reducedMerge48 reducedMerge49 := by decide +kernel

def reducedMerge51 : Integer.Sparse Master := [(Sum.inl 0, 130372544954695680000), (Sum.inl 1, 704451086980300800000), (Sum.inl 2, 195497241724108800000), (Sum.inl 5, -272241305557401600000), (Sum.inl 6, -179231461458739200000), (Sum.inl 9, 57481078240051200000), (Sum.inl 13, 659444767594905600000), (Sum.inl 35, 1318889535189811200000), (Sum.inl 52, 1318889535189811200000), (Sum.inl 60, 1318889535189811200000), (Sum.inl 128, 659444767594905600000), (Sum.inl 260, -689772938880614400000)]

def originalMerge51 : Integer.Sparse OriginalKey := originalTerm55 ++ originalTerm56

theorem reducedMerge51Check : reducedMerge51 = Integer.Sparse.mergeBy masterLess reducedTerm55 reducedTerm56 := by decide +kernel

def reducedMerge52 : Integer.Sparse Master := [(Sum.inl 0, 164059139008880640000), (Sum.inl 1, 210048601061376000000), (Sum.inl 2, -152528158295654400000), (Sum.inl 3, -344584813392691200000), (Sum.inl 5, 1026665230432665600000), (Sum.inl 6, 303418474955366400000), (Sum.inl 7, -172292406696345600000), (Sum.inl 8, -344584813392691200000), (Sum.inl 35, -344584813392691200000), (Sum.inl 52, -689169626785382400000), (Sum.inl 128, -674991207294566400000)]

def originalMerge52 : Integer.Sparse OriginalKey := originalTerm57 ++ originalTerm58

theorem reducedMerge52Check : reducedMerge52 = Integer.Sparse.mergeBy masterLess reducedTerm57 reducedTerm58 := by decide +kernel

def reducedMerge53 : Integer.Sparse Master := [(Sum.inl 0, 294431683963576320000), (Sum.inl 1, 914499688041676800000), (Sum.inl 2, 42969083428454400000), (Sum.inl 3, -344584813392691200000), (Sum.inl 5, 754423924875264000000), (Sum.inl 6, 124187013496627200000), (Sum.inl 7, -172292406696345600000), (Sum.inl 8, -344584813392691200000), (Sum.inl 9, 57481078240051200000), (Sum.inl 13, 659444767594905600000), (Sum.inl 35, 974304721797120000000), (Sum.inl 52, 629719908404428800000), (Sum.inl 60, 1318889535189811200000), (Sum.inl 128, -15546439699660800000), (Sum.inl 260, -689772938880614400000)]

def originalMerge53 : Integer.Sparse OriginalKey := originalMerge51 ++ originalMerge52

theorem reducedMerge53Check : reducedMerge53 = Integer.Sparse.mergeBy masterLess reducedMerge51 reducedMerge52 := by decide +kernel

def reducedMerge54 : Integer.Sparse Master := [(Sum.inl 0, 282689095253483520000), (Sum.inl 1, 949875780239769600000), (Sum.inl 2, 66739168213401600000), (Sum.inl 3, -344584813392691200000), (Sum.inl 5, 756387531841536000000), (Sum.inl 6, 113877558556876800000), (Sum.inl 7, -145445185673625600000), (Sum.inl 8, -344584813392691200000), (Sum.inl 9, 98718897999052800000), (Sum.inl 13, 659444767594905600000), (Sum.inl 35, 982159149662208000000), (Sum.inl 52, 706275096507187200000), (Sum.inl 54, -80541663068160000000), (Sum.inl 60, 1299896742032179200000), (Sum.inl 69, 76555188102758400000), (Sum.inl 128, -15546439699660800000), (Sum.inl 257, -18992793157632000000), (Sum.inl 259, -241624989204480000000), (Sum.inl 260, -770314601948774400000)]

def originalMerge54 : Integer.Sparse OriginalKey := originalMerge50 ++ originalMerge53

theorem reducedMerge54Check : reducedMerge54 = Integer.Sparse.mergeBy masterLess reducedMerge50 reducedMerge53 := by decide +kernel

def reducedMerge55 : Integer.Sparse Master := [(Sum.inl 0, 189506357425889280000), (Sum.inl 1, 701298388327219200000), (Sum.inl 2, 194673594466713600000), (Sum.inl 3, 863819916941721600000), (Sum.inl 5, 534481902143078400000), (Sum.inl 6, 195188517703065600000), (Sum.inl 7, 891245317629542400000), (Sum.inl 8, -738479387816755200000), (Sum.inl 9, 176310568923955200000), (Sum.inl 13, 875067473697177600000), (Sum.inl 35, 2529388133056512000000), (Sum.inl 52, 1919441745130291200000), (Sum.inl 54, -80541663068160000000), (Sum.inl 58, -22735564650086400000), (Sum.inl 60, 1731142154236723200000), (Sum.inl 69, 489470045847552000000), (Sum.inl 70, 223870022575718400000), (Sum.inl 71, -393894574424064000000), (Sum.inl 128, 200076266402611200000), (Sum.inl 257, 196629912944640000000), (Sum.inl 259, -241624989204480000000), (Sum.inl 260, -770314601948774400000), (Sum.inl 495, 215622706102272000000)]

def originalMerge55 : Integer.Sparse OriginalKey := originalMerge47 ++ originalMerge54

theorem reducedMerge55Check : reducedMerge55 = Integer.Sparse.mergeBy masterLess reducedMerge47 reducedMerge54 := by decide +kernel

def reducedMerge56 : Integer.Sparse Master := [(Sum.inl 0, 82822970789314560000), (Sum.inl 1, 849412350052761600000), (Sum.inl 2, -12950678122905600000), (Sum.inl 3, 2716483842087321600000), (Sum.inl 5, -1073345320754380800000), (Sum.inl 6, 235117722509107200000), (Sum.inl 7, 2488737572742758400000), (Sum.inl 8, -1472461491968409600000), (Sum.inl 9, -489923754769612800000), (Sum.inl 13, 4580395323988377600000), (Sum.inl 35, 10556112635382988800000), (Sum.inl 52, 8721171103363891200000), (Sum.inl 54, -80541663068160000000), (Sum.inl 58, -130971216621772800000), (Sum.inl 60, 6555874211492659200000), (Sum.inl 69, 2509029175777689600000), (Sum.inl 70, 3013820238643200000000), (Sum.inl 71, -1652182446381465600000), (Sum.inl 128, 3497300104377139200000), (Sum.inl 256, 315825855528960000000), (Sum.inl 257, 2562903792097689600000), (Sum.inl 259, -241624989204480000000), (Sum.inl 260, -4128527222842982400000), (Sum.inl 495, 3506211833344819200000)]

def originalMerge56 : Integer.Sparse OriginalKey := originalMerge41 ++ originalMerge55

theorem reducedMerge56Check : reducedMerge56 = Integer.Sparse.mergeBy masterLess reducedMerge41 reducedMerge55 := by decide +kernel

def reducedMerge57 : Integer.Sparse Master := [(Sum.inl 0, 21423666842625761280000), (Sum.inl 1, 2247695683925852160000), (Sum.inl 2, 1313238520815943680000), (Sum.inl 3, 2557483798767206400000), (Sum.inl 5, 279170139296563200000), (Sum.inl 6, -50388707084083200000), (Sum.inl 7, 876071265966489600000), (Sum.inl 8, -1542993257594880000000), (Sum.inl 9, 924422596005888000000), (Sum.inl 13, 4580395323988377600000), (Sum.inl 35, 9736766401285324800000), (Sum.inl 52, 9739296382530355200000), (Sum.inl 54, -80541663068160000000), (Sum.inl 58, -119603399808614400000), (Sum.inl 60, 6555874211492659200000), (Sum.inl 69, 2588488539085209600000), (Sum.inl 70, 1847847795720192000000), (Sum.inl 71, -136756003287859200000), (Sum.inl 128, 3497300104377139200000), (Sum.inl 256, 1211741307076608000000), (Sum.inl 257, 2120980123680768000000), (Sum.inl 259, -241624989204480000000), (Sum.inl 260, -4128527222842982400000), (Sum.inl 495, 3074676269491814400000)]

def originalMerge57 : Integer.Sparse OriginalKey := originalMerge27 ++ originalMerge56

theorem reducedMerge57Check : reducedMerge57 = Integer.Sparse.mergeBy masterLess reducedMerge27 reducedMerge56 := by decide +kernel

def reducedMerge58 : Integer.Sparse Master := [(Sum.inl 0, 90933714744606720000), (Sum.inl 1, -13178799238348800000), (Sum.inl 2, 13178799238348800000), (Sum.inl 3, 210860787813580800000), (Sum.inl 5, -26357598476697600000), (Sum.inl 6, -59304596572569600000), (Sum.inl 7, 105430393906790400000), (Sum.inl 35, 210860787813580800000), (Sum.inl 52, -105430393906790400000)]

def originalMerge58 : Integer.Sparse OriginalKey := originalTerm60 ++ originalTerm61

theorem reducedMerge58Check : reducedMerge58 = Integer.Sparse.mergeBy masterLess reducedTerm60 reducedTerm61 := by decide +kernel

def reducedMerge59 : Integer.Sparse Master := [(Sum.inl 0, -139217428012400640000), (Sum.inl 1, -622402412418662400000), (Sum.inl 2, -528353301366374400000), (Sum.inl 3, 210860787813580800000), (Sum.inl 5, 785940552430387200000), (Sum.inl 6, -194687621723750400000), (Sum.inl 7, 105430393906790400000), (Sum.inl 8, -541532100604723200000), (Sum.inl 35, 210860787813580800000), (Sum.inl 52, -646962494511513600000)]

def originalMerge59 : Integer.Sparse OriginalKey := originalTerm59 ++ originalMerge58

theorem reducedMerge59Check : reducedMerge59 = Integer.Sparse.mergeBy masterLess reducedTerm59 reducedMerge58 := by decide +kernel

def reducedMerge60 : Integer.Sparse Master := [(Sum.inl 0, 94086959355002880000), (Sum.inl 1, -246074673000038400000), (Sum.inl 2, -119934799242854400000), (Sum.inl 5, 562456395428659200000), (Sum.inl 6, 15509474710732800000), (Sum.inl 7, -562456395428659200000), (Sum.inl 35, -479739196971417600000), (Sum.inl 52, 82717198457241600000), (Sum.inl 60, 82717198457241600000)]

def originalMerge60 : Integer.Sparse OriginalKey := originalTerm62 ++ originalTerm63

theorem reducedMerge60Check : reducedMerge60 = Integer.Sparse.mergeBy masterLess reducedTerm62 reducedTerm63 := by decide +kernel

def reducedMerge61 : Integer.Sparse Master := [(Sum.inl 0, 160057579359928320000), (Sum.inl 1, 104510489274777600000), (Sum.inl 5, 947500366366310400000), (Sum.inl 6, -30501414494208000000), (Sum.inl 8, -738479387816755200000)]

def originalMerge61 : Integer.Sparse OriginalKey := originalTerm64 ++ originalTerm65

theorem reducedMerge61Check : reducedMerge61 = Integer.Sparse.mergeBy masterLess reducedTerm64 reducedTerm65 := by decide +kernel

def reducedMerge62 : Integer.Sparse Master := [(Sum.inl 0, 254144538714931200000), (Sum.inl 1, -141564183725260800000), (Sum.inl 2, -119934799242854400000), (Sum.inl 5, 1509956761794969600000), (Sum.inl 6, -14991939783475200000), (Sum.inl 7, -562456395428659200000), (Sum.inl 8, -738479387816755200000), (Sum.inl 35, -479739196971417600000), (Sum.inl 52, 82717198457241600000), (Sum.inl 60, 82717198457241600000)]

def originalMerge62 : Integer.Sparse OriginalKey := originalMerge60 ++ originalMerge61

theorem reducedMerge62Check : reducedMerge62 = Integer.Sparse.mergeBy masterLess reducedMerge60 reducedMerge61 := by decide +kernel

def reducedMerge63 : Integer.Sparse Master := [(Sum.inl 0, 114927110702530560000), (Sum.inl 1, -763966596143923200000), (Sum.inl 2, -648288100609228800000), (Sum.inl 3, 210860787813580800000), (Sum.inl 5, 2295897314225356800000), (Sum.inl 6, -209679561507225600000), (Sum.inl 7, -457026001521868800000), (Sum.inl 8, -1280011488421478400000), (Sum.inl 35, -268878409157836800000), (Sum.inl 52, -564245296054272000000), (Sum.inl 60, 82717198457241600000)]

def originalMerge63 : Integer.Sparse OriginalKey := originalMerge59 ++ originalMerge62

theorem reducedMerge63Check : reducedMerge63 = Integer.Sparse.mergeBy masterLess reducedMerge59 reducedMerge62 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
