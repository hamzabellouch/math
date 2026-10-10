import Mathlib
import OAI.Analysis.LaughlinFock.LDL
import OAI.Analysis.LaughlinFock.Sparse23

namespace OAI

/-! Certificate23 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourYData_23 : Matrix (CopyLabel 23) (CopyLabel 23) ℚ :=
  copyMatrixData 23 [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

def fourZData_23 : Matrix (CopyLabel 23) (CopyLabel 23) ℚ :=
  copyMatrixData 23 [
    [1124000727777607680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-2143861251406875/2), (246544043911790625/4)],
    [0, 1824676506132480000, 0, 0, 0, 0, 0, 0, 0, -27842353914375, 0, (49308808782358125/4)],
    [0, 0, 24008901396480000, 0, 0, 0, 0, 0, (-4396161144375/2), -27842353914375, (6821376709021875/32), (147926426347074375/64)],
    [0, 0, 0, 823834851840000, 0, 0, 0, -402263111250, (-23934655119375/4), 0, (6821376709021875/64), (49308808782358125/128)],
    [0, 0, 0, 0, 61787613888000, 0, (-603394666875/4), (-16291656005625/8), (-51288546684375/16), (116937886440375/16), (15786614669450625/512), (49308808782358125/1024)],
    [0, 0, 0, 0, 0, (18453267669375/2), (-4740958096875/4), (-33186706678125/16), 0, (918797679174375/256), (2143861251406875/512), 0],
    [0, 0, 0, 0, (-603394666875/4), (-4740958096875/4), (65597620213125/64), (-86285437363125/128), (209550347881875/512), 0, (-12668271031040625/8192), (-49308808782358125/16384)],
    [0, 0, 0, -402263111250, (-16291656005625/8), (-33186706678125/16), (-86285437363125/128), 1609052445000, (-488950811724375/1024), (-2533654206208125/2048), (-26311024449084375/16384), (-49308808782358125/32768)],
    [0, 0, (-4396161144375/2), (-23934655119375/4), (-51288546684375/16), 0, (209550347881875/512), (-488950811724375/1024), (1734529802630625/2048), (-2366600082721875/2048), (-115963404053371875/131072), (-147926426347074375/262144)],
    [0, -27842353914375, -27842353914375, 0, (116937886440375/16), (918797679174375/256), 0, (-2533654206208125/2048), (-2366600082721875/2048), (316372667529043125/65536), (-25921231494283125/65536), (-49308808782358125/262144)],
    [(-2143861251406875/2), 0, (6821376709021875/32), (6821376709021875/64), (15786614669450625/512), (2143861251406875/512), (-12668271031040625/8192), (-26311024449084375/16384), (-115963404053371875/131072), (-25921231494283125/65536), (101850365435360416875/2097152), (-246544043911790625/4194304)],
    [(246544043911790625/4), (49308808782358125/4), (147926426347074375/64), (49308808782358125/128), (49308808782358125/1024), 0, (-49308808782358125/16384), (-49308808782358125/32768), (-147926426347074375/262144), (-49308808782358125/262144), (-246544043911790625/4194304), (25851868812458629565625/8388608)]
  ]

def fourLData_23 : Matrix (CopyLabel 23) (CopyLabel 23) ℚ :=
  copyMatrixData 23 [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [(345/2097155147486), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [(465/16777241179888), (100981765197829/20166243897788951), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [(15/4194310294972), (265290126005179/322659902364623216), (332148196734695751793/11788713286154962103898), 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [(51/268435858878208), (6717450079775/80664975591155804), (241839610991979869629/47154853144619848415592), (279374048249478931531838473/3854866416052307060169897565), 1, 0, 0, 0, 0, 0, 0, 0],
    [(-33/536871717756416), (-49432942720425/5162558437833971456), (408421411799263115/23577426572309924207796), (271118458980709501504750913/30838931328418456481359180520), (183460604356060440272919394566095/1824985551106228598471302410673916), 1, 0, 0, 0, 0, 0, 0],
    [(-75/4294973742051328), (-33161265757763/5162558437833971456), (-75878744617480952119/215565042946833592756992), (-255914793917203570711756019/61677862656836912962718361040), (-52629204745453498067759412062635/7299942204424914393885209642695664), (-511161485774106343747899688487963641/9283430112523124183988623130863905918), 1, 0, 0, 0, 0, 0],
    [(15/4294973742051328), (7340042978251/82600935005343543296), (-53826474130765973461/1005970200418556766199296), (-2691513774959985657046702857/986845802509390607403493776640), (-255301583103139618475404468620105/4171395545385665367934405510111808), (-244281606388753916638146875851511556239/816941849902034928190998835516023720784), (-871270481830772945196296430021323257221815/778490845769410970935339138784831050985562), 1, 0, 0, 0, 0],
    [(375/68719579872821248), (4849086132973/2581279218916985728), (-126610091103297683417/2011940400837113532398592), (-4669321454807479672372261089/493422901254695303701746888320), (-3350528227731030896574532676573595/58399537635399315151081677141565312), (7226761974529335135951529165505220457/408470924951017464095499417758011860392), (877517561683146974892250812004505270759033/1556981691538821941870678277569662101971124), (-1074742702961238054730663901609430043788225790/357288100994165292101443563021377816034441037), 1, 0, 0, 0],
    [(453/137439159745642496), (-37186155888609801/1321614960085496692736), (-3929759593855251397667/2011940400837113532398592), (80235381091594789004152890837/19736916050187812148069875532800), (42206482799880566588067552672544509/233598150541597260604326708566261248), (15206123889007365374367234449679334888503/32677673996081397127639953420640948831360), (216051873214751591520718069234499456167193/648742371474509142446115948987359209154635), (47956834228992794970294642188728332076685865129/7145762019883305842028871260427556320688820740), (-38/5), 1, 0, 0],
    [(-1048578357607/1099513277965139968), (1394608297026685/1321614960085496692736), (6184830591167510390475025/386292556960725798220529664), (292335005146257211435397680859/1578953284015024971845590042624), (68391187533320405733068453811892445/133484657452341291773900976323577856), (3937712408681015175493709663951092602497/13071069598432558851055981368256379532544), (-12493830276507879648736028481970837666070573/16607804709747434046620568294076395754358656), (-5525214534856393868865566110795649580988755063/408329258279046048115935500595860361182218328), (931/16), 0, 1, 0],
    [(30146627830105/549756638982569984), (278034133123027888827/21145839361367947083776), (129823823892450334408582601/772585113921451596441059328), (143433987501531150697752909147377/252632525442403995495294406819840), (164070244050457811766440819336418545/533938629809365167095603905294311424), (-3474462440748244245422492818232190945903/9506232435223679164404350086004639660032), (19983224049978600492936320204846726907812909/33215609419494868093241136588152791508717312), (-190008968277167187380127733099574652696056726025/6533268132464736769854968009533765778915493248), (-33649/32), 0, 0, 1]
  ]

def fourPivotData_23 : CopyLabel 23 → ℚ :=
  copyDiagonalData 23 [(3596807727106964372495493/800), (2695083358684056754955880339/479349747996800), (41460066632617412037005591462619/516255843783397145600), (1687804688951660387226431508125931/510968990688790738386944), (440474619464572437164875860934388795628693/1578953284015024971845590042624000), (17875786513703508084674654426461795282409857029/427150903847492133676483124235449139200), (161052762702264252299142605764190579764316339459883/60839887585431546652187840550429693824204800), (3104434579359970407545821546788921635658478795883201511/27210227236450195941983139093014766803941221990400), (617253866866789232996626176408903607856598861326229375/107041065082302247237303795868201218521751441375232), 0, 0, 0]

theorem fourOccupations_23 : highestFourOccupations 23 = {{0,1,2,21}, {0,1,3,20}, {0,1,4,19}, {0,1,5,18}, {0,1,6,17}, {0,1,7,16}, {0,1,8,15}, {0,1,9,14}, {0,1,10,13}, {0,1,11,12}, {0,2,3,19}, {0,2,4,18}, {0,2,5,17}, {0,2,6,16}, {0,2,7,15}, {0,2,8,14}, {0,2,9,13}, {0,2,10,12}, {0,3,4,17}, {0,3,5,16}, {0,3,6,15}, {0,3,7,14}, {0,3,8,13}, {0,3,9,12}, {0,3,10,11}, {0,4,5,15}, {0,4,6,14}, {0,4,7,13}, {0,4,8,12}, {0,4,9,11}, {0,5,6,13}, {0,5,7,12}, {0,5,8,11}, {0,5,9,10}, {0,6,7,11}, {0,6,8,10}, {0,7,8,9}, {1,2,3,18}, {1,2,4,17}, {1,2,5,16}, {1,2,6,15}, {1,2,7,14}, {1,2,8,13}, {1,2,9,12}, {1,2,10,11}, {1,3,4,16}, {1,3,5,15}, {1,3,6,14}, {1,3,7,13}, {1,3,8,12}, {1,3,9,11}, {1,4,5,14}, {1,4,6,13}, {1,4,7,12}, {1,4,8,11}, {1,4,9,10}, {1,5,6,12}, {1,5,7,11}, {1,5,8,10}, {1,6,7,10}, {1,6,8,9}, {2,3,4,15}, {2,3,5,14}, {2,3,6,13}, {2,3,7,12}, {2,3,8,11}, {2,3,9,10}, {2,4,5,13}, {2,4,6,12}, {2,4,7,11}, {2,4,8,10}, {2,5,6,11}, {2,5,7,10}, {2,5,8,9}, {2,6,7,9}, {3,4,5,12}, {3,4,6,11}, {3,4,7,10}, {3,4,8,9}, {3,5,6,10}, {3,5,7,9}, {3,6,7,8}, {4,5,6,9}, {4,5,7,8}} := by
  decide +kernel

theorem fourYNumber_23_1_1 :
    (collectedFourTrace 23 1 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_3_1 :
    (collectedFourTrace 23 3 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_3_3 :
    (collectedFourTrace 23 3 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_5_1 :
    (collectedFourTrace 23 5 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_5_3 :
    (collectedFourTrace 23 5 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_5_5 :
    (collectedFourTrace 23 5 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_1 :
    (collectedFourTrace 23 7 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_3 :
    (collectedFourTrace 23 7 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_5 :
    (collectedFourTrace 23 7 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_7 :
    (collectedFourTrace 23 7 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_1 :
    (collectedFourTrace 23 9 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_3 :
    (collectedFourTrace 23 9 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_5 :
    (collectedFourTrace 23 9 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_7 :
    (collectedFourTrace 23 9 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_9 :
    (collectedFourTrace 23 9 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_1 :
    (collectedFourTrace 23 11 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_3 :
    (collectedFourTrace 23 11 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_5 :
    (collectedFourTrace 23 11 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_7 :
    (collectedFourTrace 23 11 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_9 :
    (collectedFourTrace 23 11 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_11 :
    (collectedFourTrace 23 11 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_1 :
    (collectedFourTrace 23 13 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_3 :
    (collectedFourTrace 23 13 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_5 :
    (collectedFourTrace 23 13 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_7 :
    (collectedFourTrace 23 13 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_9 :
    (collectedFourTrace 23 13 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_11 :
    (collectedFourTrace 23 13 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_13 :
    (collectedFourTrace 23 13 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_1 :
    (collectedFourTrace 23 15 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_3 :
    (collectedFourTrace 23 15 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_5 :
    (collectedFourTrace 23 15 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_7 :
    (collectedFourTrace 23 15 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_9 :
    (collectedFourTrace 23 15 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_11 :
    (collectedFourTrace 23 15 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_13 :
    (collectedFourTrace 23 15 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_15 :
    (collectedFourTrace 23 15 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_1 :
    (collectedFourTrace 23 17 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_3 :
    (collectedFourTrace 23 17 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_5 :
    (collectedFourTrace 23 17 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_7 :
    (collectedFourTrace 23 17 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_9 :
    (collectedFourTrace 23 17 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_11 :
    (collectedFourTrace 23 17 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_13 :
    (collectedFourTrace 23 17 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_15 :
    (collectedFourTrace 23 17 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_17 :
    (collectedFourTrace 23 17 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_1 :
    (collectedFourTrace 23 19 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_3 :
    (collectedFourTrace 23 19 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_5 :
    (collectedFourTrace 23 19 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_7 :
    (collectedFourTrace 23 19 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_9 :
    (collectedFourTrace 23 19 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_11 :
    (collectedFourTrace 23 19 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_13 :
    (collectedFourTrace 23 19 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_15 :
    (collectedFourTrace 23 19 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_17 :
    (collectedFourTrace 23 19 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_19 :
    (collectedFourTrace 23 19 19 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_1 :
    (collectedFourTrace 23 21 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_3 :
    (collectedFourTrace 23 21 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_5 :
    (collectedFourTrace 23 21 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_7 :
    (collectedFourTrace 23 21 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_9 :
    (collectedFourTrace 23 21 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_11 :
    (collectedFourTrace 23 21 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_13 :
    (collectedFourTrace 23 21 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_15 :
    (collectedFourTrace 23 21 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_17 :
    (collectedFourTrace 23 21 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_19 :
    (collectedFourTrace 23 21 19 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_21 :
    (collectedFourTrace 23 21 21 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_1 :
    (collectedFourTrace 23 23 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_3 :
    (collectedFourTrace 23 23 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_5 :
    (collectedFourTrace 23 23 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_7 :
    (collectedFourTrace 23 23 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_9 :
    (collectedFourTrace 23 23 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_11 :
    (collectedFourTrace 23 23 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_13 :
    (collectedFourTrace 23 23 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_15 :
    (collectedFourTrace 23 23 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_17 :
    (collectedFourTrace 23 23 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_19 :
    (collectedFourTrace 23 23 19 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_21 :
    (collectedFourTrace 23 23 21 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_23 :
    (collectedFourTrace 23 23 23 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

end LaughlinFock
end

end OAI
