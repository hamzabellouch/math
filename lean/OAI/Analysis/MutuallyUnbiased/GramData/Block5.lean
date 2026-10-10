import OAI.Analysis.MutuallyUnbiased.Certificate.Gram

namespace OAI

/-!
Exact integer matrix for λ = (5,), m = 12, exponent = 15.
-/

namespace MUB6.Certificate.GramData.Block5

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 12) (Fin 12) ℚ := ![
  ![3616397, -219419, 1005407, 842091, 186248, 5630326, 3598595, -2799721, -212971, 17130, 919824, -418081],
  ![-219419, 858064, -20456, -237640, 8632, -668374, -719533, 1972640, 472837, -55599, -551864, -740155],
  ![1005407, -20456, 3980209, -871566, 1228704, 3015305, -741592, -4624965, -846239, -3742225, 946245, -2217477],
  ![842091, -237640, -871566, 1225103, -1032886, 1787740, 2550956, 1845322, 193740, 3000641, -537616, 2123549],
  ![186248, 8632, 1228704, -1032886, 2523431, 415506, -2373762, -4715938, -791330, -4758384, 1140990, -3681887],
  ![5630326, -668374, 3015305, 1787740, 415506, 14075688, 6490324, -6536077, -885101, 729531, 1366079, -804],
  ![3598595, -719533, -741592, 2550956, -2373762, 6490324, 11111814, 2309105, -369038, 7029198, -149445, 5321306],
  ![-2799721, 1972640, -4624965, 1845322, -4715938, -6536077, 2309105, 20933543, 2515724, 11792046, -5705771, 8194820],
  ![-212971, 472837, -846239, 193740, -791330, -885101, -369038, 2515724, 1454109, 1090081, -502420, -325129],
  ![17130, -55599, -3742225, 3000641, -4758384, 729531, 7029198, 11792046, 1090081, 14915142, -4206760, 10354295],
  ![919824, -551864, 946245, -537616, 1140990, 1366079, -149445, -5705771, -502420, -4206760, 3573400, -4063238],
  ![-418081, -740155, -2217477, 2123549, -3681887, -804, 5321306, 8194820, -325129, 10354295, -4063238, 10569070]
]

def entries : Matrix (Fin 12) (Fin 12) ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(5596981437199023986587802591479864234103266874844442185081518081781 / 9431564276476137316302249406652340045066312658581041790680679499333), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(9024752121723864958855005808155216977010956324479945196573351 / 478995735357191027742975870517403818338762162597491826585334002), (-57603086073094515054582359527188582754702843364010638232418582 / 718493603035786541614463805776105727508143243896237739878001003), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(78143250083496273767036324975030346167235577000085768052 / 349379465359371639006642318106477150532122357473160614923), (-348693052313068535489210812175476395363963376171784539124 / 1048138396078114917019926954319431451596367072419481844769), (-387069283994005020319227948137243595319885390203365789112 / 349379465359371639006642318106477150532122357473160614923), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(119941803843766847785804406867237308267447484602212 / 990173937759478857566700889865251524679699764453343), (-962400671796460546757282745047917382337015835933958 / 2970521813278436572700102669595754574039099293360029), (-875665181236660139839521834514974753462905371754868 / 990173937759478857566700889865251524679699764453343), (76513347913309985461521495872043763142663901266383 / 990173937759478857566700889865251524679699764453343), 0, 0, 0, 0, 0, 0, 0, 0],
  ![(195314986230313698334220333529271142314421519 / 679071827041941018173889076181579750285283604), (419123235125777758926279550702916040095508641 / 12223292886754938327130003371268435505135104872), (516620017490490207657894348485648592583229135 / 2037215481125823054521667228544739250855850812), (939245091506853894916515484801477633295493323 / 8148861924503292218086668914178957003423403248), (-143021512431600477192683756622905146359608117 / 8148861924503292218086668914178957003423403248), 0, 0, 0, 0, 0, 0, 0],
  ![(1811877281114823618349420095351540074354 / 3821540804474953610122690404992415618041), (197474390150077484280366644739903970099 / 3821540804474953610122690404992415618041), (509412198793257852386185192206395025475 / 3821540804474953610122690404992415618041), (543925650112671520180129531897177948436 / 3821540804474953610122690404992415618041), (34235715976631395165850965028603113864 / 3821540804474953610122690404992415618041), (2868035580068340510730897121269167289915 / 3821540804474953610122690404992415618041), 0, 0, 0, 0, 0, 0],
  ![(-152438554035250133801136889400924 / 673208220558333996413931095649023), (90672337087880422326261812076056 / 673208220558333996413931095649023), (-99980872472861022611553034139925 / 673208220558333996413931095649023), (-20430331459781462651255084932038 / 673208220558333996413931095649023), (-52463499548145177681310232782060 / 673208220558333996413931095649023), (-407988702464931557146032404570221 / 673208220558333996413931095649023), (-59994820743749938791278562642311 / 673208220558333996413931095649023), 0, 0, 0, 0, 0],
  ![(-1121563155940342130796688 / 7323623296747635808619611), (226110096320200742209041 / 7323623296747635808619611), (-7492059782719963807100963 / 14647246593495271617239222), (653499326372212378582465 / 7323623296747635808619611), (-424824783996151542791981 / 563355638211356600663047), (-11909155694107014855434297 / 14647246593495271617239222), (-3126155550699434803461339 / 14647246593495271617239222), (16654681570337646967878523 / 14647246593495271617239222), 0, 0, 0, 0],
  ![(13339287316993735 / 123633918401546947), (59968730129378299 / 494535673606187788), (-324964627294316905 / 989071347212375576), (99158623864243919 / 494535673606187788), (-123187159486268491 / 494535673606187788), (184200407072220213 / 989071347212375576), (422899695849938159 / 989071347212375576), (724532550227200193 / 989071347212375576), (139432751472697929 / 494535673606187788), 0, 0, 0],
  ![(235968283453 / 625223873334), (-260003387305 / 625223873334), (4856827606 / 104203978889), (431136063 / 3110566534), (-85328823259 / 625223873334), (424556403917 / 625223873334), (589477590667 / 625223873334), (-794329090465 / 625223873334), (-65011653501 / 208407957778), (-23427215745 / 208407957778), 0, 0],
  ![(-24593 / 621710), (-148031 / 2113814), (-2217477 / 10569070), (2123549 / 10569070), (-3681887 / 10569070), (-402 / 5284535), (156509 / 310855), (819482 / 1056907), (-325129 / 10569070), (2070859 / 2113814), (-119507 / 310855), 0]
]

def D : Fin 12 → ℚ := ![(18238248911296124259390454311074204811055825914347849551847187862294562799 / 18863128552952274632604498813304680090132625317162083581361358998666), (301810056847236394121671981012874881442122005074593337301781743978656 / 2155480809107359624843391417328317182524429731688713219634003009), (478995735357191027742975870517403818338762162597491826585334002 / 349379465359371639006642318106477150532122357473160614923), (349379465359371639006642318106477150532122357473160614923 / 990173937759478857566700889865251524679699764453343), (990173937759478857566700889865251524679699764453343 / 2716287308167764072695556304726319001141134416), (24446585773509876654260006742536871010270209744 / 3821540804474953610122690404992415618041), (3821540804474953610122690404992415618041 / 673208220558333996413931095649023), (673208220558333996413931095649023 / 87883479560971629703435332), (7323623296747635808619611 / 8407106451305192396), (494535673606187788 / 104203978889), (625223873334 / 310855), 10569070]

theorem pivot_0 : 40000 < D 0 := by decide +kernel

theorem pivot_1 : 40000 < D 1 := by decide +kernel

theorem pivot_2 : 40000 < D 2 := by decide +kernel

theorem pivot_3 : 40000 < D 3 := by decide +kernel

theorem pivot_4 : 40000 < D 4 := by decide +kernel

theorem pivot_5 : 40000 < D 5 := by decide +kernel

theorem pivot_6 : 40000 < D 6 := by decide +kernel

theorem pivot_7 : 40000 < D 7 := by decide +kernel

theorem pivot_8 : 40000 < D 8 := by decide +kernel

theorem pivot_9 : 40000 < D 9 := by decide +kernel

theorem pivot_10 : 40000 < D 10 := by decide +kernel

theorem pivot_11 : 40000 < D 11 := by decide +kernel

theorem entry_0_0 : Z 0 0 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_0_1 : Z 0 1 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_0_2 : Z 0 2 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_0_3 : Z 0 3 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_0_4 : Z 0 4 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_0_5 : Z 0 5 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_0_6 : Z 0 6 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_0_7 : Z 0 7 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_0_8 : Z 0 8 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_0_9 : Z 0 9 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_0_10 : Z 0 10 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_0_11 : Z 0 11 =
    ∑ k : Fin 12, lowerUnit entries k 0 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_1_0 : Z 1 0 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_1_1 : Z 1 1 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_1_2 : Z 1 2 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_1_3 : Z 1 3 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_1_4 : Z 1 4 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_1_5 : Z 1 5 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_1_6 : Z 1 6 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_1_7 : Z 1 7 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_1_8 : Z 1 8 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_1_9 : Z 1 9 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_1_10 : Z 1 10 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_1_11 : Z 1 11 =
    ∑ k : Fin 12, lowerUnit entries k 1 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_2_0 : Z 2 0 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_2_1 : Z 2 1 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_2_2 : Z 2 2 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_2_3 : Z 2 3 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_2_4 : Z 2 4 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_2_5 : Z 2 5 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_2_6 : Z 2 6 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_2_7 : Z 2 7 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_2_8 : Z 2 8 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_2_9 : Z 2 9 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_2_10 : Z 2 10 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_2_11 : Z 2 11 =
    ∑ k : Fin 12, lowerUnit entries k 2 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_3_0 : Z 3 0 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_3_1 : Z 3 1 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_3_2 : Z 3 2 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_3_3 : Z 3 3 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_3_4 : Z 3 4 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_3_5 : Z 3 5 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_3_6 : Z 3 6 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_3_7 : Z 3 7 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_3_8 : Z 3 8 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_3_9 : Z 3 9 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_3_10 : Z 3 10 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_3_11 : Z 3 11 =
    ∑ k : Fin 12, lowerUnit entries k 3 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_4_0 : Z 4 0 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_4_1 : Z 4 1 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_4_2 : Z 4 2 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_4_3 : Z 4 3 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_4_4 : Z 4 4 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_4_5 : Z 4 5 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_4_6 : Z 4 6 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_4_7 : Z 4 7 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_4_8 : Z 4 8 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_4_9 : Z 4 9 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_4_10 : Z 4 10 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_4_11 : Z 4 11 =
    ∑ k : Fin 12, lowerUnit entries k 4 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_5_0 : Z 5 0 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_5_1 : Z 5 1 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_5_2 : Z 5 2 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_5_3 : Z 5 3 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_5_4 : Z 5 4 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_5_5 : Z 5 5 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_5_6 : Z 5 6 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_5_7 : Z 5 7 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_5_8 : Z 5 8 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_5_9 : Z 5 9 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_5_10 : Z 5 10 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_5_11 : Z 5 11 =
    ∑ k : Fin 12, lowerUnit entries k 5 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_6_0 : Z 6 0 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_6_1 : Z 6 1 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_6_2 : Z 6 2 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_6_3 : Z 6 3 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_6_4 : Z 6 4 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_6_5 : Z 6 5 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_6_6 : Z 6 6 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_6_7 : Z 6 7 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_6_8 : Z 6 8 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_6_9 : Z 6 9 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_6_10 : Z 6 10 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_6_11 : Z 6 11 =
    ∑ k : Fin 12, lowerUnit entries k 6 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_7_0 : Z 7 0 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_7_1 : Z 7 1 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_7_2 : Z 7 2 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_7_3 : Z 7 3 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_7_4 : Z 7 4 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_7_5 : Z 7 5 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_7_6 : Z 7 6 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_7_7 : Z 7 7 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_7_8 : Z 7 8 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_7_9 : Z 7 9 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_7_10 : Z 7 10 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_7_11 : Z 7 11 =
    ∑ k : Fin 12, lowerUnit entries k 7 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_8_0 : Z 8 0 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_8_1 : Z 8 1 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_8_2 : Z 8 2 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_8_3 : Z 8 3 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_8_4 : Z 8 4 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_8_5 : Z 8 5 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_8_6 : Z 8 6 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_8_7 : Z 8 7 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_8_8 : Z 8 8 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_8_9 : Z 8 9 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_8_10 : Z 8 10 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_8_11 : Z 8 11 =
    ∑ k : Fin 12, lowerUnit entries k 8 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_9_0 : Z 9 0 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_9_1 : Z 9 1 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_9_2 : Z 9 2 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_9_3 : Z 9 3 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_9_4 : Z 9 4 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_9_5 : Z 9 5 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_9_6 : Z 9 6 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_9_7 : Z 9 7 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_9_8 : Z 9 8 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_9_9 : Z 9 9 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_9_10 : Z 9 10 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_9_11 : Z 9 11 =
    ∑ k : Fin 12, lowerUnit entries k 9 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_10_0 : Z 10 0 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_10_1 : Z 10 1 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_10_2 : Z 10 2 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_10_3 : Z 10 3 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_10_4 : Z 10 4 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_10_5 : Z 10 5 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_10_6 : Z 10 6 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_10_7 : Z 10 7 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_10_8 : Z 10 8 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_10_9 : Z 10 9 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_10_10 : Z 10 10 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_10_11 : Z 10 11 =
    ∑ k : Fin 12, lowerUnit entries k 10 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem entry_11_0 : Z 11 0 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_11_1 : Z 11 1 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_11_2 : Z 11 2 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_11_3 : Z 11 3 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_11_4 : Z 11 4 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_11_5 : Z 11 5 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_11_6 : Z 11 6 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_11_7 : Z 11 7 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_11_8 : Z 11 8 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_11_9 : Z 11 9 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_11_10 : Z 11 10 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_11_11 : Z 11 11 =
    ∑ k : Fin 12, lowerUnit entries k 11 * D k * lowerUnit entries k 11 := by
  decide +kernel

theorem pivots_pos : ∀ k : Fin 12, 0 < D k := by
  intro k
  fin_cases k
  · exact lt_trans (by norm_num) pivot_0
  · exact lt_trans (by norm_num) pivot_1
  · exact lt_trans (by norm_num) pivot_2
  · exact lt_trans (by norm_num) pivot_3
  · exact lt_trans (by norm_num) pivot_4
  · exact lt_trans (by norm_num) pivot_5
  · exact lt_trans (by norm_num) pivot_6
  · exact lt_trans (by norm_num) pivot_7
  · exact lt_trans (by norm_num) pivot_8
  · exact lt_trans (by norm_num) pivot_9
  · exact lt_trans (by norm_num) pivot_10
  · exact lt_trans (by norm_num) pivot_11

theorem gram : ∀ i j : Fin 12, Z i j =
    ∑ k, lowerUnit entries k i * D k * lowerUnit entries k j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact entry_0_0
  · exact entry_0_1
  · exact entry_0_2
  · exact entry_0_3
  · exact entry_0_4
  · exact entry_0_5
  · exact entry_0_6
  · exact entry_0_7
  · exact entry_0_8
  · exact entry_0_9
  · exact entry_0_10
  · exact entry_0_11
  · exact entry_1_0
  · exact entry_1_1
  · exact entry_1_2
  · exact entry_1_3
  · exact entry_1_4
  · exact entry_1_5
  · exact entry_1_6
  · exact entry_1_7
  · exact entry_1_8
  · exact entry_1_9
  · exact entry_1_10
  · exact entry_1_11
  · exact entry_2_0
  · exact entry_2_1
  · exact entry_2_2
  · exact entry_2_3
  · exact entry_2_4
  · exact entry_2_5
  · exact entry_2_6
  · exact entry_2_7
  · exact entry_2_8
  · exact entry_2_9
  · exact entry_2_10
  · exact entry_2_11
  · exact entry_3_0
  · exact entry_3_1
  · exact entry_3_2
  · exact entry_3_3
  · exact entry_3_4
  · exact entry_3_5
  · exact entry_3_6
  · exact entry_3_7
  · exact entry_3_8
  · exact entry_3_9
  · exact entry_3_10
  · exact entry_3_11
  · exact entry_4_0
  · exact entry_4_1
  · exact entry_4_2
  · exact entry_4_3
  · exact entry_4_4
  · exact entry_4_5
  · exact entry_4_6
  · exact entry_4_7
  · exact entry_4_8
  · exact entry_4_9
  · exact entry_4_10
  · exact entry_4_11
  · exact entry_5_0
  · exact entry_5_1
  · exact entry_5_2
  · exact entry_5_3
  · exact entry_5_4
  · exact entry_5_5
  · exact entry_5_6
  · exact entry_5_7
  · exact entry_5_8
  · exact entry_5_9
  · exact entry_5_10
  · exact entry_5_11
  · exact entry_6_0
  · exact entry_6_1
  · exact entry_6_2
  · exact entry_6_3
  · exact entry_6_4
  · exact entry_6_5
  · exact entry_6_6
  · exact entry_6_7
  · exact entry_6_8
  · exact entry_6_9
  · exact entry_6_10
  · exact entry_6_11
  · exact entry_7_0
  · exact entry_7_1
  · exact entry_7_2
  · exact entry_7_3
  · exact entry_7_4
  · exact entry_7_5
  · exact entry_7_6
  · exact entry_7_7
  · exact entry_7_8
  · exact entry_7_9
  · exact entry_7_10
  · exact entry_7_11
  · exact entry_8_0
  · exact entry_8_1
  · exact entry_8_2
  · exact entry_8_3
  · exact entry_8_4
  · exact entry_8_5
  · exact entry_8_6
  · exact entry_8_7
  · exact entry_8_8
  · exact entry_8_9
  · exact entry_8_10
  · exact entry_8_11
  · exact entry_9_0
  · exact entry_9_1
  · exact entry_9_2
  · exact entry_9_3
  · exact entry_9_4
  · exact entry_9_5
  · exact entry_9_6
  · exact entry_9_7
  · exact entry_9_8
  · exact entry_9_9
  · exact entry_9_10
  · exact entry_9_11
  · exact entry_10_0
  · exact entry_10_1
  · exact entry_10_2
  · exact entry_10_3
  · exact entry_10_4
  · exact entry_10_5
  · exact entry_10_6
  · exact entry_10_7
  · exact entry_10_8
  · exact entry_10_9
  · exact entry_10_10
  · exact entry_10_11
  · exact entry_11_0
  · exact entry_11_1
  · exact entry_11_2
  · exact entry_11_3
  · exact entry_11_4
  · exact entry_11_5
  · exact entry_11_6
  · exact entry_11_7
  · exact entry_11_8
  · exact entry_11_9
  · exact entry_11_10
  · exact entry_11_11

theorem positiveDefinite : (realMatrix Z).PosDef :=
  posDef_of_rational_gram Z entries D pivots_pos gram

end MUB6.Certificate.GramData.Block5

end OAI
