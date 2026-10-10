import OAI.Analysis.MutuallyUnbiased.Certificate.Gram

namespace OAI

/-!
Exact integer matrix for λ = (1, 2, 2), m = 11, exponent = 13.
-/

namespace MUB6.Certificate.GramData.Block2

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 11) (Fin 11) ℚ := ![
  ![4921588, 1243280, -7309127, -624690, 1603998, -2795071, 3367935, -1583320, 2340968, -248222, 702355],
  ![1243280, 1259868, -2872973, -210702, 1253342, -2034588, 1682712, -885538, 2724267, -409660, 794],
  ![-7309127, -2872973, 13379731, 1150717, -3887583, 6470784, -6302383, 2324542, -6055529, 725259, -836950],
  ![-624690, -210702, 1150717, 690108, 8436, 557254, -693384, -181298, 1653368, -526328, -588904],
  ![1603998, 1253342, -3887583, 8436, 1940509, -2484968, 1935441, -879724, 3975384, -709322, -233345],
  ![-2795071, -2034588, 6470784, 557254, -2484968, 4332981, -3363650, 1243475, -4427358, 537643, -211242],
  ![3367935, 1682712, -6302383, -693384, 1935441, -3363650, 3298003, -1116848, 2778884, -234978, 508720],
  ![-1583320, -885538, 2324542, -181298, -879724, 1243475, -1116848, 1720010, -3611042, 821982, 282809],
  ![2340968, 2724267, -6055529, 1653368, 3975384, -4427358, 2778884, -3611042, 15022074, -3403183, -2223239],
  ![-248222, -409660, 725259, -526328, -709322, 537643, -234978, 821982, -3403183, 873834, 642996],
  ![702355, 794, -836950, -588904, -233345, -211242, 508720, 282809, -2223239, 642996, 680229]
]

def entries : Matrix (Fin 11) (Fin 11) ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-14827153955215089202732638206951917239133001841574472989 / 27507193756326595116897163357783180615127072140170648614), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(-11393478122050259797789923181655993722042228591674 / 17479418652284552137434755866464075063379980195961), (5658031728703927773343020507526599668741930181320 / 17479418652284552137434755866464075063379980195961), 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![(189756908932443978670324120470906799618796531 / 189915925886052455618184221018667842370673476), (-21066435804720785928533956539802970850506971 / 47478981471513113904546055254666960592668369), (-6082608645798733789422806265046988388465867 / 18087231036766900535065163906539794511492712), 0, 0, 0, 0, 0, 0, 0, 0],
  ![(6957201992055347941835705121579867822 / 3520003250857510716841109304189444968363), (177157843568628361209030820238058237489 / 3520003250857510716841109304189444968363), (-579960192052915214128865646888981082024 / 3520003250857510716841109304189444968363), (302228261280040133466533430515126081286 / 3520003250857510716841109304189444968363), 0, 0, 0, 0, 0, 0, 0],
  ![(4650820566461172754344495271033409 / 7653737263479163532482722018743552), (-2865428485893563144517681673963401 / 15307474526958327064965444037487104), (406219908150596939503835320206381 / 1913434315869790883120680504685888), (2007139815275909459453615706409973 / 7653737263479163532482722018743552), (-4981736393472402681607486085932019 / 15307474526958327064965444037487104), 0, 0, 0, 0, 0, 0],
  ![(29429149021131038751634709825 / 34425022755281971937245195013), (11809836990062242357994329922 / 34425022755281971937245195013), (-57726063333875233258409906259 / 34425022755281971937245195013), (-9949645983959050352458621412 / 34425022755281971937245195013), (18635080458244273734881588183 / 34425022755281971937245195013), (-15820869753746313878842815228 / 34425022755281971937245195013), 0, 0, 0, 0, 0],
  ![(5771252348976692509063 / 111830209413948198594007), (-11101839075590262135160 / 111830209413948198594007), (-116038567147699746951479 / 111830209413948198594007), (672989850357148607094 / 111830209413948198594007), (55289105352156247953139 / 111830209413948198594007), (-44299552785540597149338 / 111830209413948198594007), (36600909915959275872914 / 111830209413948198594007), 0, 0, 0, 0],
  ![(952401039090908 / 7606625109860333), (43360189344211154 / 83672876208463663), (-82737834488103571 / 83672876208463663), (-7415417341907512 / 83672876208463663), (4504310994446048 / 7606625109860333), (-91099031377911129 / 83672876208463663), (56646018017229742 / 83672876208463663), (1632534949772216 / 83672876208463663), 0, 0, 0],
  ![(-11489986267 / 3351173555), (-5169873166 / 3351173555), (2438528857 / 427809390), (1146630404 / 10053520665), (-6156694317 / 3351173555), (55727569031 / 20107041330), (-27052431949 / 10053520665), (20960607673 / 10053520665), (-98378887207 / 20107041330), 0, 0],
  ![(702355 / 680229), (794 / 680229), (-836950 / 680229), (-588904 / 680229), (-233345 / 680229), (-70414 / 226743), (508720 / 680229), (282809 / 680229), (-2223239 / 680229), (71444 / 75581), 0]
]

def D : Fin 11 → ℚ := ![(3213472828238838540323513005837750309890513122790494441732261 / 27507193756326595116897163357783180615127072140170648614), (27507193756326595116897163357783180615127072140170648614 / 367067791697975594886129873195745576330979584115181), (17479418652284552137434755866464075063379980195961 / 18087231036766900535065163906539794511492712), (379831851772104911236368442037335684741346952 / 3520003250857510716841109304189444968363), (3520003250857510716841109304189444968363 / 15307474526958327064965444037487104), (15307474526958327064965444037487104 / 34425022755281971937245195013), (34425022755281971937245195013 / 111830209413948198594007), (111830209413948198594007 / 251018628625390989), (83672876208463663 / 60321123990), (20107041330 / 75581), 680229]

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

theorem entry_0_0 : Z 0 0 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_0_1 : Z 0 1 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_0_2 : Z 0 2 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_0_3 : Z 0 3 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_0_4 : Z 0 4 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_0_5 : Z 0 5 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_0_6 : Z 0 6 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_0_7 : Z 0 7 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_0_8 : Z 0 8 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_0_9 : Z 0 9 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_0_10 : Z 0 10 =
    ∑ k : Fin 11, lowerUnit entries k 0 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_1_0 : Z 1 0 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_1_1 : Z 1 1 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_1_2 : Z 1 2 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_1_3 : Z 1 3 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_1_4 : Z 1 4 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_1_5 : Z 1 5 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_1_6 : Z 1 6 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_1_7 : Z 1 7 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_1_8 : Z 1 8 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_1_9 : Z 1 9 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_1_10 : Z 1 10 =
    ∑ k : Fin 11, lowerUnit entries k 1 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_2_0 : Z 2 0 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_2_1 : Z 2 1 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_2_2 : Z 2 2 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_2_3 : Z 2 3 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_2_4 : Z 2 4 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_2_5 : Z 2 5 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_2_6 : Z 2 6 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_2_7 : Z 2 7 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_2_8 : Z 2 8 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_2_9 : Z 2 9 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_2_10 : Z 2 10 =
    ∑ k : Fin 11, lowerUnit entries k 2 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_3_0 : Z 3 0 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_3_1 : Z 3 1 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_3_2 : Z 3 2 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_3_3 : Z 3 3 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_3_4 : Z 3 4 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_3_5 : Z 3 5 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_3_6 : Z 3 6 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_3_7 : Z 3 7 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_3_8 : Z 3 8 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_3_9 : Z 3 9 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_3_10 : Z 3 10 =
    ∑ k : Fin 11, lowerUnit entries k 3 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_4_0 : Z 4 0 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_4_1 : Z 4 1 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_4_2 : Z 4 2 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_4_3 : Z 4 3 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_4_4 : Z 4 4 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_4_5 : Z 4 5 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_4_6 : Z 4 6 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_4_7 : Z 4 7 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_4_8 : Z 4 8 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_4_9 : Z 4 9 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_4_10 : Z 4 10 =
    ∑ k : Fin 11, lowerUnit entries k 4 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_5_0 : Z 5 0 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_5_1 : Z 5 1 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_5_2 : Z 5 2 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_5_3 : Z 5 3 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_5_4 : Z 5 4 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_5_5 : Z 5 5 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_5_6 : Z 5 6 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_5_7 : Z 5 7 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_5_8 : Z 5 8 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_5_9 : Z 5 9 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_5_10 : Z 5 10 =
    ∑ k : Fin 11, lowerUnit entries k 5 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_6_0 : Z 6 0 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_6_1 : Z 6 1 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_6_2 : Z 6 2 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_6_3 : Z 6 3 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_6_4 : Z 6 4 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_6_5 : Z 6 5 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_6_6 : Z 6 6 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_6_7 : Z 6 7 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_6_8 : Z 6 8 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_6_9 : Z 6 9 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_6_10 : Z 6 10 =
    ∑ k : Fin 11, lowerUnit entries k 6 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_7_0 : Z 7 0 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_7_1 : Z 7 1 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_7_2 : Z 7 2 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_7_3 : Z 7 3 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_7_4 : Z 7 4 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_7_5 : Z 7 5 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_7_6 : Z 7 6 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_7_7 : Z 7 7 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_7_8 : Z 7 8 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_7_9 : Z 7 9 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_7_10 : Z 7 10 =
    ∑ k : Fin 11, lowerUnit entries k 7 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_8_0 : Z 8 0 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_8_1 : Z 8 1 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_8_2 : Z 8 2 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_8_3 : Z 8 3 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_8_4 : Z 8 4 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_8_5 : Z 8 5 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_8_6 : Z 8 6 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_8_7 : Z 8 7 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_8_8 : Z 8 8 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_8_9 : Z 8 9 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_8_10 : Z 8 10 =
    ∑ k : Fin 11, lowerUnit entries k 8 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_9_0 : Z 9 0 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_9_1 : Z 9 1 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_9_2 : Z 9 2 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_9_3 : Z 9 3 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_9_4 : Z 9 4 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_9_5 : Z 9 5 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_9_6 : Z 9 6 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_9_7 : Z 9 7 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_9_8 : Z 9 8 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_9_9 : Z 9 9 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_9_10 : Z 9 10 =
    ∑ k : Fin 11, lowerUnit entries k 9 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem entry_10_0 : Z 10 0 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_10_1 : Z 10 1 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_10_2 : Z 10 2 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_10_3 : Z 10 3 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_10_4 : Z 10 4 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_10_5 : Z 10 5 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_10_6 : Z 10 6 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_10_7 : Z 10 7 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_10_8 : Z 10 8 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_10_9 : Z 10 9 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_10_10 : Z 10 10 =
    ∑ k : Fin 11, lowerUnit entries k 10 * D k * lowerUnit entries k 10 := by
  decide +kernel

theorem pivots_pos : ∀ k : Fin 11, 0 < D k := by
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

theorem gram : ∀ i j : Fin 11, Z i j =
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

theorem positiveDefinite : (realMatrix Z).PosDef :=
  posDef_of_rational_gram Z entries D pivots_pos gram

end MUB6.Certificate.GramData.Block2

end OAI
