import OAI.Analysis.MutuallyUnbiased.Certificate.IntegerMerge
import OAI.Analysis.MutuallyUnbiased.PairData.Data
import OAI.Analysis.MutuallyUnbiased.PairMerge.Block0

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged32 : Integer.Sparse (Fin 271) := [(0, -709936116), (1, 8740606950), (2, -4279518990), (3, -24353494560), (4, -15124776000), (5, 1229283120), (7, -2413171200), (8, -3882126720), (12, -5598840480), (13, 497383200), (23, -496052640), (24, 5262010560), (25, 36043200), (26, -2186170080), (27, -2046856680), (29, 2708441280), (30, 9789063840), (32, 1337892480), (35, -650924640), (37, 298429920), (38, -704989440), (39, -1301849280), (42, 1069541280), (44, -5550819840), (45, -5550819840), (50, 8268992640), (53, 786444480), (54, -62102880), (55, 3700546560)]

theorem pairMergeCheck32 : pairMerged32 = Integer.Sparse.merge pairMerged30 pairMerged31 := by decide +kernel

theorem pairMergedZero32 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged32 x = 0 := by
  rw [pairMergeCheck32, Integer.Sparse.eval_merge]
  rw [pairMergedZero30 x h, pairMergedZero31 x h]
  simp only [add_zero]

def pairMerged33 : Integer.Sparse (Fin 271) := [(0, 51323124), (1, -806956560), (2, 363588060), (3, 2677578240), (4, 357930240), (5, -118157760), (7, 117168960), (8, 476586240), (12, 1078251840), (13, 1324455360), (23, -181686240), (26, 151278720), (27, 136264680), (29, -363372480), (36, -35596800), (37, 545058720), (39, 1018923840), (50, -726744960), (53, -363372480), (54, -545058720), (55, 35596800), (56, -71193600)]

theorem pairMergeCheck33 : pairMerged33 = Integer.Sparse.merge (Integer.Sparse.scale (-247200) (rows 35)) (Integer.Sparse.scale (1514052) (rows 36)) := by decide +kernel

theorem pairMergedZero33 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged33 x = 0 := by
  rw [pairMergeCheck33, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged34 : Integer.Sparse (Fin 271) := [(0, -80740800), (1, 1248220260), (2, -492432300), (3, -4464714240), (4, -1374914880), (12, -2351393280), (13, -2743292160), (26, -150557760), (30, 1175696640), (32, 1175696640), (40, -881772480), (41, -1763544960), (52, 145981440), (56, 145981440)]

theorem pairMergeCheck34 : pairMerged34 = Integer.Sparse.merge (Integer.Sparse.scale (-6123420) (rows 37)) (Integer.Sparse.scale (1013760) (rows 38)) := by decide +kernel

theorem pairMergedZero34 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged34 x = 0 := by
  rw [pairMergeCheck34, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged35 : Integer.Sparse (Fin 271) := [(0, -29417676), (1, 441263700), (2, -128844240), (3, -1787136000), (4, -1016984640), (5, -118157760), (7, 117168960), (8, 476586240), (12, -1273141440), (13, -1418836800), (23, -181686240), (26, 720960), (27, 136264680), (29, -363372480), (30, 1175696640), (32, 1175696640), (36, -35596800), (37, 545058720), (39, 1018923840), (40, -881772480), (41, -1763544960), (50, -726744960), (52, 145981440), (53, -363372480), (54, -545058720), (55, 35596800), (56, 74787840)]

theorem pairMergeCheck35 : pairMerged35 = Integer.Sparse.merge pairMerged33 pairMerged34 := by decide +kernel

theorem pairMergedZero35 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged35 x = 0 := by
  rw [pairMergeCheck35, Integer.Sparse.eval_merge]
  rw [pairMergedZero33 x h, pairMergedZero34 x h]
  simp only [add_zero]

def pairMerged36 : Integer.Sparse (Fin 271) := [(0, -739353792), (1, 9181870650), (2, -4408363230), (3, -26140630560), (4, -16141760640), (5, 1111125360), (7, -2296002240), (8, -3405540480), (12, -6871981920), (13, -921453600), (23, -677738880), (24, 5262010560), (25, 36043200), (26, -2185449120), (27, -1910592000), (29, 2345068800), (30, 10964760480), (32, 2513589120), (35, -650924640), (36, -35596800), (37, 843488640), (38, -704989440), (39, -282925440), (40, -881772480), (41, -1763544960), (42, 1069541280), (44, -5550819840), (45, -5550819840), (50, 7542247680), (52, 145981440), (53, 423072000), (54, -607161600), (55, 3736143360), (56, 74787840)]

theorem pairMergeCheck36 : pairMerged36 = Integer.Sparse.merge pairMerged32 pairMerged35 := by decide +kernel

theorem pairMergedZero36 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged36 x = 0 := by
  rw [pairMergeCheck36, Integer.Sparse.eval_merge]
  rw [pairMergedZero32 x h, pairMergedZero35 x h]
  simp only [add_zero]

def pairMerged37 : Integer.Sparse (Fin 271) := [(0, 311282724), (1, -6563693940), (2, 3017480760), (3, 28238385600), (4, 11057085120), (5, -1125976920), (7, 2430655680), (8, 3288579840), (12, 7625388480), (13, 4384773120), (14, 1072211040), (15, 4288844160), (23, -2501825760), (24, -4718194560), (25, -2501825760), (26, 6029063040), (27, 1590621120), (29, -1644289920), (30, -3288579840), (32, -8006774400), (35, 2144422080), (36, 4932869760), (38, 4932869760), (39, 4932869760), (41, 4932869760), (47, 2144422080), (50, -7291967040), (53, -714807360), (54, -5647677120), (55, -3288579840)]

theorem pairMergeCheck37 : pairMerged37 = Integer.Sparse.merge (Integer.Sparse.scale (34256040) (rows 39)) (Integer.Sparse.scale (2978364) (rows 40)) := by decide +kernel

theorem pairMergedZero37 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged37 x = 0 := by
  rw [pairMergeCheck37, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged38 : Integer.Sparse (Fin 271) := [(0, -168894831), (1, 2243807580), (2, -404709675), (3, -9100344960), (4, -3608470080), (5, 21656520), (7, -86626080), (8, -86626080), (12, -2513691840), (13, -638511120), (15, -2056656960), (16, -638511120), (18, -3333679200), (19, -1559269440), (21, -1559269440), (23, 685552320), (24, 1984943520), (25, 898389360), (26, -519756480), (27, -248117940), (30, 1039512960), (36, -1559269440), (37, -1277022240), (46, -779634720), (47, -779634720), (49, -638511120), (50, 519756480), (54, 425674080), (55, 519756480)]

theorem pairMergeCheck38 : pairMerged38 = Integer.Sparse.merge (Integer.Sparse.scale (-886821) (rows 41)) (Integer.Sparse.scale (-1082826) (rows 42)) := by decide +kernel

theorem pairMergedZero38 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged38 x = 0 := by
  rw [pairMergeCheck38, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged39 : Integer.Sparse (Fin 271) := [(0, 142387893), (1, -4319886360), (2, 2612771085), (3, 19138040640), (4, 7448615040), (5, -1104320400), (7, 2344029600), (8, 3201953760), (12, 5111696640), (13, 3746262000), (14, 1072211040), (15, 2232187200), (16, -638511120), (18, -3333679200), (19, -1559269440), (21, -1559269440), (23, -1816273440), (24, -2733251040), (25, -1603436400), (26, 5509306560), (27, 1342503180), (29, -1644289920), (30, -2249066880), (32, -8006774400), (35, 2144422080), (36, 3373600320), (37, -1277022240), (38, 4932869760), (39, 4932869760), (41, 4932869760), (46, -779634720), (47, 1364787360), (49, -638511120), (50, -6772210560), (53, -714807360), (54, -5222003040), (55, -2768823360)]

theorem pairMergeCheck39 : pairMerged39 = Integer.Sparse.merge pairMerged37 pairMerged38 := by decide +kernel

theorem pairMergedZero39 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged39 x = 0 := by
  rw [pairMergeCheck39, Integer.Sparse.eval_merge]
  rw [pairMergedZero37 x h, pairMergedZero38 x h]
  simp only [add_zero]

def pairMerged40 : Integer.Sparse (Fin 271) := [(0, 300331956), (1, -3076485120), (2, 746667540), (3, 3956297280), (4, 5021454240), (5, -76082640), (7, 304330560), (8, 456495840), (9, 19447200), (12, 608661120), (17, 1369487520), (20, 2738975040), (23, -456495840), (24, -2282479200), (25, -1369487520), (26, 304330560), (27, 342371880), (29, -1369487520), (30, -2738975040), (43, 2738975040), (44, 2738975040), (47, 1369487520), (50, -456495840), (57, -972360)]

theorem pairMergeCheck40 : pairMerged40 = Integer.Sparse.merge (Integer.Sparse.scale (3804132) (rows 43)) (Integer.Sparse.scale (-194472) (rows 44)) := by decide +kernel

theorem pairMergedZero40 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged40 x = 0 := by
  rw [pairMergeCheck40, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged41 : Integer.Sparse (Fin 271) := [(0, -435642), (1, 10750000), (2, 39111000), (3, 70702080), (5, -77343440), (6, 6722010), (7, 141404160), (8, 141404160), (9, -9526880), (27, -25389000), (34, 47134720), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

theorem pairMergeCheck41 : pairMerged41 = Integer.Sparse.merge (Integer.Sparse.scale (-141050) (rows 45)) (Integer.Sparse.scale (-294592) (rows 46)) := by decide +kernel

theorem pairMergedZero41 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged41 x = 0 := by
  rw [pairMergeCheck41, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged42 : Integer.Sparse (Fin 271) := [(0, 299896314), (1, -3065735120), (2, 785778540), (3, 4026999360), (4, 5021454240), (5, -153426080), (6, 6722010), (7, 445734720), (8, 597900000), (9, 9920320), (12, 608661120), (17, 1369487520), (20, 2738975040), (23, -456495840), (24, -2282479200), (25, -1369487520), (26, 304330560), (27, 316982880), (29, -1369487520), (30, -2738975040), (34, 47134720), (43, 2738975040), (44, 2738975040), (47, 1369487520), (50, -456495840), (57, -972360), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

theorem pairMergeCheck42 : pairMerged42 = Integer.Sparse.merge pairMerged40 pairMerged41 := by decide +kernel

theorem pairMergedZero42 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged42 x = 0 := by
  rw [pairMergeCheck42, Integer.Sparse.eval_merge]
  rw [pairMergedZero40 x h, pairMergedZero41 x h]
  simp only [add_zero]

def pairMerged43 : Integer.Sparse (Fin 271) := [(0, 442284207), (1, -7385621480), (2, 3398549625), (3, 23165040000), (4, 12470069280), (5, -1257746480), (6, 6722010), (7, 2789764320), (8, 3799853760), (9, 9920320), (12, 5720357760), (13, 3746262000), (14, 1072211040), (15, 2232187200), (16, -638511120), (17, 1369487520), (18, -3333679200), (19, -1559269440), (20, 2738975040), (21, -1559269440), (23, -2272769280), (24, -5015730240), (25, -2972923920), (26, 5813637120), (27, 1659486060), (29, -3013777440), (30, -4988041920), (32, -8006774400), (34, 47134720), (35, 2144422080), (36, 3373600320), (37, -1277022240), (38, 4932869760), (39, 4932869760), (41, 4932869760), (43, 2738975040), (44, 2738975040), (46, -779634720), (47, 2734274880), (49, -638511120), (50, -7228706400), (53, -714807360), (54, -5222003040), (55, -2768823360), (57, -972360), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

theorem pairMergeCheck43 : pairMerged43 = Integer.Sparse.merge pairMerged39 pairMerged42 := by decide +kernel

theorem pairMergedZero43 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged43 x = 0 := by
  rw [pairMergeCheck43, Integer.Sparse.eval_merge]
  rw [pairMergedZero39 x h, pairMergedZero42 x h]
  simp only [add_zero]

def pairMerged44 : Integer.Sparse (Fin 271) := [(0, -297069585), (1, 1796249170), (2, -1009813605), (3, -2975590560), (4, -3671691360), (5, -146621120), (6, 6722010), (7, 493762080), (8, 394313280), (9, 9920320), (12, -1151624160), (13, 2824808400), (14, 1072211040), (15, 2232187200), (16, -638511120), (17, 1369487520), (18, -3333679200), (19, -1559269440), (20, 2738975040), (21, -1559269440), (23, -2950508160), (24, 246280320), (25, -2936880720), (26, 3628188000), (27, -251105940), (29, -668708640), (30, 5976718560), (32, -5493185280), (34, 47134720), (35, 1493497440), (36, 3338003520), (37, -433533600), (38, 4227880320), (39, 4649944320), (40, -881772480), (41, 3169324800), (42, 1069541280), (43, 2738975040), (44, -2811844800), (45, -5550819840), (46, -779634720), (47, 2734274880), (49, -638511120), (50, 313541280), (52, 145981440), (53, -291735360), (54, -5829164640), (55, 967320000), (56, 74787840), (57, -972360), (66, -33852000), (67, 70702080), (68, 23567360), (69, 141404160)]

theorem pairMergeCheck44 : pairMerged44 = Integer.Sparse.merge pairMerged36 pairMerged43 := by decide +kernel

theorem pairMergedZero44 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged44 x = 0 := by
  rw [pairMergeCheck44, Integer.Sparse.eval_merge]
  rw [pairMergedZero36 x h, pairMergedZero43 x h]
  simp only [add_zero]

def pairMerged45 : Integer.Sparse (Fin 271) := [(0, 2253012), (1, -35796300), (2, 39664440), (3, 337326720), (4, 117492480), (5, -62641200), (6, 7343280), (7, 200252160), (8, 58746240), (9, -5896080), (12, 16008960), (13, 8004480), (23, -36020160), (24, -176238720), (26, 117492480), (34, 172665600), (51, 117492480), (67, 74755200), (68, 47168640), (69, 19582080), (111, -36020160), (112, -24013440), (113, -176238720), (131, -117492480)]

theorem pairMergeCheck45 : pairMerged45 = Integer.Sparse.merge (Integer.Sparse.scale (-50028) (rows 47)) (Integer.Sparse.scale (-244776) (rows 48)) := by decide +kernel

theorem pairMergedZero45 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged45 x = 0 := by
  rw [pairMergeCheck45, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged46 : Integer.Sparse (Fin 271) := [(0, -596160), (1, 29059980), (2, -76569000), (3, -404705280), (4, -43178880), (5, 109394880), (6, -8881140), (7, -206866560), (8, -129536640), (9, 7008400), (12, -96662400), (13, -199768960), (23, 57997440), (24, 129536640), (27, -16192080), (34, -115994880), (50, 129536640), (51, -120508800), (53, 115994880), (67, -62511360), (68, -19332480), (69, -86357760), (111, 64768320), (112, 57997440), (113, 259073280), (130, 38664960)]

theorem pairMergeCheck46 : pairMerged46 = Integer.Sparse.merge (Integer.Sparse.scale (161104) (rows 49)) (Integer.Sparse.scale (269868) (rows 50)) := by decide +kernel

theorem pairMergedZero46 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged46 x = 0 := by
  rw [pairMergeCheck46, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged47 : Integer.Sparse (Fin 271) := [(0, 1656852), (1, -6736320), (2, -36904560), (3, -67378560), (4, 74313600), (5, 46753680), (6, -1537860), (7, -6614400), (8, -70790400), (9, 1112320), (12, -80653440), (13, -191764480), (23, 21977280), (24, -46702080), (26, 117492480), (27, -16192080), (34, 56670720), (50, 129536640), (51, -3016320), (53, 115994880), (67, 12243840), (68, 27836160), (69, -66775680), (111, 28748160), (112, 33984000), (113, 82834560), (130, 38664960), (131, -117492480)]

theorem pairMergeCheck47 : pairMerged47 = Integer.Sparse.merge pairMerged45 pairMerged46 := by decide +kernel

theorem pairMergedZero47 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged47 x = 0 := by
  rw [pairMergeCheck47, Integer.Sparse.eval_merge]
  rw [pairMergedZero45 x h, pairMergedZero46 x h]
  simp only [add_zero]

def pairMerged48 : Integer.Sparse (Fin 271) := [(0, 790464), (1, 5379360), (2, 11551440), (3, -70012800), (4, -33784320), (5, 17085600), (6, -3642960), (7, -5445120), (8, 6558720), (9, 680640), (13, -42230400), (24, 50676480), (26, -33784320), (27, 4292640), (29, -34341120), (34, -42230400), (51, -22337280), (54, 25338240), (55, 101352960), (67, -2722560), (68, -8446080), (69, -5166720), (112, 25338240), (113, -17170560), (131, 101352960), (146, -68682240)]

theorem pairMergeCheck48 : pairMerged48 = Integer.Sparse.merge (Integer.Sparse.scale (-71544) (rows 51)) (Integer.Sparse.scale (105576) (rows 52)) := by decide +kernel

theorem pairMergedZero48 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged48 x = 0 := by
  rw [pairMergeCheck48, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged49 : Integer.Sparse (Fin 271) := [(0, 11280586), (1, -375059460), (2, 1630660770), (3, 5983799520), (4, 189706080), (5, -3317388720), (6, 228491940), (7, 6673498560), (8, 5414681280), (10, -1888225920), (11, 189706080), (12, 1258817280), (13, 1678423040), (26, 379412160), (34, 4242141120), (51, 948530400), (80, 629408640), (143, -569118240)]

theorem pairMergeCheck49 : pairMerged49 = Integer.Sparse.merge (Integer.Sparse.scale (-10490144) (rows 53)) (Integer.Sparse.scale (-790442) (rows 54)) := by decide +kernel

theorem pairMergedZero49 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged49 x = 0 := by
  rw [pairMergeCheck49, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged50 : Integer.Sparse (Fin 271) := [(0, 12071050), (1, -369680100), (2, 1642212210), (3, 5913786720), (4, 155921760), (5, -3300303120), (6, 224848980), (7, 6668053440), (8, 5421240000), (9, 680640), (10, -1888225920), (11, 189706080), (12, 1258817280), (13, 1636192640), (24, 50676480), (26, 345627840), (27, 4292640), (29, -34341120), (34, 4199910720), (51, 926193120), (54, 25338240), (55, 101352960), (67, -2722560), (68, -8446080), (69, -5166720), (80, 629408640), (112, 25338240), (113, -17170560), (131, 101352960), (143, -569118240), (146, -68682240)]

theorem pairMergeCheck50 : pairMerged50 = Integer.Sparse.merge pairMerged48 pairMerged49 := by decide +kernel

theorem pairMergedZero50 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged50 x = 0 := by
  rw [pairMergeCheck50, Integer.Sparse.eval_merge]
  rw [pairMergedZero48 x h, pairMergedZero49 x h]
  simp only [add_zero]

def pairMerged51 : Integer.Sparse (Fin 271) := [(0, 13727902), (1, -376416420), (2, 1605307650), (3, 5846408160), (4, 230235360), (5, -3253549440), (6, 223311120), (7, 6661439040), (8, 5350449600), (9, 1792960), (10, -1888225920), (11, 189706080), (12, 1178163840), (13, 1444428160), (23, 21977280), (24, 3974400), (26, 463120320), (27, -11899440), (29, -34341120), (34, 4256581440), (50, 129536640), (51, 923176800), (53, 115994880), (54, 25338240), (55, 101352960), (67, 9521280), (68, 19390080), (69, -71942400), (80, 629408640), (111, 28748160), (112, 59322240), (113, 65664000), (130, 38664960), (131, -16139520), (143, -569118240), (146, -68682240)]

theorem pairMergeCheck51 : pairMerged51 = Integer.Sparse.merge pairMerged47 pairMerged50 := by decide +kernel

theorem pairMergedZero51 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged51 x = 0 := by
  rw [pairMergeCheck51, Integer.Sparse.eval_merge]
  rw [pairMergedZero47 x h, pairMergedZero50 x h]
  simp only [add_zero]

def pairMerged52 : Integer.Sparse (Fin 271) := [(0, 589008), (1, -17946720), (2, -29830560), (3, -98664960), (5, 53701920), (6, -8938800), (7, -25495680), (8, -47673600), (10, 2488320), (12, -13577280), (13, -99770880), (34, -97559040), (51, -190694400), (80, -72339840), (114, 2488320), (115, -96176640), (132, 35755200), (133, 143020800)]

theorem pairMergeCheck52 : pairMerged52 = Integer.Sparse.merge (Integer.Sparse.scale (595920) (rows 55)) (Integer.Sparse.scale (6912) (rows 56)) := by decide +kernel

theorem pairMergedZero52 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged52 x = 0 := by
  rw [pairMergeCheck52, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged53 : Integer.Sparse (Fin 271) := [(0, -20052162), (1, 425908260), (2, -61213590), (3, -2399309280), (4, -922805280), (5, 262631520), (6, -46138320), (7, -85190400), (11, -156169440), (12, -340761600), (13, -596332800), (25, 255571200), (26, -1078974720), (27, -106468560), (30, 425874240), (34, -965413440), (51, -440085600), (53, 766713600), (54, 425874240), (55, 511142400), (142, 170380800), (143, 468508320), (147, 425874240), (148, 425874240)]

theorem pairMergeCheck53 : pairMerged53 = Integer.Sparse.merge (Integer.Sparse.scale (354960) (rows 57)) (Integer.Sparse.scale (887238) (rows 58)) := by decide +kernel

theorem pairMergedZero53 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged53 x = 0 := by
  rw [pairMergeCheck53, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged54 : Integer.Sparse (Fin 271) := [(0, -19463154), (1, 407961540), (2, -91044150), (3, -2497974240), (4, -922805280), (5, 316333440), (6, -55077120), (7, -110686080), (8, -47673600), (10, 2488320), (11, -156169440), (12, -354338880), (13, -696103680), (25, 255571200), (26, -1078974720), (27, -106468560), (30, 425874240), (34, -1062972480), (51, -630780000), (53, 766713600), (54, 425874240), (55, 511142400), (80, -72339840), (114, 2488320), (115, -96176640), (132, 35755200), (133, 143020800), (142, 170380800), (143, 468508320), (147, 425874240), (148, 425874240)]

theorem pairMergeCheck54 : pairMerged54 = Integer.Sparse.merge pairMerged52 pairMerged53 := by decide +kernel

theorem pairMergedZero54 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged54 x = 0 := by
  rw [pairMergeCheck54, Integer.Sparse.eval_merge]
  rw [pairMergedZero52 x h, pairMergedZero53 x h]
  simp only [add_zero]

def pairMerged55 : Integer.Sparse (Fin 271) := [(0, 20700400), (1, -67199300), (2, -1503912660), (3, -8931624000), (4, -634164480), (5, 4102916080), (6, -552422560), (7, -3314535360), (8, -2838912000), (12, -2136598080), (13, -6958509760), (26, -634164480), (34, -6555978560), (51, -6946152960), (53, 1426870080), (55, 951246720), (58, 2129184000), (59, -946304000), (80, -634164480), (115, -1343892480), (132, 475623360), (133, 951246720)]

theorem pairMergeCheck55 : pairMerged55 = Integer.Sparse.merge (Integer.Sparse.scale (9908820) (rows 59)) (Integer.Sparse.scale (2957200) (rows 60)) := by decide +kernel

theorem pairMergedZero55 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged55 x = 0 := by
  rw [pairMergeCheck55, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged56 : Integer.Sparse (Fin 271) := [(0, 106242624), (1, 401250720), (2, -669469680), (3, -17088683520), (4, -361543680), (5, 1254169920), (6, -132770640), (7, -2169262080), (8, -1446174720), (12, -6103399680), (13, -16953888000), (26, -5470176000), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -3842184960), (51, -723087360), (54, 6103399680), (59, -1356311040), (60, 4068933120), (65, -361543680), (79, 1084631040)]

theorem pairMergeCheck56 : pairMerged56 = Integer.Sparse.merge (Integer.Sparse.scale (4519296) (rows 61)) (Integer.Sparse.scale (8476944) (rows 62)) := by decide +kernel

theorem pairMergedZero56 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged56 x = 0 := by
  rw [pairMergeCheck56, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged57 : Integer.Sparse (Fin 271) := [(0, 126943024), (1, 334051420), (2, -2173382340), (3, -26020307520), (4, -995708160), (5, 5357086000), (6, -685193200), (7, -5483797440), (8, -4285086720), (12, -8239997760), (13, -23912397760), (26, -6104340480), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -10398163520), (51, -7669240320), (53, 1426870080), (54, 6103399680), (55, 951246720), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (79, 1084631040), (80, -634164480), (115, -1343892480), (132, 475623360), (133, 951246720)]

theorem pairMergeCheck57 : pairMerged57 = Integer.Sparse.merge pairMerged55 pairMerged56 := by decide +kernel

theorem pairMergedZero57 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged57 x = 0 := by
  rw [pairMergeCheck57, Integer.Sparse.eval_merge]
  rw [pairMergedZero55 x h, pairMergedZero56 x h]
  simp only [add_zero]

def pairMerged58 : Integer.Sparse (Fin 271) := [(0, 107479870), (1, 742012960), (2, -2264426490), (3, -28518281760), (4, -1918513440), (5, 5673419440), (6, -740270320), (7, -5594483520), (8, -4332760320), (10, 2488320), (11, -156169440), (12, -8594336640), (13, -24608501440), (25, 255571200), (26, -7183315200), (27, -106468560), (30, 425874240), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -11461136000), (51, -8300020320), (53, 2193583680), (54, 6529273920), (55, 1462389120), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (79, 1084631040), (80, -706504320), (114, 2488320), (115, -1440069120), (132, 511378560), (133, 1094267520), (142, 170380800), (143, 468508320), (147, 425874240), (148, 425874240)]

theorem pairMergeCheck58 : pairMerged58 = Integer.Sparse.merge pairMerged54 pairMerged57 := by decide +kernel

theorem pairMergedZero58 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged58 x = 0 := by
  rw [pairMergeCheck58, Integer.Sparse.eval_merge]
  rw [pairMergedZero54 x h, pairMergedZero57 x h]
  simp only [add_zero]

def pairMerged59 : Integer.Sparse (Fin 271) := [(0, 121207772), (1, 365596540), (2, -659118840), (3, -22671873600), (4, -1688278080), (5, 2419870000), (6, -516959200), (7, 1066955520), (8, 1017689280), (9, 1792960), (10, -1885737600), (11, 33536640), (12, -7416172800), (13, -23164073280), (23, 21977280), (24, 3974400), (25, 255571200), (26, -6720194880), (27, -118368000), (29, -34341120), (30, 425874240), (31, -1356311040), (32, 6103399680), (33, -4068933120), (34, -7204554560), (50, 129536640), (51, -7376843520), (53, 2309578560), (54, 6554612160), (55, 1563742080), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (67, 9521280), (68, 19390080), (69, -71942400), (79, 1084631040), (80, -77095680), (111, 28748160), (112, 59322240), (113, 65664000), (114, 2488320), (115, -1440069120), (130, 38664960), (131, -16139520), (132, 511378560), (133, 1094267520), (142, 170380800), (143, -100609920), (146, -68682240), (147, 425874240), (148, 425874240)]

theorem pairMergeCheck59 : pairMerged59 = Integer.Sparse.merge pairMerged51 pairMerged58 := by decide +kernel

theorem pairMergedZero59 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged59 x = 0 := by
  rw [pairMergeCheck59, Integer.Sparse.eval_merge]
  rw [pairMergedZero51 x h, pairMergedZero58 x h]
  simp only [add_zero]

def pairMerged60 : Integer.Sparse (Fin 271) := [(0, -175861813), (1, 2161845710), (2, -1668932445), (3, -25647464160), (4, -5359969440), (5, 2273248880), (6, -510237190), (7, 1560717600), (8, 1412002560), (9, 11713280), (10, -1885737600), (11, 33536640), (12, -8567796960), (13, -20339264880), (14, 1072211040), (15, 2232187200), (16, -638511120), (17, 1369487520), (18, -3333679200), (19, -1559269440), (20, 2738975040), (21, -1559269440), (23, -2928530880), (24, 250254720), (25, -2681309520), (26, -3092006880), (27, -369473940), (29, -703049760), (30, 6402592800), (31, -1356311040), (32, 610214400), (33, -4068933120), (34, -7157419840), (35, 1493497440), (36, 3338003520), (37, -433533600), (38, 4227880320), (39, 4649944320), (40, -881772480), (41, 3169324800), (42, 1069541280), (43, 2738975040), (44, -2811844800), (45, -5550819840), (46, -779634720), (47, 2734274880), (49, -638511120), (50, 443077920), (51, -7376843520), (52, 145981440), (53, 2017843200), (54, 725447520), (55, 2531062080), (56, 74787840), (57, -972360), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (66, -33852000), (67, 80223360), (68, 42957440), (69, 69461760), (79, 1084631040), (80, -77095680), (111, 28748160), (112, 59322240), (113, 65664000), (114, 2488320), (115, -1440069120), (130, 38664960), (131, -16139520), (132, 511378560), (133, 1094267520), (142, 170380800), (143, -100609920), (146, -68682240), (147, 425874240), (148, 425874240)]

theorem pairMergeCheck60 : pairMerged60 = Integer.Sparse.merge pairMerged44 pairMerged59 := by decide +kernel

theorem pairMergedZero60 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged60 x = 0 := by
  rw [pairMergeCheck60, Integer.Sparse.eval_merge]
  rw [pairMergedZero44 x h, pairMergedZero59 x h]
  simp only [add_zero]

def pairMerged61 : Integer.Sparse (Fin 271) := [(0, -7827687), (1, -375567690), (2, -2748339445), (3, -391602720), (4, 5024984160), (5, 2021660200), (6, -184596880), (7, -1436280960), (8, -2385636480), (9, 11713280), (10, -1885737600), (11, 33536640), (12, -399672480), (13, -11415440400), (14, -2177280), (15, -174752640), (16, 38024640), (17, -131207040), (18, 16277760), (20, 142248960), (21, 37324800), (22, -9953280), (23, 6723750240), (24, 13474975680), (25, -2951681040), (26, -938592000), (27, -6660731520), (28, 97977600), (29, 10409509440), (30, -4561295040), (31, -1814405120), (32, -9395513280), (33, -3394560000), (34, -3432207200), (35, 1493497440), (36, 3338003520), (37, -433533600), (38, 4227880320), (39, 4649944320), (40, -881772480), (41, 3169324800), (42, 589619520), (43, 4042042560), (44, -3197819520), (45, -4247752320), (46, 486920160), (47, 1462743360), (48, -9953280), (49, 3906081360), (50, 5754528000), (51, -5616688800), (52, 145981440), (53, 2030490720), (54, 2182822560), (55, -581823360), (56, 74787840), (57, -972360), (58, 2129184000), (59, -2302615040), (60, 4068933120), (65, -361543680), (66, -33852000), (67, 80223360), (68, 42957440), (69, 69461760), (79, 1084631040), (80, -77095680), (111, 28748160), (112, 59322240), (113, 65664000), (114, 2488320), (115, -1440069120), (130, 38664960), (131, -16139520), (132, 511378560), (133, 1094267520), (142, 170380800), (143, -100609920), (146, -68682240), (147, 425874240), (148, 425874240)]

theorem pairMergeCheck61 : pairMerged61 = Integer.Sparse.merge pairMerged29 pairMerged60 := by decide +kernel

theorem pairMergedZero61 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged61 x = 0 := by
  rw [pairMergeCheck61, Integer.Sparse.eval_merge]
  rw [pairMergedZero29 x h, pairMergedZero60 x h]
  simp only [add_zero]

def pairMerged62 : Integer.Sparse (Fin 271) := [(0, 13193040), (1, 39671280), (2, -32953800), (3, -1689262080), (5, 52933440), (6, -6659880), (7, -921600), (12, -632897280), (13, -1477067520), (23, 1382400), (25, 315527040), (26, -423467520), (32, 1264872960), (33, -212194560), (34, -213116160), (51, -210351360), (53, 2764800), (54, 633818880), (62, 316909440), (63, 631054080), (64, 2764800), (65, -921600)]

theorem pairMergeCheck62 : pairMerged62 = Integer.Sparse.merge (Integer.Sparse.scale (6573480) (rows 63)) (Integer.Sparse.scale (5760) (rows 64)) := by decide +kernel

theorem pairMergedZero62 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged62 x = 0 := by
  rw [pairMergeCheck62, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged63 : Integer.Sparse (Fin 271) := [(0, -51051744), (1, 28266080), (2, 368668640), (3, 8165514240), (5, -341612160), (6, 28611680), (7, 4147200), (12, 4078609920), (13, 14952138240), (26, 1360919040), (31, 1811793920), (32, -12441600), (33, 2713543680), (34, 1369213440), (51, 2721838080), (53, -12441600), (58, -4070315520), (59, 2264051200), (60, -4070315520), (61, -8294400), (115, 1356771840)]

theorem pairMergeCheck63 : pairMerged63 = Integer.Sparse.merge (Integer.Sparse.scale (-5653216) (rows 65)) (Integer.Sparse.scale (-172800) (rows 66)) := by decide +kernel

theorem pairMergedZero63 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged63 x = 0 := by
  rw [pairMergeCheck63, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
