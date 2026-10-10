import OAI.Analysis.MutuallyUnbiased.Certificate.IntegerMerge
import OAI.Analysis.MutuallyUnbiased.PairData.Data
import OAI.Analysis.MutuallyUnbiased.PairMerge.Block8

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged288 : Integer.Sparse (Fin 271) := [(0, -81486405), (1, 707190750), (2, 3773385), (3, -2750721120), (4, -1078116480), (5, -21409920), (7, 171279360), (12, -231789600), (13, -725442480), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -1314804960), (24, -544047840), (25, -1072990800), (27, 196465500), (32, -1027676160), (35, 1541514240), (37, -1450884960), (47, 1541514240), (49, -725442480), (50, -513838080), (53, -513838080), (54, -30209760)]

theorem pairMergeCheck288 : pairMerged288 = Integer.Sparse.merge (Integer.Sparse.scale (2140992) (rows 40)) (Integer.Sparse.scale (-1007559) (rows 41)) := by decide +kernel

theorem pairMergedZero288 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged288 x = 0 := by
  rw [pairMergeCheck288, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged289 : Integer.Sparse (Fin 271) := [(0, 52529715), (1, -1974730590), (2, 1238574645), (3, 8070723360), (4, 3264649920), (5, -512749440), (7, 1153958400), (8, 1474018560), (12, 2124753120), (13, 1123068240), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -1314804960), (24, -2018066400), (25, -1072990800), (26, 2673155520), (27, 749222460), (29, -737009280), (30, -1423941120), (32, -3925635840), (35, 1541514240), (36, 2211027840), (37, -1450884960), (38, 2211027840), (39, 2211027840), (40, -37558080), (41, 2135911680), (47, 1541514240), (49, -725442480), (50, -3461875200), (53, -513838080), (54, -2241237600), (55, -1474018560)]

theorem pairMergeCheck289 : pairMerged289 = Integer.Sparse.merge pairMerged287 pairMerged288 := by decide +kernel

theorem pairMergedZero289 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged289 x = 0 := by
  rw [pairMergeCheck289, Integer.Sparse.eval_merge]
  rw [pairMergedZero287 x h, pairMergedZero288 x h]
  simp only [add_zero]

def pairMerged290 : Integer.Sparse (Fin 271) := [(0, 249978393), (1, -4979053800), (2, 2133674865), (3, 17649757440), (4, 5357016000), (5, -783639360), (7, 1448254080), (8, 2463955200), (12, 5667278400), (13, 5503483440), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -1615813920), (24, -2018066400), (25, -2321116560), (26, 3906584640), (27, 974979180), (29, -1339027200), (30, -2547417600), (32, -4799813760), (35, 1354540320), (36, 2211027840), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (47, 1541514240), (49, -725442480), (50, -4665911040), (53, -1958463360), (54, -3144264480), (55, -1474018560)]

theorem pairMergeCheck290 : pairMerged290 = Integer.Sparse.merge pairMerged286 pairMerged289 := by decide +kernel

theorem pairMergedZero290 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged290 x = 0 := by
  rw [pairMergeCheck290, Integer.Sparse.eval_merge]
  rw [pairMergedZero286 x h, pairMergedZero289 x h]
  simp only [add_zero]

def pairMerged291 : Integer.Sparse (Fin 271) := [(0, -86155083), (1, -1765898820), (2, 305031825), (3, 7619391360), (4, -346187520), (5, -262316880), (7, 275607360), (8, 834986880), (12, 2673881280), (13, 6095159280), (14, 770757120), (15, 1632143520), (16, -725442480), (18, -2901769920), (23, -2395824480), (24, -60147360), (25, 480498480), (26, 3429760320), (27, 338260860), (29, -750072960), (30, 3908217600), (32, -563915520), (35, 1354540320), (36, 2211027840), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (42, 886697280), (43, 947116800), (44, -4737216960), (45, -2276346240), (46, 1946488320), (47, -404974080), (49, -725442480), (50, -367960320), (53, -1958463360), (54, -3924275040), (55, 674956800)]

theorem pairMergeCheck291 : pairMerged291 = Integer.Sparse.merge pairMerged284 pairMerged290 := by decide +kernel

theorem pairMergedZero291 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged291 x = 0 := by
  rw [pairMergeCheck291, Integer.Sparse.eval_merge]
  rw [pairMergedZero284 x h, pairMergedZero290 x h]
  simp only [add_zero]

def pairMerged292 : Integer.Sparse (Fin 271) := [(0, 432508356), (1, -4436865720), (2, 1073160900), (3, 5691591360), (4, 7223942880), (5, -129412080), (6, 2494800), (7, 437814720), (8, 656722080), (9, -2661120), (12, 875629440), (17, 1970166240), (20, 3940332480), (23, -656722080), (24, -3283610400), (25, -1970166240), (26, 437814720), (27, 522479160), (29, -1970166240), (30, -3940332480), (43, 3940332480), (44, 3940332480), (47, 1970166240), (50, -656722080), (66, 39916800)]

theorem pairMergeCheck292 : pairMerged292 = Integer.Sparse.merge (Integer.Sparse.scale (5472684) (rows 43)) (Integer.Sparse.scale (166320) (rows 45)) := by decide +kernel

theorem pairMergedZero292 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged292 x = 0 := by
  rw [pairMergeCheck292, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged293 : Integer.Sparse (Fin 271) := [(0, 456957396), (1, -4782764070), (2, 1144007550), (3, 6825137760), (4, 7712923680), (5, -134968680), (6, 2494800), (7, 460041120), (8, 678948480), (9, -2661120), (12, 1120119840), (15, 200037600), (17, 1970166240), (18, 200037600), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -723401280), (24, -3683685600), (25, -2036845440), (26, 571173120), (27, 572488560), (29, -1970166240), (30, -4207049280), (36, 400075200), (43, 3940332480), (44, 3940332480), (46, 200037600), (47, 2170203840), (50, -790080480), (55, -133358400), (66, 39916800)]

theorem pairMergeCheck293 : pairMerged293 = Integer.Sparse.merge (Integer.Sparse.scale (277830) (rows 42)) pairMerged292 := by decide +kernel

theorem pairMergedZero293 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged293 x = 0 := by
  rw [pairMergeCheck293, Integer.Sparse.eval_merge]
  rw [pairMergedZero292 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged294 : Integer.Sparse (Fin 271) := [(0, 611226), (1, -21642390), (2, -57754620), (3, 5987520), (5, 131974920), (6, -11975040), (7, -89812800), (8, -191600640), (9, 11725560), (12, 67858560), (13, 33929280), (23, -152681760), (34, 3991680), (67, -27941760), (68, 1995840), (69, -191600640), (111, -152681760), (112, -101787840)]

theorem pairMergeCheck294 : pairMerged294 = Integer.Sparse.merge (Integer.Sparse.scale (399168) (rows 46)) (Integer.Sparse.scale (-212058) (rows 47)) := by decide +kernel

theorem pairMergedZero294 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged294 x = 0 := by
  rw [pairMergeCheck294, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged295 : Integer.Sparse (Fin 271) := [(0, 1614816), (1, 3447360), (2, 2268000), (3, -114670080), (4, 56609280), (5, 8074080), (6, -1995840), (7, -3628800), (8, 28304640), (9, -514080), (12, -110678400), (13, -228735360), (23, 66407040), (24, -84913920), (26, 56609280), (34, -57335040), (51, -31933440), (53, 132814080), (67, 6168960), (68, -3265920), (69, 9434880), (112, 66407040), (113, -84913920), (130, 44271360), (131, -56609280)]

theorem pairMergeCheck295 : pairMerged295 = Integer.Sparse.merge (Integer.Sparse.scale (-117936) (rows 48)) (Integer.Sparse.scale (184464) (rows 49)) := by decide +kernel

theorem pairMergedZero295 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged295 x = 0 := by
  rw [pairMergeCheck295, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged296 : Integer.Sparse (Fin 271) := [(0, 2226042), (1, -18195030), (2, -55486620), (3, -108682560), (4, 56609280), (5, 140049000), (6, -13970880), (7, -93441600), (8, -163296000), (9, 11211480), (12, -42819840), (13, -194806080), (23, -86274720), (24, -84913920), (26, 56609280), (34, -53343360), (51, -31933440), (53, 132814080), (67, -21772800), (68, -1270080), (69, -182165760), (111, -152681760), (112, -35380800), (113, -84913920), (130, 44271360), (131, -56609280)]

theorem pairMergeCheck296 : pairMerged296 = Integer.Sparse.merge pairMerged294 pairMerged295 := by decide +kernel

theorem pairMergedZero296 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged296 x = 0 := by
  rw [pairMergeCheck296, Integer.Sparse.eval_merge]
  rw [pairMergedZero294 x h, pairMergedZero295 x h]
  simp only [add_zero]

def pairMerged297 : Integer.Sparse (Fin 271) := [(0, 459183438), (1, -4800959100), (2, 1088520930), (3, 6716455200), (4, 7769532960), (5, 5080320), (6, -11476080), (7, 366599520), (8, 515652480), (9, 8550360), (12, 1077300000), (13, -194806080), (15, 200037600), (17, 1970166240), (18, 200037600), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -809676000), (24, -3768599520), (25, -2036845440), (26, 627782400), (27, 572488560), (29, -1970166240), (30, -4207049280), (34, -53343360), (36, 400075200), (43, 3940332480), (44, 3940332480), (46, 200037600), (47, 2170203840), (50, -790080480), (51, -31933440), (53, 132814080), (55, -133358400), (66, 39916800), (67, -21772800), (68, -1270080), (69, -182165760), (111, -152681760), (112, -35380800), (113, -84913920), (130, 44271360), (131, -56609280)]

theorem pairMergeCheck297 : pairMerged297 = Integer.Sparse.merge pairMerged293 pairMerged296 := by decide +kernel

theorem pairMergedZero297 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged297 x = 0 := by
  rw [pairMergeCheck297, Integer.Sparse.eval_merge]
  rw [pairMergedZero293 x h, pairMergedZero296 x h]
  simp only [add_zero]

def pairMerged298 : Integer.Sparse (Fin 271) := [(0, 7969752), (1, -38363220), (2, 142702560), (3, 195410880), (4, 5080320), (5, -256782960), (6, 26546940), (7, 93260160), (8, 461220480), (9, -11657520), (13, 6350400), (24, -7620480), (26, 5080320), (27, 34020000), (29, -272160000), (34, 6350400), (51, 95800320), (54, -3810240), (55, -15240960), (67, 46630080), (68, 1270080), (69, 231880320), (112, -3810240), (113, -136080000), (131, -15240960), (146, -544320000)]

theorem pairMergeCheck298 : pairMerged298 = Integer.Sparse.merge (Integer.Sparse.scale (-567000) (rows 51)) (Integer.Sparse.scale (-15876) (rows 52)) := by decide +kernel

theorem pairMergedZero298 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged298 x = 0 := by
  rw [pairMergeCheck298, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged299 : Integer.Sparse (Fin 271) := [(0, 7348320), (1, -31372110), (2, 106970220), (3, 95981760), (4, -19776960), (5, -213282720), (6, 24216570), (7, 18688320), (8, 386648640), (9, -8550360), (13, 6350400), (24, 66951360), (26, 5080320), (27, 24698520), (29, -272160000), (34, 6350400), (50, 74571840), (51, 70943040), (54, -3810240), (55, -15240960), (67, 21772800), (68, 1270080), (69, 182165760), (111, 37285920), (112, -3810240), (113, 13063680), (131, -15240960), (146, -544320000)]

theorem pairMergeCheck299 : pairMerged299 = Integer.Sparse.merge (Integer.Sparse.scale (155358) (rows 50)) pairMerged298 := by decide +kernel

theorem pairMergedZero299 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged299 x = 0 := by
  rw [pairMergeCheck299, Integer.Sparse.eval_merge]
  rw [pairMergedZero298 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged300 : Integer.Sparse (Fin 271) := [(0, 8714034), (1, -290504340), (2, 1257630570), (3, 4599957600), (4, 139073760), (5, -2549700720), (6, 174171060), (7, 5158883520), (8, 4182736320), (10, -1464220800), (11, 139073760), (12, 976147200), (13, 1301529600), (26, 278147520), (34, 3252070080), (51, 695368800), (80, 488073600), (143, -417221280)]

theorem pairMergeCheck300 : pairMerged300 = Integer.Sparse.merge (Integer.Sparse.scale (-8134560) (rows 53)) (Integer.Sparse.scale (-579474) (rows 54)) := by decide +kernel

theorem pairMergedZero300 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged300 x = 0 := by
  rw [pairMergeCheck300, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged301 : Integer.Sparse (Fin 271) := [(0, -5298048), (1, 263042640), (2, 117936000), (3, -1111864320), (4, -489888000), (5, -88996320), (6, 12111120), (7, -33022080), (8, 129911040), (11, -97977600), (12, -359432640), (13, -426021120), (25, 293932800), (26, -587865600), (34, -360702720), (51, 421666560), (53, 881798400), (55, 587865600), (80, 194866560), (115, 259822080), (132, -97433280), (133, -389733120), (142, 195955200), (143, 293932800)]

theorem pairMergeCheck301 : pairMerged301 = Integer.Sparse.merge (Integer.Sparse.scale (-1623888) (rows 55)) (Integer.Sparse.scale (408240) (rows 57)) := by decide +kernel

theorem pairMergedZero301 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged301 x = 0 := by
  rw [pairMergeCheck301, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged302 : Integer.Sparse (Fin 271) := [(0, 3415986), (1, -27461700), (2, 1375566570), (3, 3488093280), (4, -350814240), (5, -2638697040), (6, 186282180), (7, 5125861440), (8, 4312647360), (10, -1464220800), (11, 41096160), (12, 616714560), (13, 875508480), (25, 293932800), (26, -309718080), (34, 2891367360), (51, 1117035360), (53, 881798400), (55, 587865600), (80, 682940160), (115, 259822080), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480)]

theorem pairMergeCheck302 : pairMerged302 = Integer.Sparse.merge pairMerged300 pairMerged301 := by decide +kernel

theorem pairMergedZero302 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged302 x = 0 := by
  rw [pairMergeCheck302, Integer.Sparse.eval_merge]
  rw [pairMergedZero300 x h, pairMergedZero301 x h]
  simp only [add_zero]

def pairMerged303 : Integer.Sparse (Fin 271) := [(0, 10764306), (1, -58833810), (2, 1482536790), (3, 3584075040), (4, -370591200), (5, -2851979760), (6, 210498750), (7, 5144549760), (8, 4699296000), (9, -8550360), (10, -1464220800), (11, 41096160), (12, 616714560), (13, 881858880), (24, 66951360), (25, 293932800), (26, -304637760), (27, 24698520), (29, -272160000), (34, 2897717760), (50, 74571840), (51, 1187978400), (53, 881798400), (54, -3810240), (55, 572624640), (67, 21772800), (68, 1270080), (69, 182165760), (80, 682940160), (111, 37285920), (112, -3810240), (113, 13063680), (115, 259822080), (131, -15240960), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

theorem pairMergeCheck303 : pairMerged303 = Integer.Sparse.merge pairMerged299 pairMerged302 := by decide +kernel

theorem pairMergedZero303 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged303 x = 0 := by
  rw [pairMergeCheck303, Integer.Sparse.eval_merge]
  rw [pairMergedZero299 x h, pairMergedZero302 x h]
  simp only [add_zero]

def pairMerged304 : Integer.Sparse (Fin 271) := [(0, 469947744), (1, -4859792910), (2, 2571057720), (3, 10300530240), (4, 7398941760), (5, -2846899440), (6, 199022670), (7, 5511149280), (8, 5214948480), (10, -1464220800), (11, 41096160), (12, 1694014560), (13, 687052800), (15, 200037600), (17, 1970166240), (18, 200037600), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -809676000), (24, -3701648160), (25, -1742912640), (26, 323144640), (27, 597187080), (29, -2242326240), (30, -4207049280), (34, 2844374400), (36, 400075200), (43, 3940332480), (44, 3940332480), (46, 200037600), (47, 2170203840), (50, -715508640), (51, 1156044960), (53, 1014612480), (54, -3810240), (55, 439266240), (66, 39916800), (80, 682940160), (111, -115395840), (112, -39191040), (113, -71850240), (115, 259822080), (130, 44271360), (131, -71850240), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

theorem pairMergeCheck304 : pairMerged304 = Integer.Sparse.merge pairMerged297 pairMerged303 := by decide +kernel

theorem pairMergedZero304 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged304 x = 0 := by
  rw [pairMergeCheck304, Integer.Sparse.eval_merge]
  rw [pairMergedZero297 x h, pairMergedZero303 x h]
  simp only [add_zero]

def pairMerged305 : Integer.Sparse (Fin 271) := [(0, 383792661), (1, -6625691730), (2, 2876089545), (3, 17919921600), (4, 7052754240), (5, -3109216320), (6, 199022670), (7, 5786756640), (8, 6049935360), (10, -1464220800), (11, 41096160), (12, 4367895840), (13, 6782212080), (14, 770757120), (15, 1832181120), (16, -725442480), (17, 1970166240), (18, -2701732320), (19, 400075200), (20, 3940332480), (21, 400075200), (23, -3205500480), (24, -3761795520), (25, -1262414160), (26, 3752904960), (27, 935447940), (29, -2992399200), (30, -298831680), (32, -563915520), (34, 2844374400), (35, 1354540320), (36, 2611103040), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (42, 886697280), (43, 4887449280), (44, -796884480), (45, -2276346240), (46, 2146525920), (47, 1765229760), (49, -725442480), (50, -1083468960), (51, 1156044960), (53, -943850880), (54, -3928085280), (55, 1114223040), (66, 39916800), (80, 682940160), (111, -115395840), (112, -39191040), (113, -71850240), (115, 259822080), (130, 44271360), (131, -71850240), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

theorem pairMergeCheck305 : pairMerged305 = Integer.Sparse.merge pairMerged291 pairMerged304 := by decide +kernel

theorem pairMergedZero305 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged305 x = 0 := by
  rw [pairMergeCheck305, Integer.Sparse.eval_merge]
  rw [pairMergedZero291 x h, pairMergedZero304 x h]
  simp only [add_zero]

def pairMerged306 : Integer.Sparse (Fin 271) := [(0, 74977623), (1, -3284859690), (2, 116920125), (3, 26488425600), (4, 8149196160), (5, -1923982200), (6, 312972660), (7, 2170022400), (8, 931150080), (10, -1464220800), (11, 41096160), (12, 8748038880), (13, 12059454960), (15, -186157440), (16, 34292160), (17, -107775360), (20, 156764160), (23, 3307560480), (24, 7022272320), (25, -3825072720), (26, 4907226240), (27, -3541754160), (28, 97977600), (29, 5713727040), (30, -5467150080), (31, -282078720), (32, -11238575040), (33, 213373440), (34, 5151656160), (35, 1354540320), (36, 2611103040), (37, 668697120), (38, 3896242560), (39, 4017081600), (40, -37558080), (41, 2135911680), (42, 886697280), (43, 4887449280), (44, -1616630400), (45, -2276346240), (46, 2146525920), (47, 1765229760), (49, 2947084560), (50, 3858140160), (51, 1334128320), (53, -550035360), (54, -4844175840), (55, -1217099520), (66, 39916800), (80, 682940160), (111, -115395840), (112, -39191040), (113, -71850240), (115, 259822080), (130, 44271360), (131, -71850240), (132, -97433280), (133, -389733120), (142, 195955200), (143, -123288480), (146, -544320000)]

theorem pairMergeCheck306 : pairMerged306 = Integer.Sparse.merge pairMerged279 pairMerged305 := by decide +kernel

theorem pairMergedZero306 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged306 x = 0 := by
  rw [pairMergeCheck306, Integer.Sparse.eval_merge]
  rw [pairMergedZero279 x h, pairMergedZero305 x h]
  simp only [add_zero]

def pairMerged307 : Integer.Sparse (Fin 271) := [(0, 12340944), (1, 126664020), (2, -958513500), (3, -7230202560), (4, -682940160), (5, 2655631440), (6, -367446240), (7, -2204677440), (8, -1692472320), (12, -1959733440), (13, -5901456960), (26, -682940160), (34, -4899303360), (51, -4750824960), (53, 1536615360), (55, 1024410240), (58, 1269354240), (59, -564157440), (80, -682940160), (115, -1106058240), (132, 512205120), (133, 1024410240)]

theorem pairMergeCheck307 : pairMerged307 = Integer.Sparse.merge (Integer.Sparse.scale (10670940) (rows 59)) (Integer.Sparse.scale (1762992) (rows 60)) := by decide +kernel

theorem pairMergedZero307 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged307 x = 0 := by
  rw [pairMergeCheck307, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged308 : Integer.Sparse (Fin 271) := [(0, 2580606), (1, 265363560), (2, -1012452210), (3, -7928837280), (4, -970613280), (5, 2778919920), (6, -387994320), (7, -2204677440), (8, -1692472320), (11, -41096160), (12, -1959733440), (13, -5901456960), (26, -1011709440), (27, -61644240), (30, 246576960), (34, -5145880320), (51, -4956305760), (53, 1536615360), (54, 246576960), (55, 1024410240), (58, 1269354240), (59, -564157440), (80, -682940160), (115, -1106058240), (132, 512205120), (133, 1024410240), (143, 123288480), (147, 246576960), (148, 246576960)]

theorem pairMergeCheck308 : pairMerged308 = Integer.Sparse.merge (Integer.Sparse.scale (513702) (rows 58)) pairMerged307 := by decide +kernel

theorem pairMergedZero308 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged308 x = 0 := by
  rw [pairMergeCheck308, Integer.Sparse.eval_merge]
  rw [pairMergedZero307 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged309 : Integer.Sparse (Fin 271) := [(0, 72675792), (1, 292073040), (2, -102354840), (3, -10487232000), (5, 142611840), (6, -31048920), (12, -4250050560), (13, -11609256960), (25, 220993920), (26, -3256485120), (31, -846236160), (32, 4692038400), (33, -2686037760), (34, -1416683520), (51, -147329280), (54, 4250050560), (59, -846236160), (60, 2538708480), (62, 220993920), (63, 441987840)]

theorem pairMergeCheck309 : pairMerged309 = Integer.Sparse.merge (Integer.Sparse.scale (5288976) (rows 62)) (Integer.Sparse.scale (4604040) (rows 63)) := by decide +kernel

theorem pairMergedZero309 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged309 x = 0 := by
  rw [pairMergeCheck309, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged310 : Integer.Sparse (Fin 271) := [(0, 76576752), (1, 272568240), (2, -570470040), (3, -12359692800), (4, -312076800), (5, 1078842240), (6, -109068120), (7, -1872460800), (8, -1248307200), (12, -4250050560), (13, -11609256960), (25, 220993920), (26, -3880638720), (31, -846236160), (32, 4692038400), (33, -2686037760), (34, -2977067520), (51, -771482880), (54, 4250050560), (59, -846236160), (60, 2538708480), (62, 220993920), (63, 441987840), (65, -312076800), (79, 936230400)]

theorem pairMergeCheck310 : pairMerged310 = Integer.Sparse.merge (Integer.Sparse.scale (3900960) (rows 61)) pairMerged309 := by decide +kernel

theorem pairMergedZero310 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged310 x = 0 := by
  rw [pairMergeCheck310, Integer.Sparse.eval_merge]
  rw [pairMergedZero309 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged311 : Integer.Sparse (Fin 271) := [(0, 79157358), (1, 537931800), (2, -1582922250), (3, -20288530080), (4, -1282690080), (5, 3857762160), (6, -497062440), (7, -4077138240), (8, -2940779520), (11, -41096160), (12, -6209784000), (13, -17510713920), (25, 220993920), (26, -4892348160), (27, -61644240), (30, 246576960), (31, -846236160), (32, 4692038400), (33, -2686037760), (34, -8122947840), (51, -5727788640), (53, 1536615360), (54, 4496627520), (55, 1024410240), (58, 1269354240), (59, -1410393600), (60, 2538708480), (62, 220993920), (63, 441987840), (65, -312076800), (79, 936230400), (80, -682940160), (115, -1106058240), (132, 512205120), (133, 1024410240), (143, 123288480), (147, 246576960), (148, 246576960)]

theorem pairMergeCheck311 : pairMerged311 = Integer.Sparse.merge pairMerged308 pairMerged310 := by decide +kernel

theorem pairMergedZero311 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged311 x = 0 := by
  rw [pairMergeCheck311, Integer.Sparse.eval_merge]
  rw [pairMergedZero308 x h, pairMergedZero310 x h]
  simp only [add_zero]

def pairMerged312 : Integer.Sparse (Fin 271) := [(0, -9362304), (1, -248686200), (2, 303299640), (3, 3666902400), (4, 62415360), (5, -487620000), (6, 60464880), (7, 1139080320), (8, 312076800), (12, 1435553280), (13, 3261202560), (25, 140434560), (26, 1092268800), (30, 280869120), (32, 561738240), (33, 780192000), (34, 1700818560), (50, -936230400), (51, 1279514880), (53, -608549760), (63, -468115200), (65, 312076800), (79, 280869120), (110, 280869120)]

theorem pairMergeCheck312 : pairMerged312 = Integer.Sparse.merge (Integer.Sparse.scale (585144) (rows 67)) (Integer.Sparse.scale (-12678120) (rows 68)) := by decide +kernel

theorem pairMergedZero312 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged312 x = 0 := by
  rw [pairMergeCheck312, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged313 : Integer.Sparse (Fin 271) := [(0, -41096160), (1, -231056280), (2, 532488600), (3, 8744319360), (4, 62415360), (5, -699179040), (6, 78094800), (7, 1139080320), (8, 312076800), (12, 3974261760), (13, 12569800320), (25, 140434560), (26, 1938504960), (30, 280869120), (31, 1128314880), (32, 561738240), (33, 2472664320), (34, 2547054720), (50, -936230400), (51, 2971987200), (53, -608549760), (58, -2538708480), (59, 1410393600), (60, -2538708480), (63, -468115200), (65, 312076800), (79, 280869120), (110, 280869120), (115, 846236160)]

theorem pairMergeCheck313 : pairMerged313 = Integer.Sparse.merge (Integer.Sparse.scale (-3525984) (rows 65)) pairMerged312 := by decide +kernel

theorem pairMergedZero313 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged313 x = 0 := by
  rw [pairMergeCheck313, Integer.Sparse.eval_merge]
  rw [pairMergedZero312 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged314 : Integer.Sparse (Fin 271) := [(0, 150259536), (1, -2232437760), (2, 1754887680), (3, 5873575680), (4, 1985679360), (5, -1033754400), (6, 32477760), (7, 1594857600), (8, 2085471360), (10, -1409244480), (12, 2029769280), (13, 1382572800), (23, -3820582080), (24, -10424816640), (27, 3889302480), (29, -6151904640), (34, 389733120), (50, -779466240), (51, 259822080), (53, -389733120), (54, -5957038080), (58, -779466240), (70, 292299840), (72, 584599680), (73, 584599680), (77, 1116944640), (78, 2233889280), (132, -292299840)]

theorem pairMergeCheck314 : pairMerged314 = Integer.Sparse.merge (Integer.Sparse.scale (31026240) (rows 69)) (Integer.Sparse.scale (1623888) (rows 71)) := by decide +kernel

theorem pairMergedZero314 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged314 x = 0 := by
  rw [pairMergeCheck314, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged315 : Integer.Sparse (Fin 271) := [(0, 2519748), (1, -54976320), (2, -245102760), (3, -549763200), (4, -183254400), (5, 549763200), (6, -51540300), (7, -824644800), (8, -696366720), (12, 109952640), (13, 146603520), (26, -219905280), (34, -476461440), (51, -329857920), (71, 164928960), (73, 329857920), (79, 219905280), (82, -329857920), (83, -659715840), (133, -164928960), (143, 329857920)]

theorem pairMergeCheck315 : pairMerged315 = Integer.Sparse.merge (Integer.Sparse.scale (-458136) (rows 72)) (Integer.Sparse.scale (229068) (rows 74)) := by decide +kernel

theorem pairMergedZero315 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged315 x = 0 := by
  rw [pairMergeCheck315, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged316 : Integer.Sparse (Fin 271) := [(0, 152779284), (1, -2287414080), (2, 1509784920), (3, 5323812480), (4, 1802424960), (5, -483991200), (6, -19062540), (7, 770212800), (8, 1389104640), (10, -1409244480), (12, 2139721920), (13, 1529176320), (23, -3820582080), (24, -10424816640), (26, -219905280), (27, 3889302480), (29, -6151904640), (34, -86728320), (50, -779466240), (51, -70035840), (53, -389733120), (54, -5957038080), (58, -779466240), (70, 292299840), (71, 164928960), (72, 584599680), (73, 914457600), (77, 1116944640), (78, 2233889280), (79, 219905280), (82, -329857920), (83, -659715840), (132, -292299840), (133, -164928960), (143, 329857920)]

theorem pairMergeCheck316 : pairMerged316 = Integer.Sparse.merge pairMerged314 pairMerged315 := by decide +kernel

theorem pairMergedZero316 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged316 x = 0 := by
  rw [pairMergeCheck316, Integer.Sparse.eval_merge]
  rw [pairMergedZero314 x h, pairMergedZero315 x h]
  simp only [add_zero]

def pairMerged317 : Integer.Sparse (Fin 271) := [(0, 111683124), (1, -2518470360), (2, 2042273520), (3, 14068131840), (4, 1864840320), (5, -1183170240), (6, 59032260), (7, 1909293120), (8, 1701181440), (10, -1409244480), (12, 6113983680), (13, 14098976640), (23, -3820582080), (24, -10424816640), (25, 140434560), (26, 1718599680), (27, 3889302480), (29, -6151904640), (30, 280869120), (31, 1128314880), (32, 561738240), (33, 2472664320), (34, 2460326400), (50, -1715696640), (51, 2901951360), (53, -998282880), (54, -5957038080), (58, -3318174720), (59, 1410393600), (60, -2538708480), (63, -468115200), (65, 312076800), (70, 292299840), (71, 164928960), (72, 584599680), (73, 914457600), (77, 1116944640), (78, 2233889280), (79, 500774400), (82, -329857920), (83, -659715840), (110, 280869120), (115, 846236160), (132, -292299840), (133, -164928960), (143, 329857920)]

theorem pairMergeCheck317 : pairMerged317 = Integer.Sparse.merge pairMerged313 pairMerged316 := by decide +kernel

theorem pairMergedZero317 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged317 x = 0 := by
  rw [pairMergeCheck317, Integer.Sparse.eval_merge]
  rw [pairMergedZero313 x h, pairMergedZero316 x h]
  simp only [add_zero]

def pairMerged318 : Integer.Sparse (Fin 271) := [(0, 190840482), (1, -1980538560), (2, 459351270), (3, -6220398240), (4, 582150240), (5, 2674591920), (6, -438030180), (7, -2167845120), (8, -1239598080), (10, -1409244480), (11, -41096160), (12, -95800320), (13, -3411737280), (23, -3820582080), (24, -10424816640), (25, 361428480), (26, -3173748480), (27, 3827658240), (29, -6151904640), (30, 527446080), (31, 282078720), (32, 5253776640), (33, -213373440), (34, -5662621440), (50, -1715696640), (51, -2825837280), (53, 538332480), (54, -1460410560), (55, 1024410240), (58, -2048820480), (62, 220993920), (63, -26127360), (70, 292299840), (71, 164928960), (72, 584599680), (73, 914457600), (77, 1116944640), (78, 2233889280), (79, 1437004800), (80, -682940160), (82, -329857920), (83, -659715840), (110, 280869120), (115, -259822080), (132, 219905280), (133, 859481280), (143, 453146400), (147, 246576960), (148, 246576960)]

theorem pairMergeCheck318 : pairMerged318 = Integer.Sparse.merge pairMerged311 pairMerged317 := by decide +kernel

theorem pairMergedZero318 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged318 x = 0 := by
  rw [pairMergeCheck318, Integer.Sparse.eval_merge]
  rw [pairMergedZero311 x h, pairMergedZero317 x h]
  simp only [add_zero]

def pairMerged319 : Integer.Sparse (Fin 271) := [(0, -38359818), (1, 911770020), (2, -365865255), (3, -6769072800), (4, -1878901920), (5, 125000820), (6, -3433185), (7, -689018400), (8, -134084160), (10, 201126240), (12, -3641455440), (13, -1548454320), (23, 1938595680), (24, 1206757440), (25, 1519469280), (26, -439447680), (27, -351970920), (32, 329585760), (34, -219723840), (42, -1977514560), (46, -2413514880), (47, -1206757440), (49, -1097757360), (50, 1206757440), (51, -109861920), (54, 1134090720), (58, 402252480), (77, -603378720), (87, -1206757440), (96, -988757280), (103, -494378640)]

theorem pairMergeCheck319 : pairMerged319 = Integer.Sparse.merge (Integer.Sparse.scale (-838026) (rows 76)) (Integer.Sparse.scale (-3433185) (rows 77)) := by decide +kernel

theorem pairMergedZero319 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged319 x = 0 := by
  rw [pairMergeCheck319, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
