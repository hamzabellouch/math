import OAI.Analysis.MutuallyUnbiased.Certificate.IntegerMerge
import OAI.Analysis.MutuallyUnbiased.PairData.Data

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged0 : Integer.Sparse (Fin 271) := [(0, 138332760), (1, 8501053680), (2, -2890080960), (3, -23120647680), (4, -11560323840), (5, 5080523400), (6, -499592880), (7, -5780161920), (8, -2890080960), (12, -8670242880), (23, 4335121440), (24, 8670242880), (27, -5995114560)]

theorem pairMergeCheck0 : pairMerged0 = Integer.Sparse.merge (Integer.Sparse.scale (-499592880) (rows 1)) (Integer.Sparse.scale (361260120) (rows 2)) := by decide +kernel

theorem pairMergedZero0 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged0 x = 0 := by
  rw [pairMergeCheck0, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged1 : Integer.Sparse (Fin 271) := [(0, -528840840), (1, -4101114320), (2, -1036820960), (3, -17190215680), (4, 300540160), (5, 5080523400), (6, -499592880), (7, -5780161920), (8, -2890080960), (12, -5705026880), (23, 4335121440), (24, 8670242880), (27, -5995114560)]

theorem pairMergeCheck1 : pairMerged1 = Integer.Sparse.merge (Integer.Sparse.scale (-74130400) (rows 0)) pairMerged0 := by decide +kernel

theorem pairMergedZero1 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged1 x = 0 := by
  rw [pairMergeCheck1, Integer.Sparse.eval_merge]
  rw [pairMergedZero0 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged2 : Integer.Sparse (Fin 271) := [(0, 1714328), (1, -402065650), (2, -2209009090), (3, 23263569280), (4, 8328009920), (5, 1238915520), (7, -1651887360), (8, -8259436800), (12, 14935559360), (13, 7467779680), (24, 4955662080), (29, 9911324160)]

theorem pairMergeCheck2 : pairMerged2 = Integer.Sparse.merge (Integer.Sparse.scale (41297184) (rows 3)) (Integer.Sparse.scale (-93347246) (rows 4)) := by decide +kernel

theorem pairMergedZero2 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged2 x = 0 := by
  rw [pairMergeCheck2, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged3 : Integer.Sparse (Fin 271) := [(0, -1107976740), (1, 32648566440), (2, -6775888140), (3, -68779985280), (4, -48839748480), (12, -19940236800), (25, 5449439520), (26, -12674317440), (30, 16225194240)]

theorem pairMergeCheck3 : pairMerged3 = Integer.Sparse.merge (Integer.Sparse.scale (45411996) (rows 5)) (Integer.Sparse.scale (67604976) (rows 6)) := by decide +kernel

theorem pairMergedZero3 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged3 x = 0 := by
  rw [pairMergeCheck3, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged4 : Integer.Sparse (Fin 271) := [(0, -1106262412), (1, 32246500790), (2, -8984897230), (3, -45516416000), (4, -40511738560), (5, 1238915520), (7, -1651887360), (8, -8259436800), (12, -5004677440), (13, 7467779680), (24, 4955662080), (25, 5449439520), (26, -12674317440), (29, 9911324160), (30, 16225194240)]

theorem pairMergeCheck4 : pairMerged4 = Integer.Sparse.merge pairMerged2 pairMerged3 := by decide +kernel

theorem pairMergedZero4 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged4 x = 0 := by
  rw [pairMergeCheck4, Integer.Sparse.eval_merge]
  rw [pairMergedZero2 x h, pairMergedZero3 x h]
  simp only [add_zero]

def pairMerged5 : Integer.Sparse (Fin 271) := [(0, -1635103252), (1, 28145386470), (2, -10021718190), (3, -62706631680), (4, -40211198400), (5, 6319438920), (6, -499592880), (7, -7432049280), (8, -11149517760), (12, -10709704320), (13, 7467779680), (23, 4335121440), (24, 13625904960), (25, 5449439520), (26, -12674317440), (27, -5995114560), (29, 9911324160), (30, 16225194240)]

theorem pairMergeCheck5 : pairMerged5 = Integer.Sparse.merge pairMerged1 pairMerged4 := by decide +kernel

theorem pairMergedZero5 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged5 x = 0 := by
  rw [pairMergeCheck5, Integer.Sparse.eval_merge]
  rw [pairMergedZero1 x h, pairMergedZero4 x h]
  simp only [add_zero]

def pairMerged6 : Integer.Sparse (Fin 271) := [(0, -489718332), (1, 5557056000), (2, -1061293740), (3, -6003104640), (4, -8311991040), (12, -2308886400), (14, -1074388320), (15, -2077997760), (17, -4297553280), (20, -4155995520), (23, 3557701440), (24, 2077997760), (25, 7115402880), (27, -1056693600), (29, 2817849600), (30, 8500734720)]

theorem pairMergeCheck6 : pairMerged6 = Integer.Sparse.merge (Integer.Sparse.scale (-59688240) (rows 7)) (Integer.Sparse.scale (-2886108) (rows 8)) := by decide +kernel

theorem pairMergedZero6 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged6 x = 0 := by
  rw [pairMergeCheck6, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged7 : Integer.Sparse (Fin 271) := [(0, -89710500), (1, 3349521720), (2, 102819000), (3, -2519143680), (4, -3545995200), (12, -1032618240), (16, 676535760), (17, 1353071520), (18, -1582908480), (22, -3165816960), (23, -902047680), (27, 169133940), (29, -451023840)]

theorem pairMergeCheck7 : pairMerged7 = Integer.Sparse.merge (Integer.Sparse.scale (3758532) (rows 9)) (Integer.Sparse.scale (-4396968) (rows 10)) := by decide +kernel

theorem pairMergedZero7 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged7 x = 0 := by
  rw [pairMergeCheck7, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged8 : Integer.Sparse (Fin 271) := [(0, -579428832), (1, 8906577720), (2, -958474740), (3, -8522248320), (4, -11857986240), (12, -3341504640), (14, -1074388320), (15, -2077997760), (16, 676535760), (17, -2944481760), (18, -1582908480), (20, -4155995520), (22, -3165816960), (23, 2655653760), (24, 2077997760), (25, 7115402880), (27, -887559660), (29, 2366825760), (30, 8500734720)]

theorem pairMergeCheck8 : pairMerged8 = Integer.Sparse.merge pairMerged6 pairMerged7 := by decide +kernel

theorem pairMergedZero8 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged8 x = 0 := by
  rw [pairMergeCheck8, Integer.Sparse.eval_merge]
  rw [pairMergedZero6 x h, pairMergedZero7 x h]
  simp only [add_zero]

def pairMerged9 : Integer.Sparse (Fin 271) := [(0, 102527280), (1, -2538944880), (2, 401060880), (3, 2734060800), (4, 2953355520), (12, 427671360), (15, -328942080), (17, 1394798400), (19, 1559269440), (20, 1559269440), (22, 1559269440), (23, 164471040), (24, -2489135040), (25, 328942080), (27, 348699600), (29, -464932800), (30, -1750083840)]

theorem pairMergeCheck9 : pairMerged9 = Integer.Sparse.merge (Integer.Sparse.scale (-2284320) (rows 11)) (Integer.Sparse.scale (43313040) (rows 12)) := by decide +kernel

theorem pairMergedZero9 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged9 x = 0 := by
  rw [pairMergeCheck9, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged10 : Integer.Sparse (Fin 271) := [(0, 425465220), (1, -8119256040), (2, 1356329580), (3, 19540684800), (4, 13543423200), (12, 8303453280), (18, 4932865440), (21, 1596594240), (22, 1596594240), (25, -3288576960), (30, -4352973120)]

theorem pairMergeCheck10 : pairMerged10 = Integer.Sparse.merge (Integer.Sparse.scale (2217492) (rows 13)) (Integer.Sparse.scale (13702404) (rows 14)) := by decide +kernel

theorem pairMergedZero10 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged10 x = 0 := by
  rw [pairMergeCheck10, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged11 : Integer.Sparse (Fin 271) := [(0, 527992500), (1, -10658200920), (2, 1757390460), (3, 22274745600), (4, 16496778720), (12, 8731124640), (15, -328942080), (17, 1394798400), (18, 4932865440), (19, 1559269440), (20, 1559269440), (21, 1596594240), (22, 3155863680), (23, 164471040), (24, -2489135040), (25, -2959634880), (27, 348699600), (29, -464932800), (30, -6103056960)]

theorem pairMergeCheck11 : pairMerged11 = Integer.Sparse.merge pairMerged9 pairMerged10 := by decide +kernel

theorem pairMergedZero11 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged11 x = 0 := by
  rw [pairMergeCheck11, Integer.Sparse.eval_merge]
  rw [pairMergedZero9 x h, pairMergedZero10 x h]
  simp only [add_zero]

def pairMerged12 : Integer.Sparse (Fin 271) := [(0, -51436332), (1, -1751623200), (2, 798915720), (3, 13752497280), (4, 4638792480), (12, 5389620000), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1549683360), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 2820124800), (24, -411137280), (25, 4155768000), (27, -538860060), (29, 1901892960), (30, 2397677760)]

theorem pairMergeCheck12 : pairMerged12 = Integer.Sparse.merge pairMerged8 pairMerged11 := by decide +kernel

theorem pairMergedZero12 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged12 x = 0 := by
  rw [pairMergeCheck12, Integer.Sparse.eval_merge]
  rw [pairMergedZero8 x h, pairMergedZero11 x h]
  simp only [add_zero]

def pairMerged13 : Integer.Sparse (Fin 271) := [(0, -1686539584), (1, 26393763270), (2, -9222802470), (3, -48954134400), (4, -35572405920), (5, 6319438920), (6, -499592880), (7, -7432049280), (8, -11149517760), (12, -5320084320), (13, 7467779680), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1549683360), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 7155246240), (24, 13214767680), (25, 9605207520), (26, -12674317440), (27, -6533974620), (29, 11813217120), (30, 18622872000)]

theorem pairMergeCheck13 : pairMerged13 = Integer.Sparse.merge pairMerged5 pairMerged12 := by decide +kernel

theorem pairMergedZero13 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged13 x = 0 := by
  rw [pairMergeCheck13, Integer.Sparse.eval_merge]
  rw [pairMergedZero5 x h, pairMergedZero12 x h]
  simp only [add_zero]

def pairMerged14 : Integer.Sparse (Fin 271) := [(0, -109408634), (1, 1684676680), (2, -2029825900), (3, -9843319200), (4, -1933827360), (5, 2142154040), (6, -123585810), (7, -3954745920), (8, -3954745920), (12, -3911200320), (13, -2636497280), (17, 48988800), (23, -16329600), (27, 12247200), (28, 97977600), (29, -81648000), (34, -1318248640), (50, 5932118880), (51, -1977372960)]

theorem pairMergeCheck14 : pairMerged14 = Integer.Sparse.merge (Integer.Sparse.scale (272160) (rows 15)) (Integer.Sparse.scale (8239054) (rows 16)) := by decide +kernel

theorem pairMergedZero14 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged14 x = 0 := by
  rw [pairMergeCheck14, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged15 : Integer.Sparse (Fin 271) := [(0, 8099576), (1, -56641740), (2, 606072000), (3, 624640320), (4, -276472320), (5, -1541099280), (6, 177490980), (7, 831135360), (8, 1662270720), (12, -484685760), (13, -323123840), (26, -276472320), (34, 346449600), (51, 1662270720), (54, 1454057280)]

theorem pairMergeCheck15 : pairMerged15 = Integer.Sparse.merge (Integer.Sparse.scale (2019524) (rows 17)) (Integer.Sparse.scale (-10389192) (rows 18)) := by decide +kernel

theorem pairMergedZero15 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged15 x = 0 := by
  rw [pairMergeCheck15, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged16 : Integer.Sparse (Fin 271) := [(0, -101309058), (1, 1628034940), (2, -1423753900), (3, -9218678880), (4, -2210299680), (5, 601054760), (6, 53905170), (7, -3123610560), (8, -2292475200), (12, -4395886080), (13, -2959621120), (17, 48988800), (23, -16329600), (26, -276472320), (27, 12247200), (28, 97977600), (29, -81648000), (34, -971799040), (50, 5932118880), (51, -315102240), (54, 1454057280)]

theorem pairMergeCheck16 : pairMerged16 = Integer.Sparse.merge pairMerged14 pairMerged15 := by decide +kernel

theorem pairMergedZero16 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged16 x = 0 := by
  rw [pairMergeCheck16, Integer.Sparse.eval_merge]
  rw [pairMergedZero14 x h, pairMergedZero15 x h]
  simp only [add_zero]

def pairMerged17 : Integer.Sparse (Fin 271) := [(0, 440260440), (1, -9120956850), (2, 3598850490), (3, 34429673760), (4, 10265991360), (5, -7146635880), (6, 771328020), (7, 8709548640), (8, 9228362880), (12, 2075256960), (13, 6744585120), (26, 10265991360), (34, 5324316000), (51, 2075256960), (53, -1556442720), (55, -3112885440)]

theorem pairMergeCheck17 : pairMerged17 = Integer.Sparse.merge (Integer.Sparse.scale (-32425890) (rows 19)) (Integer.Sparse.scale (-34128060) (rows 20)) := by decide +kernel

theorem pairMergedZero17 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged17 x = 0 := by
  rw [pairMergeCheck17, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged18 : Integer.Sparse (Fin 271) := [(0, -32241928), (1, 1069918200), (2, -85892640), (3, -7259368320), (5, 78413040), (7, -1254608640), (12, -3943336320), (13, -7379041920), (23, 2822869440), (25, 2822869440), (31, -458094080), (34, -627304320), (53, 1881912960)]

theorem pairMergeCheck18 : pairMerged18 = Integer.Sparse.merge (Integer.Sparse.scale (7841304) (rows 21)) (Integer.Sparse.scale (5726176) (rows 22)) := by decide +kernel

theorem pairMergedZero18 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged18 x = 0 := by
  rw [pairMergeCheck18, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged19 : Integer.Sparse (Fin 271) := [(0, 408018512), (1, -8051038650), (2, 3512957850), (3, 27170305440), (4, 10265991360), (5, -7068222840), (6, 771328020), (7, 7454940000), (8, 9228362880), (12, -1868079360), (13, -634456800), (23, 2822869440), (25, 2822869440), (26, 10265991360), (31, -458094080), (34, 4697011680), (51, 2075256960), (53, 325470240), (55, -3112885440)]

theorem pairMergeCheck19 : pairMerged19 = Integer.Sparse.merge pairMerged17 pairMerged18 := by decide +kernel

theorem pairMergedZero19 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged19 x = 0 := by
  rw [pairMergeCheck19, Integer.Sparse.eval_merge]
  rw [pairMergedZero17 x h, pairMergedZero18 x h]
  simp only [add_zero]

def pairMerged20 : Integer.Sparse (Fin 271) := [(0, 306709454), (1, -6423003710), (2, 2089203950), (3, 17951626560), (4, 8055691680), (5, -6467168080), (6, 825233190), (7, 4331329440), (8, 6935887680), (12, -6263965440), (13, -3594077920), (17, 48988800), (23, 2806539840), (25, 2822869440), (26, 9989519040), (27, 12247200), (28, 97977600), (29, -81648000), (31, -458094080), (34, 3725212640), (50, 5932118880), (51, 1760154720), (53, 325470240), (54, 1454057280), (55, -3112885440)]

theorem pairMergeCheck20 : pairMerged20 = Integer.Sparse.merge pairMerged16 pairMerged19 := by decide +kernel

theorem pairMergedZero20 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged20 x = 0 := by
  rw [pairMergeCheck20, Integer.Sparse.eval_merge]
  rw [pairMergedZero16 x h, pairMergedZero19 x h]
  simp only [add_zero]

def pairMerged21 : Integer.Sparse (Fin 271) := [(0, 564230340), (1, -9199501680), (2, 2247190020), (3, 22750199040), (4, 14786640000), (12, 6329693280), (13, 1348746240), (25, -6381760320), (26, 4487559360), (30, -12763520640), (32, -7393320000), (33, 674373120)]

theorem pairMergeCheck21 : pairMerged21 = Integer.Sparse.merge (Integer.Sparse.scale (-8429664) (rows 23)) (Integer.Sparse.scale (-26590668) (rows 24)) := by decide +kernel

theorem pairMergedZero21 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged21 x = 0 := by
  rw [pairMergeCheck21, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged22 : Integer.Sparse (Fin 271) := [(0, 1067875890), (1, -13625816460), (2, 4109578350), (3, 34682576640), (4, 22843653120), (5, -104274240), (7, 104274240), (8, 417096960), (12, 14764377600), (13, 3534683040), (23, -312822720), (25, -7887143520), (27, 234617040), (29, -625645440), (30, -18804015360), (32, -6685102080), (44, 1876936320), (49, 4544592480), (50, -625645440), (53, -312822720)]

theorem pairMergeCheck22 : pairMerged22 = Integer.Sparse.merge (Integer.Sparse.scale (6311934) (rows 25)) (Integer.Sparse.scale (1303428) (rows 26)) := by decide +kernel

theorem pairMergedZero22 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged22 x = 0 := by
  rw [pairMergeCheck22, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged23 : Integer.Sparse (Fin 271) := [(0, 1632106230), (1, -22825318140), (2, 6356768370), (3, 57432775680), (4, 37630293120), (5, -104274240), (7, 104274240), (8, 417096960), (12, 21094070880), (13, 4883429280), (23, -312822720), (25, -14268903840), (26, 4487559360), (27, 234617040), (29, -625645440), (30, -31567536000), (32, -14078422080), (33, 674373120), (44, 1876936320), (49, 4544592480), (50, -625645440), (53, -312822720)]

theorem pairMergeCheck23 : pairMerged23 = Integer.Sparse.merge pairMerged21 pairMerged22 := by decide +kernel

theorem pairMergedZero23 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged23 x = 0 := by
  rw [pairMergeCheck23, Integer.Sparse.eval_merge]
  rw [pairMergedZero21 x h, pairMergedZero22 x h]
  simp only [add_zero]

def pairMerged24 : Integer.Sparse (Fin 271) := [(0, -127417782), (1, 1285084380), (2, -492829650), (3, -2986179840), (4, -982462080), (12, -1897068480), (13, -396219840), (25, -548763840), (26, 350653920), (30, 1119817440), (32, 2377319040), (42, -479921760), (43, 1303067520), (44, -2262911040), (45, 1303067520)]

theorem pairMergeCheck24 : pairMerged24 = Integer.Sparse.merge (Integer.Sparse.scale (-12381870) (rows 27)) (Integer.Sparse.scale (1809816) (rows 28)) := by decide +kernel

theorem pairMergedZero24 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged24 x = 0 := by
  rw [pairMergeCheck24, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged25 : Integer.Sparse (Fin 271) := [(0, 43175808), (1, -967939200), (2, 190252800), (3, 1811773440), (4, 1253836800), (5, 414720), (7, -552960), (8, -1105920), (12, 555171840), (13, 562913280), (23, 3317760), (24, 9953280), (25, 2119219200), (27, -4147200), (29, 6635520), (30, 860958720), (32, 1695375360), (46, 1266554880), (47, -1271531520), (48, -9953280), (50, 4976640), (54, 3317760)]

theorem pairMergeCheck25 : pairMerged25 = Integer.Sparse.merge (Integer.Sparse.scale (-3532032) (rows 29)) (Integer.Sparse.scale (1759104) (rows 30)) := by decide +kernel

theorem pairMergedZero25 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged25 x = 0 := by
  rw [pairMergeCheck25, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged26 : Integer.Sparse (Fin 271) := [(0, -84241974), (1, 317145180), (2, -302576850), (3, -1174406400), (4, 271374720), (5, 414720), (7, -552960), (8, -1105920), (12, -1341896640), (13, 166693440), (23, 3317760), (24, 9953280), (25, 1570455360), (26, 350653920), (27, -4147200), (29, 6635520), (30, 1980776160), (32, 4072694400), (42, -479921760), (43, 1303067520), (44, -2262911040), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (50, 4976640), (54, 3317760)]

theorem pairMergeCheck26 : pairMerged26 = Integer.Sparse.merge pairMerged24 pairMerged25 := by decide +kernel

theorem pairMergedZero26 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged26 x = 0 := by
  rw [pairMergeCheck26, Integer.Sparse.eval_merge]
  rw [pairMergedZero24 x h, pairMergedZero25 x h]
  simp only [add_zero]

def pairMerged27 : Integer.Sparse (Fin 271) := [(0, 1547864256), (1, -22508172960), (2, 6054191520), (3, 56258369280), (4, 37901667840), (5, -103859520), (7, 103721280), (8, 415991040), (12, 19752174240), (13, 5050122720), (23, -309504960), (24, 9953280), (25, -12698448480), (26, 4838213280), (27, 230469840), (29, -619009920), (30, -29586759840), (32, -10005727680), (33, 674373120), (42, -479921760), (43, 1303067520), (44, -385974720), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (49, 4544592480), (50, -620668800), (53, -312822720), (54, 3317760)]

theorem pairMergeCheck27 : pairMerged27 = Integer.Sparse.merge pairMerged23 pairMerged26 := by decide +kernel

theorem pairMergedZero27 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged27 x = 0 := by
  rw [pairMergeCheck27, Integer.Sparse.eval_merge]
  rw [pairMergedZero23 x h, pairMergedZero26 x h]
  simp only [add_zero]

def pairMerged28 : Integer.Sparse (Fin 271) := [(0, 1854573710), (1, -28931176670), (2, 8143395470), (3, 74209995840), (4, 45957359520), (5, -6571027600), (6, 825233190), (7, 4435050720), (8, 7351878720), (12, 13488208800), (13, 1456044800), (17, 48988800), (23, 2497034880), (24, 9953280), (25, -9875579040), (26, 14827732320), (27, 242717040), (28, 97977600), (29, -700657920), (30, -29586759840), (31, -458094080), (32, -10005727680), (33, 674373120), (34, 3725212640), (42, -479921760), (43, 1303067520), (44, -385974720), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (49, 4544592480), (50, 5311450080), (51, 1760154720), (53, 12647520), (54, 1457375040), (55, -3112885440)]

theorem pairMergeCheck28 : pairMerged28 = Integer.Sparse.merge pairMerged20 pairMerged27 := by decide +kernel

theorem pairMergedZero28 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged28 x = 0 := by
  rw [pairMergeCheck28, Integer.Sparse.eval_merge]
  rw [pairMergedZero20 x h, pairMergedZero27 x h]
  simp only [add_zero]

def pairMerged29 : Integer.Sparse (Fin 271) := [(0, 168034126), (1, -2537413400), (2, -1079407000), (3, 25255861440), (4, 10384953600), (5, -251588680), (6, 325640310), (7, -2996998560), (8, -3797639040), (12, 8168124480), (13, 8923824480), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1500694560), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 9652281120), (24, 13224720960), (25, -270371520), (26, 2153414880), (27, -6291257580), (28, 97977600), (29, 11112559200), (30, -10963887840), (31, -458094080), (32, -10005727680), (33, 674373120), (34, 3725212640), (42, -479921760), (43, 1303067520), (44, -385974720), (45, 1303067520), (46, 1266554880), (47, -1271531520), (48, -9953280), (49, 4544592480), (50, 5311450080), (51, 1760154720), (53, 12647520), (54, 1457375040), (55, -3112885440)]

theorem pairMergeCheck29 : pairMerged29 = Integer.Sparse.merge pairMerged13 pairMerged28 := by decide +kernel

theorem pairMergedZero29 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged29 x = 0 := by
  rw [pairMergeCheck29, Integer.Sparse.eval_merge]
  rw [pairMergedZero13 x h, pairMergedZero28 x h]
  simp only [add_zero]

def pairMerged30 : Integer.Sparse (Fin 271) := [(0, -701544198), (1, 8476671000), (2, -3863485110), (3, -22859176320), (4, -14654783040), (5, 1055258640), (7, -2229355200), (8, -3225194880), (12, -5595956160), (23, -713027520), (24, 5262010560), (26, -1872841440), (27, -1884125520), (29, 2274491520), (30, 9319070880), (42, 1069541280), (44, -5550819840), (45, -5550819840), (50, 7401093120), (54, -713027520), (55, 3700546560)]

theorem pairMergeCheck30 : pairMerged30 = Integer.Sparse.merge (Integer.Sparse.scale (1485474) (rows 31)) (Integer.Sparse.scale (-15418944) (rows 32)) := by decide +kernel

theorem pairMergedZero30 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged30 x = 0 := by
  rw [pairMergeCheck30, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged31 : Integer.Sparse (Fin 271) := [(0, -8391918), (1, 263935950), (2, -416033880), (3, -1494318240), (4, -469992960), (5, 174024480), (7, -183816000), (8, -656931840), (12, -2884320), (13, 497383200), (23, 216974880), (25, 36043200), (26, -313328640), (27, -162731160), (29, 433949760), (30, 469992960), (32, 1337892480), (35, -650924640), (37, 298429920), (38, -704989440), (39, -1301849280), (50, 867899520), (53, 786444480), (54, 650924640)]

theorem pairMergeCheck31 : pairMerged31 = Integer.Sparse.merge (Integer.Sparse.scale (414486) (rows 33)) (Integer.Sparse.scale (-4520310) (rows 34)) := by decide +kernel

theorem pairMergedZero31 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged31 x = 0 := by
  rw [pairMergeCheck31, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
