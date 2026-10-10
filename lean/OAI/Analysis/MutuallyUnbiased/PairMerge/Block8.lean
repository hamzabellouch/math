import OAI.Analysis.MutuallyUnbiased.Certificate.IntegerMerge
import OAI.Analysis.MutuallyUnbiased.PairData.Data
import OAI.Analysis.MutuallyUnbiased.PairMerge.Block7

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged256 : Integer.Sparse (Fin 271) := [(0, -92782368), (1, 1923477570), (2, 11440170), (3, -5430741120), (4, -4707218880), (12, -723522240), (13, 3621935520), (25, 2987772480), (26, -3983696640)]

theorem pairMergeCheck256 : pairMerged256 = Integer.Sparse.merge (Integer.Sparse.scale (-45274194) (rows 4)) (Integer.Sparse.scale (24898104) (rows 5)) := by decide +kernel

theorem pairMergedZero256 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged256 x = 0 := by
  rw [pairMergeCheck256, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged257 : Integer.Sparse (Fin 271) := [(0, -343196784), (1, 7627361490), (2, -3049180470), (3, -9882552960), (4, -9159030720), (5, 834714720), (7, -1112952960), (8, -5564764800), (12, -723522240), (13, 3621935520), (24, 3338858880), (25, 2987772480), (26, -3983696640), (29, 6677717760)]

theorem pairMergeCheck257 : pairMerged257 = Integer.Sparse.merge (Integer.Sparse.scale (27823824) (rows 3)) pairMerged256 := by decide +kernel

theorem pairMergedZero257 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged257 x = 0 := by
  rw [pairMergeCheck257, Integer.Sparse.eval_merge]
  rw [pairMergedZero256 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged258 : Integer.Sparse (Fin 271) := [(0, -750087324), (1, 3091618530), (2, -3314574270), (3, -18696303360), (4, -6875305920), (5, 3875445000), (6, -302313060), (7, -4431490560), (8, -7224033600), (12, -3471128640), (13, 3621935520), (23, 2488903200), (24, 8316665280), (25, 2987772480), (26, -3983696640), (27, -3627756720), (29, 6677717760)]

theorem pairMergeCheck258 : pairMerged258 = Integer.Sparse.merge pairMerged255 pairMerged257 := by decide +kernel

theorem pairMergedZero258 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged258 x = 0 := by
  rw [pairMergeCheck258, Integer.Sparse.eval_merge]
  rw [pairMergedZero255 x h, pairMergedZero257 x h]
  simp only [add_zero]

def pairMerged259 : Integer.Sparse (Fin 271) := [(0, -392917392), (1, 4477939200), (2, -840929040), (3, -4887267840), (4, -6766986240), (12, -1879718400), (14, -770757120), (15, -1691746560), (17, -3083028480), (20, -3383493120), (23, 2619267840), (24, 1691746560), (25, 5238535680), (27, -808315200), (29, 2155507200), (30, 6366366720)]

theorem pairMergeCheck259 : pairMerged259 = Integer.Sparse.merge (Integer.Sparse.scale (-42819840) (rows 7)) (Integer.Sparse.scale (-2349648) (rows 8)) := by decide +kernel

theorem pairMergedZero259 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged259 x = 0 := by
  rw [pairMergeCheck259, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged260 : Integer.Sparse (Fin 271) := [(0, -946123416), (1, 23840150040), (2, -5143642560), (3, -34391589120), (4, -31353920640), (12, -6797105280), (14, -770757120), (15, -1691746560), (17, -3083028480), (20, -3383493120), (23, 2619267840), (24, 1691746560), (25, 5238535680), (26, -4917386880), (27, -808315200), (29, 2155507200), (30, 21118527360)]

theorem pairMergeCheck260 : pairMerged260 = Integer.Sparse.merge (Integer.Sparse.scale (61467336) (rows 6)) pairMerged259 := by decide +kernel

theorem pairMergedZero260 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged260 x = 0 := by
  rw [pairMergeCheck260, Integer.Sparse.eval_merge]
  rw [pairMergedZero259 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged261 : Integer.Sparse (Fin 271) := [(0, -34203708), (1, -1622187000), (2, 387669240), (3, 3945957120), (4, 2550864960), (12, 1501960320), (16, 759734640), (17, 1519469280), (18, 400075200), (22, 800150400), (23, -1012979520), (27, 189933660), (29, -506489760)]

theorem pairMergeCheck261 : pairMerged261 = Integer.Sparse.merge (Integer.Sparse.scale (4220748) (rows 9)) (Integer.Sparse.scale (1111320) (rows 10)) := by decide +kernel

theorem pairMergedZero261 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged261 x = 0 := by
  rw [pairMergeCheck261, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged262 : Integer.Sparse (Fin 271) := [(0, -60555600), (1, 996786000), (2, -197089200), (3, -1614816000), (4, -1397088000), (12, -657720000), (15, -326592000), (17, -563371200), (19, -400075200), (20, -400075200), (22, -400075200), (23, 163296000), (24, 775656000), (25, 326592000), (27, -140842800), (29, 187790400), (30, 860025600)]

theorem pairMergeCheck262 : pairMerged262 = Integer.Sparse.merge (Integer.Sparse.scale (-2268000) (rows 11)) (Integer.Sparse.scale (-11113200) (rows 12)) := by decide +kernel

theorem pairMergedZero262 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged262 x = 0 := by
  rw [pairMergeCheck262, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged263 : Integer.Sparse (Fin 271) := [(0, -94759308), (1, -625401000), (2, 190580040), (3, 2331141120), (4, 1153776960), (12, 844240320), (15, -326592000), (16, 759734640), (17, 956098080), (18, 400075200), (19, -400075200), (20, -400075200), (22, 400075200), (23, -849683520), (24, 775656000), (25, 326592000), (27, 49090860), (29, -318699360), (30, 860025600)]

theorem pairMergeCheck263 : pairMerged263 = Integer.Sparse.merge pairMerged261 pairMerged262 := by decide +kernel

theorem pairMergedZero263 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged263 x = 0 := by
  rw [pairMergeCheck263, Integer.Sparse.eval_merge]
  rw [pairMergedZero261 x h, pairMergedZero262 x h]
  simp only [add_zero]

def pairMerged264 : Integer.Sparse (Fin 271) := [(0, -1040882724), (1, 23214749040), (2, -4953062520), (3, -32060448000), (4, -30200143680), (12, -5952864960), (14, -770757120), (15, -2018338560), (16, 759734640), (17, -2126930400), (18, 400075200), (19, -400075200), (20, -3783568320), (22, 400075200), (23, 1769584320), (24, 2467402560), (25, 5565127680), (26, -4917386880), (27, -759224340), (29, 1836807840), (30, 21978552960)]

theorem pairMergeCheck264 : pairMerged264 = Integer.Sparse.merge pairMerged260 pairMerged263 := by decide +kernel

theorem pairMergedZero264 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged264 x = 0 := by
  rw [pairMergeCheck264, Integer.Sparse.eval_merge]
  rw [pairMergedZero260 x h, pairMergedZero263 x h]
  simp only [add_zero]

def pairMerged265 : Integer.Sparse (Fin 271) := [(0, -1790970048), (1, 26306367570), (2, -8267636790), (3, -50756751360), (4, -37075449600), (5, 3875445000), (6, -302313060), (7, -4431490560), (8, -7224033600), (12, -9423993600), (13, 3621935520), (14, -770757120), (15, -2018338560), (16, 759734640), (17, -2126930400), (18, 400075200), (19, -400075200), (20, -3783568320), (22, 400075200), (23, 4258487520), (24, 10784067840), (25, 8552900160), (26, -8901083520), (27, -4386981060), (29, 8514525600), (30, 21978552960)]

theorem pairMergeCheck265 : pairMerged265 = Integer.Sparse.merge pairMerged258 pairMerged264 := by decide +kernel

theorem pairMergedZero265 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged265 x = 0 := by
  rw [pairMergeCheck265, Integer.Sparse.eval_merge]
  rw [pairMergedZero258 x h, pairMergedZero264 x h]
  simp only [add_zero]

def pairMerged266 : Integer.Sparse (Fin 271) := [(0, 83516832), (1, -2141865180), (2, 445514580), (3, 6181297920), (4, 3879640800), (12, 2345202720), (17, 48988800), (18, 2301657120), (23, -16329600), (25, -1534438080), (27, 12247200), (28, 97977600), (29, -81648000), (30, -1534438080)]

theorem pairMergeCheck266 : pairMerged266 = Integer.Sparse.merge (Integer.Sparse.scale (6393492) (rows 14)) (Integer.Sparse.scale (272160) (rows 15)) := by decide +kernel

theorem pairMergedZero266 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged266 x = 0 := by
  rw [pairMergeCheck266, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged267 : Integer.Sparse (Fin 271) := [(0, 31840452), (1, -1188908280), (2, 328825980), (3, 4580997120), (4, 2546056800), (12, 1500599520), (17, 48988800), (18, 2301657120), (21, -400075200), (22, -400075200), (23, -16329600), (25, -1534438080), (27, 12247200), (28, 97977600), (29, -81648000), (30, -1267721280)]

theorem pairMergeCheck267 : pairMerged267 = Integer.Sparse.merge (Integer.Sparse.scale (-555660) (rows 13)) pairMerged266 := by decide +kernel

theorem pairMergedZero267 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged267 x = 0 := by
  rw [pairMergeCheck267, Integer.Sparse.eval_merge]
  rw [pairMergedZero266 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged268 : Integer.Sparse (Fin 271) := [(0, -30607038), (1, 643949460), (2, -1544617620), (3, -5032329120), (4, -334666080), (5, 1609455960), (6, -78172290), (7, -3112240320), (8, -3112240320), (12, -2806876800), (13, -1871251200), (26, 1221454080), (34, -732049920), (50, 4668360480), (51, -1556120160), (54, -916090560)]

theorem pairMergeCheck268 : pairMerged268 = Integer.Sparse.merge (Integer.Sparse.scale (6483834) (rows 16)) (Integer.Sparse.scale (-1272348) (rows 17)) := by decide +kernel

theorem pairMergedZero268 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged268 x = 0 := by
  rw [pairMergeCheck268, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged269 : Integer.Sparse (Fin 271) := [(0, 56443716), (1, -1476269550), (2, 345875670), (3, 7922486880), (4, 1734203520), (5, -1442788200), (6, 216775440), (7, 478548000), (8, 957096000), (12, 1554215040), (13, 5051198880), (26, 1734203520), (34, 2032763040), (51, 1734203520), (53, -1165661280), (55, -2331322560)]

theorem pairMergeCheck269 : pairMerged269 = Integer.Sparse.merge (Integer.Sparse.scale (-1124928) (rows 18)) (Integer.Sparse.scale (-24284610) (rows 19)) := by decide +kernel

theorem pairMergedZero269 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged269 x = 0 := by
  rw [pairMergeCheck269, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged270 : Integer.Sparse (Fin 271) := [(0, 25836678), (1, -832320090), (2, -1198741950), (3, 2890157760), (4, 1399537440), (5, 166667760), (6, 138603150), (7, -2633692320), (8, -2155144320), (12, -1252661760), (13, 3179947680), (26, 2955657600), (34, 1300713120), (50, 4668360480), (51, 178083360), (53, -1165661280), (54, -916090560), (55, -2331322560)]

theorem pairMergeCheck270 : pairMerged270 = Integer.Sparse.merge pairMerged268 pairMerged269 := by decide +kernel

theorem pairMergedZero270 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged270 x = 0 := by
  rw [pairMergeCheck270, Integer.Sparse.eval_merge]
  rw [pairMergedZero268 x h, pairMergedZero269 x h]
  simp only [add_zero]

def pairMerged271 : Integer.Sparse (Fin 271) := [(0, 57677130), (1, -2021228370), (2, -869915970), (3, 7471154880), (4, 3945594240), (5, 166667760), (6, 138603150), (7, -2633692320), (8, -2155144320), (12, 247937760), (13, 3179947680), (17, 48988800), (18, 2301657120), (21, -400075200), (22, -400075200), (23, -16329600), (25, -1534438080), (26, 2955657600), (27, 12247200), (28, 97977600), (29, -81648000), (30, -1267721280), (34, 1300713120), (50, 4668360480), (51, 178083360), (53, -1165661280), (54, -916090560), (55, -2331322560)]

theorem pairMergeCheck271 : pairMerged271 = Integer.Sparse.merge pairMerged267 pairMerged270 := by decide +kernel

theorem pairMergedZero271 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged271 x = 0 := by
  rw [pairMergeCheck271, Integer.Sparse.eval_merge]
  rw [pairMergedZero267 x h, pairMergedZero270 x h]
  simp only [add_zero]

def pairMerged272 : Integer.Sparse (Fin 271) := [(0, -18753336), (1, 664319880), (2, -52889760), (3, -4910129280), (5, 59285520), (7, -948568320), (12, -2692206720), (13, -4807797120), (23, 2134278720), (25, 2134278720), (31, -282078720), (34, -474284160), (53, 1422852480)]

theorem pairMergeCheck272 : pairMerged272 = Integer.Sparse.merge (Integer.Sparse.scale (5928552) (rows 21)) (Integer.Sparse.scale (3525984) (rows 22)) := by decide +kernel

theorem pairMergedZero272 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged272 x = 0 := by
  rw [pairMergeCheck272, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged273 : Integer.Sparse (Fin 271) := [(0, 184863924), (1, -3315472020), (2, 1705622940), (3, 8417545920), (4, 4442558400), (5, -2902420080), (6, 277659900), (7, 3493990080), (8, 4442558400), (12, -2692206720), (13, -4807797120), (23, 2134278720), (25, 2134278720), (26, 4442558400), (31, -282078720), (34, 1006568640), (53, 1422852480)]

theorem pairMergeCheck273 : pairMerged273 = Integer.Sparse.merge (Integer.Sparse.scale (-18510660) (rows 20)) pairMerged272 := by decide +kernel

theorem pairMergedZero273 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged273 x = 0 := by
  rw [pairMergeCheck273, Integer.Sparse.eval_merge]
  rw [pairMergedZero272 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged274 : Integer.Sparse (Fin 271) := [(0, 472385844), (1, -7550670960), (2, 1870997940), (3, 17096728320), (4, 12102410880), (12, 5096014560), (13, 426746880), (25, -5731145280), (26, 2657188800), (30, -11462290560), (32, -6051205440), (33, 213373440)]

theorem pairMergeCheck274 : pairMerged274 = Integer.Sparse.merge (Integer.Sparse.scale (-2667168) (rows 23)) (Integer.Sparse.scale (-23879772) (rows 24)) := by decide +kernel

theorem pairMergedZero274 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged274 x = 0 := by
  rw [pairMergeCheck274, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged275 : Integer.Sparse (Fin 271) := [(0, 767228112), (1, -10078164180), (2, 2801762460), (3, 26339826240), (4, 17681328000), (5, 45541440), (7, -45541440), (8, -182165760), (12, 11152391040), (13, 2856409920), (23, 136624320), (25, -5984254080), (27, -102468240), (29, 273248640), (30, -14416859520), (32, -4623454080), (44, -819745920), (49, 3672527040), (50, 273248640), (53, 136624320)]

theorem pairMergeCheck275 : pairMerged275 = Integer.Sparse.merge (Integer.Sparse.scale (5100732) (rows 25)) (Integer.Sparse.scale (-569268) (rows 26)) := by decide +kernel

theorem pairMergedZero275 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged275 x = 0 := by
  rw [pairMergeCheck275, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged276 : Integer.Sparse (Fin 271) := [(0, 1239613956), (1, -17628835140), (2, 4672760400), (3, 43436554560), (4, 29783738880), (5, 45541440), (7, -45541440), (8, -182165760), (12, 16248405600), (13, 3283156800), (23, 136624320), (25, -11715399360), (26, 2657188800), (27, -102468240), (29, 273248640), (30, -25879150080), (32, -10674659520), (33, 213373440), (44, -819745920), (49, 3672527040), (50, 273248640), (53, 136624320)]

theorem pairMergeCheck276 : pairMerged276 = Integer.Sparse.merge pairMerged274 pairMerged275 := by decide +kernel

theorem pairMergedZero276 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged276 x = 0 := by
  rw [pairMergeCheck276, Integer.Sparse.eval_merge]
  rw [pairMergedZero274 x h, pairMergedZero275 x h]
  simp only [add_zero]

def pairMerged277 : Integer.Sparse (Fin 271) := [(0, 1424477880), (1, -20944307160), (2, 6378383340), (3, 51854100480), (4, 34226297280), (5, -2856878640), (6, 277659900), (7, 3448448640), (8, 4260392640), (12, 13556198880), (13, -1524640320), (23, 2270903040), (25, -9581120640), (26, 7099747200), (27, -102468240), (29, 273248640), (30, -25879150080), (31, -282078720), (32, -10674659520), (33, 213373440), (34, 1006568640), (44, -819745920), (49, 3672527040), (50, 273248640), (53, 1559476800)]

theorem pairMergeCheck277 : pairMerged277 = Integer.Sparse.merge pairMerged273 pairMerged276 := by decide +kernel

theorem pairMergedZero277 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged277 x = 0 := by
  rw [pairMergeCheck277, Integer.Sparse.eval_merge]
  rw [pairMergedZero273 x h, pairMergedZero276 x h]
  simp only [add_zero]

def pairMerged278 : Integer.Sparse (Fin 271) := [(0, 1482155010), (1, -22965535530), (2, 5508467370), (3, 59325255360), (4, 38171891520), (5, -2690210880), (6, 416263050), (7, 814756320), (8, 2105248320), (12, 13804136640), (13, 1655307360), (17, 48988800), (18, 2301657120), (21, -400075200), (22, -400075200), (23, 2254573440), (25, -11115558720), (26, 10055404800), (27, -90221040), (28, 97977600), (29, 191600640), (30, -27146871360), (31, -282078720), (32, -10674659520), (33, 213373440), (34, 2307281760), (44, -819745920), (49, 3672527040), (50, 4941609120), (51, 178083360), (53, 393815520), (54, -916090560), (55, -2331322560)]

theorem pairMergeCheck278 : pairMerged278 = Integer.Sparse.merge pairMerged271 pairMerged277 := by decide +kernel

theorem pairMergedZero278 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged278 x = 0 := by
  rw [pairMergeCheck278, Integer.Sparse.eval_merge]
  rw [pairMergedZero271 x h, pairMergedZero277 x h]
  simp only [add_zero]

def pairMerged279 : Integer.Sparse (Fin 271) := [(0, -308815038), (1, 3340832040), (2, -2759169420), (3, 8568504000), (4, 1096441920), (5, 1185234120), (6, 113949990), (7, -3616734240), (8, -5118785280), (12, 4380143040), (13, 5277242880), (14, -770757120), (15, -2018338560), (16, 759734640), (17, -2077941600), (18, 2701732320), (19, -400075200), (20, -3783568320), (21, -400075200), (23, 6513060960), (24, 10784067840), (25, -2562658560), (26, 1154321280), (27, -4477202100), (28, 97977600), (29, 8706126240), (30, -5168318400), (31, -282078720), (32, -10674659520), (33, 213373440), (34, 2307281760), (44, -819745920), (49, 3672527040), (50, 4941609120), (51, 178083360), (53, 393815520), (54, -916090560), (55, -2331322560)]

theorem pairMergeCheck279 : pairMerged279 = Integer.Sparse.merge pairMerged265 pairMerged278 := by decide +kernel

theorem pairMergedZero279 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged279 x = 0 := by
  rw [pairMergeCheck279, Integer.Sparse.eval_merge]
  rw [pairMergedZero265 x h, pairMergedZero278 x h]
  simp only [add_zero]

def pairMerged280 : Integer.Sparse (Fin 271) := [(0, -145224576), (1, 1199363760), (2, -737871120), (3, -1027676160), (4, -1080656640), (5, 162207360), (7, -216276480), (8, -432552960), (12, -1238872320), (23, 1297658880), (24, 3892976640), (25, 1981324800), (26, 1262822400), (27, -1622073600), (29, 2595317760), (30, 4278355200), (32, 2595317760), (42, 947116800), (43, 947116800), (44, 947116800), (45, 947116800), (47, -1946488320), (48, -3892976640), (50, 1946488320), (54, 1297658880)]

theorem pairMergeCheck280 : pairMerged280 = Integer.Sparse.merge (Integer.Sparse.scale (1315440) (rows 28)) (Integer.Sparse.scale (-5406912) (rows 29)) := by decide +kernel

theorem pairMergedZero280 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged280 x = 0 := by
  rw [pairMergeCheck280, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged281 : Integer.Sparse (Fin 271) := [(0, -393020586), (1, 4053290220), (2, -1583795430), (3, -8683718400), (4, -5455537920), (5, 162207360), (7, -216276480), (8, -432552960), (12, -4246603200), (13, -273430080), (23, 1297658880), (24, 3892976640), (25, 2801615040), (26, 305817120), (27, -1622073600), (29, 2595317760), (30, 7149371040), (32, 4235898240), (42, -283318560), (43, 947116800), (44, -1513753920), (45, 947116800), (47, -1946488320), (48, -3892976640), (50, 1946488320), (54, 1297658880)]

theorem pairMergeCheck281 : pairMerged281 = Integer.Sparse.merge (Integer.Sparse.scale (-8544690) (rows 27)) pairMerged280 := by decide +kernel

theorem pairMergedZero281 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged281 x = 0 := by
  rw [pairMergeCheck281, Integer.Sparse.eval_merge]
  rw [pairMergedZero280 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged282 : Integer.Sparse (Fin 271) := [(0, -324300186), (1, 3931464600), (2, -1812852090), (3, -11079089280), (4, -7168512960), (5, 521322480), (7, -1172646720), (8, -1628968320), (12, -2639770560), (23, -780010560), (24, 1957919040), (26, -782641440), (27, -636718320), (29, 588954240), (30, 4496899680), (42, 1170015840), (44, -3223463040), (45, -3223463040), (50, 4297950720), (54, -780010560), (55, 2148975360)]

theorem pairMergeCheck282 : pairMerged282 = Integer.Sparse.merge (Integer.Sparse.scale (1625022) (rows 31)) (Integer.Sparse.scale (-8954064) (rows 32)) := by decide +kernel

theorem pairMergedZero282 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged282 x = 0 := by
  rw [pairMergeCheck282, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged283 : Integer.Sparse (Fin 271) := [(0, 56887110), (1, -840135240), (2, -244847610), (3, -1346647680), (4, -247665600), (5, 359115120), (7, -956370240), (8, -1196415360), (12, 1253206080), (13, 865105920), (23, -2077669440), (24, -1935057600), (26, -782641440), (27, 985355280), (29, -2006363520), (30, -693735840), (42, 1170015840), (44, -3223463040), (45, -3223463040), (46, 1946488320), (48, 3892976640), (50, 2351462400), (54, -2077669440), (55, 2148975360)]

theorem pairMergeCheck283 : pairMerged283 = Integer.Sparse.merge (Integer.Sparse.scale (2703456) (rows 30)) pairMerged282 := by decide +kernel

theorem pairMergedZero283 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged283 x = 0 := by
  rw [pairMergeCheck283, Integer.Sparse.eval_merge]
  rw [pairMergedZero282 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged284 : Integer.Sparse (Fin 271) := [(0, -336133476), (1, 3213154980), (2, -1828643040), (3, -10030366080), (4, -5703203520), (5, 521322480), (7, -1172646720), (8, -1628968320), (12, -2993397120), (13, 591675840), (23, -780010560), (24, 1957919040), (25, 2801615040), (26, -476824320), (27, -636718320), (29, 588954240), (30, 6455635200), (32, 4235898240), (42, 886697280), (43, 947116800), (44, -4737216960), (45, -2276346240), (46, 1946488320), (47, -1946488320), (50, 4297950720), (54, -780010560), (55, 2148975360)]

theorem pairMergeCheck284 : pairMerged284 = Integer.Sparse.merge pairMerged281 pairMerged283 := by decide +kernel

theorem pairMergedZero284 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged284 x = 0 := by
  rw [pairMergeCheck284, Integer.Sparse.eval_merge]
  rw [pairMergedZero281 x h, pairMergedZero283 x h]
  simp only [add_zero]

def pairMerged285 : Integer.Sparse (Fin 271) := [(0, 101640420), (1, -1560049470), (2, 630555030), (3, 5003117280), (4, 719591040), (5, -185091480), (7, 179897760), (8, 761140800), (12, 2055352320), (13, 2664446400), (23, -301008960), (25, 124649280), (26, 318245760), (27, 225756720), (29, -602017920), (30, 249298560), (32, 498597120), (35, -186973920), (37, 1090000800), (38, -373947840), (39, 1806053760), (50, -1204035840), (53, -415044000), (54, -903026880)]

theorem pairMergeCheck285 : pairMerged285 = Integer.Sparse.merge (Integer.Sparse.scale (-1298430) (rows 34)) (Integer.Sparse.scale (3027780) (rows 36)) := by decide +kernel

theorem pairMergedZero285 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged285 x = 0 := by
  rw [pairMergeCheck285, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged286 : Integer.Sparse (Fin 271) := [(0, 197448678), (1, -3004323210), (2, 895100220), (3, 9579034080), (4, 2092366080), (5, -270889920), (7, 294295680), (8, 989936640), (12, 3542525280), (13, 4380415200), (23, -301008960), (25, -1248125760), (26, 1233429120), (27, 225756720), (29, -602017920), (30, -1123476480), (32, -874177920), (35, -186973920), (37, 2119582080), (38, 1685214720), (39, 1806053760), (50, -1204035840), (53, -1444625280), (54, -903026880)]

theorem pairMergeCheck286 : pairMerged286 = Integer.Sparse.merge (Integer.Sparse.scale (1429974) (rows 33)) pairMerged285 := by decide +kernel

theorem pairMergedZero286 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged286 x = 0 := by
  rw [pairMergeCheck286, Integer.Sparse.eval_merge]
  rw [pairMergedZero285 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

def pairMerged287 : Integer.Sparse (Fin 271) := [(0, 134016120), (1, -2681921340), (2, 1234801260), (3, 10821444480), (4, 4342766400), (5, -491339520), (7, 982679040), (8, 1474018560), (12, 2356542720), (13, 1848510720), (24, -1474018560), (26, 2673155520), (27, 552756960), (29, -737009280), (30, -1423941120), (32, -2897959680), (36, 2211027840), (38, 2211027840), (39, 2211027840), (40, -37558080), (41, 2135911680), (50, -2948037120), (54, -2211027840), (55, -1474018560)]

theorem pairMergeCheck287 : pairMerged287 = Integer.Sparse.merge (Integer.Sparse.scale (-260820) (rows 37)) (Integer.Sparse.scale (15354360) (rows 39)) := by decide +kernel

theorem pairMergedZero287 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged287 x = 0 := by
  rw [pairMergeCheck287, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
