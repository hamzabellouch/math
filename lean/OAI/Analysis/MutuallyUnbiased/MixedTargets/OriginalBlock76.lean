import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock76 : Integer.Sparse (Fin 2886) := [(2432, -74677500000), (2433, 39902572800), (2434, 277266644640), (2435, 145494670080), (2436, -104137225920), (2437, 4560264960), (2438, -143659440000), (2439, 7336967200), (2440, -170220652800), (2441, 24549885760), (2442, -173815992000), (2443, -68900767200), (2444, 5158261120), (2445, 128688370560), (2446, 142548077280), (2447, -251085086160), (2448, 75397542720), (2449, -213667645200), (2450, -92685692160), (2451, 88699461120), (2452, 11700642624), (2453, 26420478720), (2454, 36378677920), (2455, 19932687520), (2456, -50386334880), (2457, -170767914240), (2458, -9318353280), (2459, -11069268480), (2460, 32751053760), (2461, -138298757760), (2462, -41795249280), (2463, 156207899520)]

def originalBlock76 : Integer.Sparse OriginalKey := [(Sum.inl 2708, 26420478720), (Sum.inl 2728, 32751053760), (Sum.inl 2729, 75397542720), (Sum.inl 2735, -41795249280), (Sum.inl 2750, 39902572800), (Sum.inl 2763, -170220652800), (Sum.inl 2781, -104137225920), (Sum.inl 3085, -170767914240), (Sum.inl 3086, 128688370560), (Sum.inl 3097, -138298757760), (Sum.inl 3119, 145494670080), (Sum.inl 3225, 5158261120), (Sum.inl 3227, -50386334880), (Sum.inl 3540, 7336967200), (Sum.inl 3572, -143659440000), (Sum.inl 3834, 11700642624), (Sum.inl 3840, -74677500000), (Sum.inl 3848, -68900767200), (Sum.inl 3866, 88699461120), (Sum.inl 3871, 36378677920), (Sum.inl 3872, -213667645200), (Sum.inl 3880, -92685692160), (Sum.inl 3881, -251085086160), (Sum.inl 3882, 19932687520), (Sum.inl 3883, 142548077280), (Sum.inl 3972, 156207899520), (Sum.inl 3976, -11069268480), (Sum.inl 3977, -9318353280), (Sum.inl 3978, -173815992000), (Sum.inl 3993, 4560264960), (Sum.inl 3994, 277266644640), (Sum.inl 3997, 24549885760), (Sum.inl 4888, -201545339520), (Sum.inl 4896, 20633044480), (Sum.inl 5173, -167180997120), (Sum.inl 5249, 105681914880), (Sum.inl 5256, -683071656960), (Sum.inl 5260, 544101351040), (Sum.inl 5263, 131004215040), (Sum.inl 5264, 301590170880), (Sum.inl 5281, 159610291200), (Sum.inl 5289, -1808715402240), (Sum.inl 5295, -416548903680), (Sum.inl 5304, 581978680320), (Sum.inl 5381, 46802570496), (Sum.inl 5382, 354797844480), (Sum.inl 5405, -37273413120), (Sum.inl 5411, 570192309120), (Sum.inl 5425, -1153380580800), (Sum.inl 5430, 494743240960), (Sum.inl 5438, 18241059840), (Sum.inl 5445, -370742768640), (Sum.inl 5446, -1004340344640), (Sum.inl 5447, 79730750080), (Sum.inl 5471, -44277073920), (Sum.inl 5478, 1109066578560), (Sum.inl 5480, -695263968000), (Sum.inl 5484, 98199543040)]

theorem originalBlockCheck76 : originalBlock76 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock76 keyMomentRows) := by decide +kernel

theorem originalBlockEval76 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock76 x =
      Integer.Sparse.eval keyPolynomialBlock76 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck76, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
