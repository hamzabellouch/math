import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock77 : Integer.Sparse (Fin 2886) := [(2464, 59625673920), (2465, 80569291200), (2466, 90415507200), (2467, -222656215200), (2468, -35817134400), (2469, -37074625440), (2470, -73256630440), (2471, -15029351280), (2472, -28075223520), (2473, 6312192000), (2474, -333860876800), (2475, 39902572800), (2476, -1174422320), (2477, 171721161200), (2478, 71754163680), (2479, 96987695040), (2480, -31543610640), (2481, 40201116000), (2482, 251942575840), (2483, 101673310000), (2484, 90525826320), (2485, -20456109360), (2486, 6909342320), (2487, 56990279280), (2488, -25002267840), (2489, -22594677120), (2490, -222331042080), (2491, 17151888960), (2492, -96987695040), (2493, 57327463280), (2494, -4970178000), (2495, 1800137360)]

def originalBlock77 : Integer.Sparse OriginalKey := [(Sum.inl 2718, 90415507200), (Sum.inl 2719, 6312192000), (Sum.inl 2736, 39902572800), (Sum.inl 2737, -37074625440), (Sum.inl 3098, -35817134400), (Sum.inl 3289, -1174422320), (Sum.inl 3294, 1800137360), (Sum.inl 3296, -28075223520), (Sum.inl 3303, -15029351280), (Sum.inl 3306, -4970178000), (Sum.inl 3517, 80569291200), (Sum.inl 3557, -31543610640), (Sum.inl 3558, 231346835120), (Sum.inl 3565, 17151888960), (Sum.inl 3571, 71754163680), (Sum.inl 3572, -333860876800), (Sum.inl 3573, -73256630440), (Sum.inl 3584, 57327463280), (Sum.inl 3832, -20456109360), (Sum.inl 3842, 40201116000), (Sum.inl 3868, 90525826320), (Sum.inl 3869, -15685334800), (Sum.inl 3874, 56990279280), (Sum.inl 3877, 251942575840), (Sum.inl 3884, 101673310000), (Sum.inl 3954, -25002267840), (Sum.inl 3955, -96987695040), (Sum.inl 3959, -222331042080), (Sum.inl 3973, 96987695040), (Sum.inl 3978, -222656215200), (Sum.inl 4599, -4697689280), (Sum.inl 4603, 7200549440), (Sum.inl 4607, -112300894080), (Sum.inl 4616, -60117405120), (Sum.inl 4617, -148298501760), (Sum.inl 4620, -19880712000), (Sum.inl 5138, 322277164800), (Sum.inl 5144, -126174442560), (Sum.inl 5160, 925387340480), (Sum.inl 5161, 25248768000), (Sum.inl 5164, 68607555840), (Sum.inl 5255, 361662028800), (Sum.inl 5269, 159610291200), (Sum.inl 5281, 287016654720), (Sum.inl 5289, -1335443507200), (Sum.inl 5295, -143268537600), (Sum.inl 5299, -293026521760), (Sum.inl 5300, 229309853120), (Sum.inl 5379, -81824437440), (Sum.inl 5385, 362103305280), (Sum.inl 5414, -62741339200), (Sum.inl 5419, 160804464000), (Sum.inl 5429, 127952045760), (Sum.inl 5436, 1007770303360), (Sum.inl 5446, -482630928320), (Sum.inl 5461, 387950780160), (Sum.inl 5470, -387950780160), (Sum.inl 5480, -890624860800)]

theorem originalBlockCheck77 : originalBlock77 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock77 keyMomentRows) := by decide +kernel

theorem originalBlockEval77 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock77 x =
      Integer.Sparse.eval keyPolynomialBlock77 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck77, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
