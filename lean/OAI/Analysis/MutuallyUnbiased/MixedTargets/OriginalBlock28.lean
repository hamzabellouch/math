import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock28 : Integer.Sparse (Fin 2886) := [(896, 20355807360), (897, -26140056960), (898, 59646838080), (899, 3684537600), (900, 24438657600), (901, 90786548160), (902, 72717328320), (903, 12656995200), (904, -53105987520), (905, -24436592640), (906, -16494482880), (907, -4854971520), (908, 22442110560), (909, -44920608000), (910, -46013337600), (911, 37131510240), (912, -24425581920), (913, -30122788320), (914, -34914424320), (915, -15924055680), (916, 17303277120), (917, 84184678080), (918, -25105542720), (919, 10095405120), (920, -21429406080), (921, -26705880000), (922, -7207872000), (923, -2290443840), (924, 19270920960), (925, 15924055680), (926, -44733043200), (927, -20190810240)]

def originalBlock28 : Integer.Sparse OriginalKey := [(Sum.inl 2247, -174572121600), (Sum.inl 2967, -223665216000), (Sum.inl 3029, -224603040000), (Sum.inl 3030, -230066688000), (Sum.inl 3031, 122193288000), (Sum.inl 3036, 185657551200), (Sum.inl 3037, -122127909600), (Sum.inl 3038, 453932740800), (Sum.inl 3039, 363586641600), (Sum.inl 3040, 63284976000), (Sum.inl 3043, -150613941600), (Sum.inl 3044, -265529937600), (Sum.inl 3045, -122182963200), (Sum.inl 3050, -82472414400), (Sum.inl 3051, -24274857600), (Sum.inl 3052, 101779036800), (Sum.inl 3053, 112210552800), (Sum.inl 3054, -130700284800), (Sum.inl 3055, 298234190400), (Sum.inl 3056, 18422688000), (Sum.inl 3064, 50477025600), (Sum.inl 3066, -107147030400), (Sum.inl 3068, -133529400000), (Sum.inl 3069, -36039360000), (Sum.inl 3073, -11452219200), (Sum.inl 3074, 96354604800), (Sum.inl 3075, -79620278400), (Sum.inl 3077, 86516385600), (Sum.inl 3078, 420923390400), (Sum.inl 3079, -125527713600), (Sum.inl 3086, -100954051200), (Sum.inl 3098, 79620278400)]

theorem originalBlockCheck28 : originalBlock28 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock28 keyMomentRows) := by decide +kernel

theorem originalBlockEval28 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock28 x =
      Integer.Sparse.eval keyPolynomialBlock28 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck28, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
