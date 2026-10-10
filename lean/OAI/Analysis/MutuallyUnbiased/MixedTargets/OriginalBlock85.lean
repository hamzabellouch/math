import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock85 : Integer.Sparse (Fin 2886) := [(2720, -123152322240), (2721, 61981314480), (2722, -48784844320), (2723, 2248083000), (2724, 59248431360), (2725, 617189760), (2726, 13467990040), (2727, 102678513360), (2728, 41470746960), (2729, 19791401920), (2730, -96553292760), (2731, -19207074240), (2732, 39601068160), (2733, 83076659520), (2734, -17253001680), (2735, 11730552000), (2736, -50180808480), (2737, -79464541920), (2738, -44732773560), (2739, -53078305800), (2740, -18203620320), (2741, -9899351640), (2742, 8815051200), (2743, -33818861040), (2744, 1090620480), (2745, -13949930640), (2746, 307527960), (2747, 33430043680), (2748, 42334134120), (2749, 21662031480), (2750, 4532419840), (2751, 17425550160)]

def originalBlock85 : Integer.Sparse OriginalKey := [(Sum.inl 1514, -17253001680), (Sum.inl 1520, 83076659520), (Sum.inl 1533, 33430043680), (Sum.inl 1670, -44732773560), (Sum.inl 1676, 11730552000), (Sum.inl 1689, 42334134120), (Sum.inl 1723, -50180808480), (Sum.inl 1729, 39601068160), (Sum.inl 2164, -18203620320), (Sum.inl 2181, -9899351640), (Sum.inl 2683, 4532419840), (Sum.inl 2702, 17425550160), (Sum.inl 3260, 41470746960), (Sum.inl 3266, 102678513360), (Sum.inl 3272, -13949930640), (Sum.inl 3406, 8815051200), (Sum.inl 3408, -52770777840), (Sum.inl 3413, -79464541920), (Sum.inl 3414, 1090620480), (Sum.inl 3415, -33818861040), (Sum.inl 3419, 21662031480), (Sum.inl 3451, 19791401920), (Sum.inl 3452, 61981314480), (Sum.inl 3458, 617189760), (Sum.inl 3461, 59248431360), (Sum.inl 3465, -19207074240), (Sum.inl 3466, -96553292760), (Sum.inl 3472, 13467990040), (Sum.inl 3474, -48784844320), (Sum.inl 3475, -123152322240), (Sum.inl 3476, 2248083000), (Sum.inl 4153, -69012006720), (Sum.inl 4161, 133720174720), (Sum.inl 4178, 332306638080), (Sum.inl 4327, -178931094240), (Sum.inl 4335, 169336536480), (Sum.inl 4347, 46922208000), (Sum.inl 4440, -200723233920), (Sum.inl 4476, 158404272640), (Sum.inl 4528, 165882987840), (Sum.inl 4535, -55799722560), (Sum.inl 4547, 410714053440), (Sum.inl 4600, 69702200640), (Sum.inl 4611, 18129679360), (Sum.inl 4670, -72814481280), (Sum.inl 4757, -39597406560), (Sum.inl 4930, -211083111360), (Sum.inl 4931, 35260204800), (Sum.inl 4933, 4362481920), (Sum.inl 4934, -135275444160), (Sum.inl 4935, 86648125920), (Sum.inl 4944, -317858167680), (Sum.inl 4954, 247925257920), (Sum.inl 4965, -492609288960), (Sum.inl 5034, 79165607680), (Sum.inl 5041, 2468759040), (Sum.inl 5043, -76828296960), (Sum.inl 5044, -195139377280), (Sum.inl 5065, -386213171040), (Sum.inl 5067, 8992332000), (Sum.inl 5085, 236993725440), (Sum.inl 5087, 53871960160)]

theorem originalBlockCheck85 : originalBlock85 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock85 keyMomentRows) := by decide +kernel

theorem originalBlockEval85 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock85 x =
      Integer.Sparse.eval keyPolynomialBlock85 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck85, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
