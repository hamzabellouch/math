import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock81 : Integer.Sparse (Fin 2886) := [(2592, 19706327616), (2593, -23608051200), (2594, 45458951520), (2595, 21803022720), (2596, 27397679520), (2597, -120295503360), (2598, -249815111640), (2599, -146618106000), (2600, -1583273280), (2601, -97221541440), (2602, -112133076480), (2603, -57918681480), (2604, -30136375440), (2605, 111263016744), (2606, -77090685120), (2607, -55422491760), (2608, -58291364928), (2609, -154533336000), (2610, 11023403520), (2611, 45165883200), (2612, 97278520320), (2613, 22389196080), (2614, 243375339360), (2615, 1965872184), (2616, 108902126400), (2617, -84480861360), (2618, 65159040000), (2619, 51191942400), (2620, 21474181440), (2621, -93282494400), (2622, -48167756160), (2623, -59653416480)]

def originalBlock81 : Integer.Sparse OriginalKey := [(Sum.inl 1511, -59653416480), (Sum.inl 1512, -48167756160), (Sum.inl 1513, 21474181440), (Sum.inl 1715, -93282494400), (Sum.inl 1716, 51191942400), (Sum.inl 2144, 19706327616), (Sum.inl 2171, -23608051200), (Sum.inl 2195, 45458951520), (Sum.inl 2252, 21803022720), (Sum.inl 2652, 108902126400), (Sum.inl 2653, -77090685120), (Sum.inl 2654, -1583273280), (Sum.inl 2655, 11023403520), (Sum.inl 2656, 65159040000), (Sum.inl 2657, 97278520320), (Sum.inl 2659, -112133076480), (Sum.inl 3016, -120295503360), (Sum.inl 3023, -154533336000), (Sum.inl 3024, 45165883200), (Sum.inl 3025, -97221541440), (Sum.inl 3221, -58291364928), (Sum.inl 3222, 27397679520), (Sum.inl 3258, 1965872184), (Sum.inl 3259, 243375339360), (Sum.inl 3463, -84480861360), (Sum.inl 3464, 22389196080), (Sum.inl 3509, 111263016744), (Sum.inl 3553, -30136375440), (Sum.inl 3761, -55422491760), (Sum.inl 3762, -57918681480), (Sum.inl 3802, -146618106000), (Sum.inl 3803, -249815111640), (Sum.inl 4154, -238613665920), (Sum.inl 4176, -192671024640), (Sum.inl 4179, 85896725760), (Sum.inl 4475, -373129977600), (Sum.inl 4500, 204767769600), (Sum.inl 4529, 7863488736), (Sum.inl 4545, 973501357440), (Sum.inl 4548, 389114081280), (Sum.inl 4665, 78825310464), (Sum.inl 4762, -94432204800), (Sum.inl 4803, 181835806080), (Sum.inl 4885, -145953368832), (Sum.inl 4891, 109590718080), (Sum.inl 4957, 445052066976), (Sum.inl 4963, -120545501760), (Sum.inl 4976, -448532305920), (Sum.inl 5035, 435608505600), (Sum.inl 5074, -337923445440), (Sum.inl 5086, 89556784320), (Sum.inl 5103, 180663532800), (Sum.inl 5116, 44093614080), (Sum.inl 5215, -308362740480), (Sum.inl 5216, -6333093120), (Sum.inl 5217, 260636160000), (Sum.inl 5254, -481182013440), (Sum.inl 5286, -618133344000), (Sum.inl 5287, -388886165760), (Sum.inl 5353, -221689967040), (Sum.inl 5360, -231674725920), (Sum.inl 5402, -586472424000), (Sum.inl 5407, -999260446560)]

theorem originalBlockCheck81 : originalBlock81 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock81 keyMomentRows) := by decide +kernel

theorem originalBlockEval81 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock81 x =
      Integer.Sparse.eval keyPolynomialBlock81 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck81, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
