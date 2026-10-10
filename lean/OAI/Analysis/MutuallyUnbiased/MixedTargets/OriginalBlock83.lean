import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock83 : Integer.Sparse (Fin 2886) := [(2656, 8689273200), (2657, 116686987200), (2658, 46987459440), (2659, -9428064960), (2660, 39641370240), (2661, 8356094400), (2662, 25571060400), (2663, 6448516320), (2664, 85165226856), (2665, -83506716880), (2666, -4466670560), (2667, -28301606400), (2668, -54421667240), (2669, 65164959920), (2670, -5759404800), (2671, 24440506640), (2672, 75158508480), (2673, -7644434160), (2674, 37314069920), (2675, 4912046640), (2676, 249303360), (2677, 31168829520), (2678, 54421821120), (2679, 57815945440), (2680, -6115859880), (2681, -2349687640), (2682, -28910416160), (2683, -111901383360), (2684, 23588739440), (2685, -29135184640), (2686, 85300658880), (2687, -7881846960)]

def originalBlock83 : Integer.Sparse OriginalKey := [(Sum.inl 1522, 8689273200), (Sum.inl 1523, 24440506640), (Sum.inl 1678, 39641370240), (Sum.inl 1679, 75158508480), (Sum.inl 1682, 116686987200), (Sum.inl 1736, 46987459440), (Sum.inl 2155, 25571060400), (Sum.inl 2176, 6448516320), (Sum.inl 2681, 31168829520), (Sum.inl 2687, 249303360), (Sum.inl 2700, -6115859880), (Sum.inl 2706, 54421821120), (Sum.inl 2738, 57815945440), (Sum.inl 2744, 37314069920), (Sum.inl 2781, 4912046640), (Sum.inl 3268, -54421667240), (Sum.inl 3414, 8356094400), (Sum.inl 3415, -7644434160), (Sum.inl 3418, -9428064960), (Sum.inl 3452, 65164959920), (Sum.inl 3508, -4466670560), (Sum.inl 3509, 85165226856), (Sum.inl 3510, -28301606400), (Sum.inl 3511, -5759404800), (Sum.inl 3512, -83506716880), (Sum.inl 3557, 23588739440), (Sum.inl 3569, -29135184640), (Sum.inl 3570, -111901383360), (Sum.inl 3571, 85300658880), (Sum.inl 3572, -28910416160), (Sum.inl 3573, -2349687640), (Sum.inl 3584, -7881846960), (Sum.inl 4158, 34757092800), (Sum.inl 4160, 97762026560), (Sum.inl 4332, 158565480960), (Sum.inl 4334, 300634033920), (Sum.inl 4357, 466747948800), (Sum.inl 4444, 187949837760), (Sum.inl 4534, -217686668960), (Sum.inl 4669, 102284241600), (Sum.inl 4756, 25794065280), (Sum.inl 4933, 33424377600), (Sum.inl 4934, -30577736640), (Sum.inl 4951, -37712259840), (Sum.inl 4954, 260659839680), (Sum.inl 4955, -17866682240), (Sum.inl 4956, -113206425600), (Sum.inl 4957, 340660907424), (Sum.inl 4958, -23037619200), (Sum.inl 4959, -334026867520), (Sum.inl 5144, 94354957760), (Sum.inl 5150, -24463439520), (Sum.inl 5151, 124675318080), (Sum.inl 5197, -116540738560), (Sum.inl 5198, -447605533440), (Sum.inl 5205, 217687284480), (Sum.inl 5206, 997213440), (Sum.inl 5270, 231263781760), (Sum.inl 5276, 149256279680), (Sum.inl 5281, 341202635520), (Sum.inl 5289, -115641664640), (Sum.inl 5295, 19648186560), (Sum.inl 5299, -9398750560), (Sum.inl 5300, -31527387840)]

theorem originalBlockCheck83 : originalBlock83 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock83 keyMomentRows) := by decide +kernel

theorem originalBlockEval83 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock83 x =
      Integer.Sparse.eval keyPolynomialBlock83 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck83, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
