import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic91
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources53

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1456 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h1922 : mixedVector B (Sum.inr 1922) = Sparse.eval nodeValue1922 (mixedVector B) := by
    change mixedMoment B node1922 node1922Labels = _
    exact sound1922 B hB hF
  have h2118 : mixedVector B (Sum.inr 2118) = Sparse.eval nodeValue2118 (mixedVector B) := by
    change mixedMoment B node2118 node2118Labels = _
    exact sound2118 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1707, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h1922, h2118, h2195, h2214, h2216, h4080, reducedSource1456] using sourceEq1707 B hB

theorem rowSound1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1456 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1456, numericCheck1456, reducedZero1456 B hB hF, mul_zero]

theorem reducedZero1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1457 (mixedVector B) = 0 := by
  have h987 : mixedVector B (Sum.inr 987) = Sparse.eval nodeValue987 (mixedVector B) := by
    change mixedMoment B node987 node987Labels = _
    exact sound987 B hB hF
  have h1921 : mixedVector B (Sum.inr 1921) = Sparse.eval nodeValue1921 (mixedVector B) := by
    change mixedMoment B node1921 node1921Labels = _
    exact sound1921 B hB hF
  have h2117 : mixedVector B (Sum.inr 2117) = Sparse.eval nodeValue2117 (mixedVector B) := by
    change mixedMoment B node2117 node2117Labels = _
    exact sound2117 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1708, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h987, h1921, h2117, h2213, h2215, h4082, reducedSource1457] using sourceEq1708 B hB

theorem rowSound1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1457 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1457, numericCheck1457, reducedZero1457 B hB hF, mul_zero]

theorem reducedZero1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1458 (mixedVector B) = 0 := by
  have h1023 : mixedVector B (Sum.inr 1023) = Sparse.eval nodeValue1023 (mixedVector B) := by
    change mixedMoment B node1023 node1023Labels = _
    exact sound1023 B hB hF
  have h2091 : mixedVector B (Sum.inr 2091) = Sparse.eval nodeValue2091 (mixedVector B) := by
    change mixedMoment B node2091 node2091Labels = _
    exact sound2091 B hB hF
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1709, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1023, h2091, h2234, h2241, h4079, reducedSource1458] using sourceEq1709 B hB

theorem rowSound1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1458 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1458, numericCheck1458, reducedZero1458 B hB hF, mul_zero]

theorem reducedZero1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1459 (mixedVector B) = 0 := by
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h1023 : mixedVector B (Sum.inr 1023) = Sparse.eval nodeValue1023 (mixedVector B) := by
    change mixedMoment B node1023 node1023Labels = _
    exact sound1023 B hB hF
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1710, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1018, h1023, h1034, h2241, h4079, reducedSource1459] using sourceEq1710 B hB

theorem rowSound1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1459 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1459, numericCheck1459, reducedZero1459 B hB hF, mul_zero]

theorem reducedZero1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1460 (mixedVector B) = 0 := by
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h2086 : mixedVector B (Sum.inr 2086) = Sparse.eval nodeValue2086 (mixedVector B) := by
    change mixedMoment B node2086 node2086Labels = _
    exact sound2086 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1711, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1018, h2086, h2191, h2232, h2241, h4079, reducedSource1460] using sourceEq1711 B hB

theorem rowSound1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1460 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1460, numericCheck1460, reducedZero1460 B hB hF, mul_zero]

theorem reducedZero1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1461 (mixedVector B) = 0 := by
  have h1017 : mixedVector B (Sum.inr 1017) = Sparse.eval nodeValue1017 (mixedVector B) := by
    change mixedMoment B node1017 node1017Labels = _
    exact sound1017 B hB hF
  have h2085 : mixedVector B (Sum.inr 2085) = Sparse.eval nodeValue2085 (mixedVector B) := by
    change mixedMoment B node2085 node2085Labels = _
    exact sound2085 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1712, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1017, h2085, h2190, h2240, h2242, h4080, reducedSource1461] using sourceEq1712 B hB

theorem rowSound1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1461 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1461, numericCheck1461, reducedZero1461 B hB hF, mul_zero]

theorem reducedZero1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1462 (mixedVector B) = 0 := by
  have h1045 : mixedVector B (Sum.inr 1045) = Sparse.eval nodeValue1045 (mixedVector B) := by
    change mixedMoment B node1045 node1045Labels = _
    exact sound1045 B hB hF
  have h2024 : mixedVector B (Sum.inr 2024) = Sparse.eval nodeValue2024 (mixedVector B) := by
    change mixedMoment B node2024 node2024Labels = _
    exact sound2024 B hB hF
  have h2111 : mixedVector B (Sum.inr 2111) = Sparse.eval nodeValue2111 (mixedVector B) := by
    change mixedMoment B node2111 node2111Labels = _
    exact sound2111 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1713, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1045, h2024, h2111, h2246, h2254, h2260, h4080, reducedSource1462] using sourceEq1713 B hB

theorem rowSound1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1462 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1462, numericCheck1462, reducedZero1462 B hB hF, mul_zero]

theorem reducedZero1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1463 (mixedVector B) = 0 := by
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h1045 : mixedVector B (Sum.inr 1045) = Sparse.eval nodeValue1045 (mixedVector B) := by
    change mixedMoment B node1045 node1045Labels = _
    exact sound1045 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1714, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1032, h1035, h1036, h1045, h1073, h2260, h4080, reducedSource1463] using sourceEq1714 B hB

theorem rowSound1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1463 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1463, numericCheck1463, reducedZero1463 B hB hF, mul_zero]

theorem reducedZero1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1464 (mixedVector B) = 0 := by
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h2017 : mixedVector B (Sum.inr 2017) = Sparse.eval nodeValue2017 (mixedVector B) := by
    change mixedMoment B node2017 node2017Labels = _
    exact sound2017 B hB hF
  have h2102 : mixedVector B (Sum.inr 2102) = Sparse.eval nodeValue2102 (mixedVector B) := by
    change mixedMoment B node2102 node2102Labels = _
    exact sound2102 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1715, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1036, h2017, h2102, h2206, h2251, h2260, h4080, reducedSource1464] using sourceEq1715 B hB

theorem rowSound1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1464 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1464, numericCheck1464, reducedZero1464 B hB hF, mul_zero]

theorem reducedZero1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1465 (mixedVector B) = 0 := by
  have h4152 : mixedVector B (Sum.inr 4152) = Sparse.eval nodeValue4152 (mixedVector B) := by
    change mixedMoment B node4152 node4152Labels = _
    exact sound4152 B hB hF
  have h4157 : mixedVector B (Sum.inr 4157) = Sparse.eval nodeValue4157 (mixedVector B) := by
    change mixedMoment B node4157 node4157Labels = _
    exact sound4157 B hB hF
  have h4158 : mixedVector B (Sum.inr 4158) = Sparse.eval nodeValue4158 (mixedVector B) := by
    change mixedMoment B node4158 node4158Labels = _
    exact sound4158 B hB hF
  have h4182 : mixedVector B (Sum.inr 4182) = Sparse.eval nodeValue4182 (mixedVector B) := by
    change mixedMoment B node4182 node4182Labels = _
    exact sound4182 B hB hF
  have h4331 : mixedVector B (Sum.inr 4331) = Sparse.eval nodeValue4331 (mixedVector B) := by
    change mixedMoment B node4331 node4331Labels = _
    exact sound4331 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4366 : mixedVector B (Sum.inr 4366) = Sparse.eval nodeValue4366 (mixedVector B) := by
    change mixedMoment B node4366 node4366Labels = _
    exact sound4366 B hB hF
  have h4371 : mixedVector B (Sum.inr 4371) = Sparse.eval nodeValue4371 (mixedVector B) := by
    change mixedMoment B node4371 node4371Labels = _
    exact sound4371 B hB hF
  have h4372 : mixedVector B (Sum.inr 4372) = Sparse.eval nodeValue4372 (mixedVector B) := by
    change mixedMoment B node4372 node4372Labels = _
    exact sound4372 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  simpa only [sourceForm1716, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4152, h4157, h4158, h4182, h4331, h4332, h4351, h4366, h4371, h4372, h4439, h4442, h4444, h4456, h4458, h4461, h4497, h4805, h4869, h4889, h4893, reducedSource1465] using sourceEq1716 B hB

theorem rowSound1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1465 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1465, numericCheck1465, reducedZero1465 B hB hF, mul_zero]

theorem reducedZero1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1466 (mixedVector B) = 0 := by
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h1528 : mixedVector B (Sum.inr 1528) = Sparse.eval nodeValue1528 (mixedVector B) := by
    change mixedMoment B node1528 node1528Labels = _
    exact sound1528 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1680 : mixedVector B (Sum.inr 1680) = Sparse.eval nodeValue1680 (mixedVector B) := by
    change mixedMoment B node1680 node1680Labels = _
    exact sound1680 B hB hF
  have h1684 : mixedVector B (Sum.inr 1684) = Sparse.eval nodeValue1684 (mixedVector B) := by
    change mixedMoment B node1684 node1684Labels = _
    exact sound1684 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1742 : mixedVector B (Sum.inr 1742) = Sparse.eval nodeValue1742 (mixedVector B) := by
    change mixedMoment B node1742 node1742Labels = _
    exact sound1742 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  simpa only [sourceForm1717, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1510, h1522, h1524, h1528, h1678, h1680, h1684, h1706, h1711, h1713, h1724, h1726, h1734, h1736, h1737, h1742, h1744, h2214, h2263, h2275, h2277, reducedSource1466] using sourceEq1717 B hB

theorem rowSound1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1466 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1466, numericCheck1466, reducedZero1466 B hB hF, mul_zero]

theorem reducedZero1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1467 (mixedVector B) = 0 := by
  have h610 : mixedVector B (Sum.inr 610) = Sparse.eval nodeValue610 (mixedVector B) := by
    change mixedMoment B node610 node610Labels = _
    exact sound610 B hB hF
  have h929 : mixedVector B (Sum.inr 929) = Sparse.eval nodeValue929 (mixedVector B) := by
    change mixedMoment B node929 node929Labels = _
    exact sound929 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1718, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h610, h929, h1044, h1081, h4083, reducedSource1467] using sourceEq1718 B hB

theorem rowSound1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1467 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1467, numericCheck1467, reducedZero1467 B hB hF, mul_zero]

theorem reducedZero1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1468 (mixedVector B) = 0 := by
  have h944 : mixedVector B (Sum.inr 944) = Sparse.eval nodeValue944 (mixedVector B) := by
    change mixedMoment B node944 node944Labels = _
    exact sound944 B hB hF
  have h949 : mixedVector B (Sum.inr 949) = Sparse.eval nodeValue949 (mixedVector B) := by
    change mixedMoment B node949 node949Labels = _
    exact sound949 B hB hF
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1719, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h944, h949, h950, h1044, h2110, h4083, reducedSource1468] using sourceEq1719 B hB

theorem rowSound1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1468 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1468, numericCheck1468, reducedZero1468 B hB hF, mul_zero]

theorem reducedZero1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1469 (mixedVector B) = 0 := by
  have h4104 : mixedVector B (Sum.inr 4104) = Sparse.eval nodeValue4104 (mixedVector B) := by
    change mixedMoment B node4104 node4104Labels = _
    exact sound4104 B hB hF
  have h4105 : mixedVector B (Sum.inr 4105) = Sparse.eval nodeValue4105 (mixedVector B) := by
    change mixedMoment B node4105 node4105Labels = _
    exact sound4105 B hB hF
  have h4106 : mixedVector B (Sum.inr 4106) = Sparse.eval nodeValue4106 (mixedVector B) := by
    change mixedMoment B node4106 node4106Labels = _
    exact sound4106 B hB hF
  have h4126 : mixedVector B (Sum.inr 4126) = Sparse.eval nodeValue4126 (mixedVector B) := by
    change mixedMoment B node4126 node4126Labels = _
    exact sound4126 B hB hF
  have h4290 : mixedVector B (Sum.inr 4290) = Sparse.eval nodeValue4290 (mixedVector B) := by
    change mixedMoment B node4290 node4290Labels = _
    exact sound4290 B hB hF
  have h4291 : mixedVector B (Sum.inr 4291) = Sparse.eval nodeValue4291 (mixedVector B) := by
    change mixedMoment B node4291 node4291Labels = _
    exact sound4291 B hB hF
  have h4307 : mixedVector B (Sum.inr 4307) = Sparse.eval nodeValue4307 (mixedVector B) := by
    change mixedMoment B node4307 node4307Labels = _
    exact sound4307 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4489 : mixedVector B (Sum.inr 4489) = Sparse.eval nodeValue4489 (mixedVector B) := by
    change mixedMoment B node4489 node4489Labels = _
    exact sound4489 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1720, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4104, h4105, h4106, h4126, h4290, h4291, h4307, h4351, h4352, h4354, h4451, h4452, h4461, h4463, h4466, h4489, h4503, h5076, h5172, h5290, h5294, reducedSource1469] using sourceEq1720 B hB

theorem rowSound1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1469 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1469, numericCheck1469, reducedZero1469 B hB hF, mul_zero]

theorem reducedZero1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1470 (mixedVector B) = 0 := by
  have h786 : mixedVector B (Sum.inr 786) = Sparse.eval nodeValue786 (mixedVector B) := by
    change mixedMoment B node786 node786Labels = _
    exact sound786 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h811 : mixedVector B (Sum.inr 811) = Sparse.eval nodeValue811 (mixedVector B) := by
    change mixedMoment B node811 node811Labels = _
    exact sound811 B hB hF
  have h827 : mixedVector B (Sum.inr 827) = Sparse.eval nodeValue827 (mixedVector B) := by
    change mixedMoment B node827 node827Labels = _
    exact sound827 B hB hF
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h981 : mixedVector B (Sum.inr 981) = Sparse.eval nodeValue981 (mixedVector B) := by
    change mixedMoment B node981 node981Labels = _
    exact sound981 B hB hF
  have h990 : mixedVector B (Sum.inr 990) = Sparse.eval nodeValue990 (mixedVector B) := by
    change mixedMoment B node990 node990Labels = _
    exact sound990 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h1023 : mixedVector B (Sum.inr 1023) = Sparse.eval nodeValue1023 (mixedVector B) := by
    change mixedMoment B node1023 node1023Labels = _
    exact sound1023 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h1045 : mixedVector B (Sum.inr 1045) = Sparse.eval nodeValue1045 (mixedVector B) := by
    change mixedMoment B node1045 node1045Labels = _
    exact sound1045 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h1060 : mixedVector B (Sum.inr 1060) = Sparse.eval nodeValue1060 (mixedVector B) := by
    change mixedMoment B node1060 node1060Labels = _
    exact sound1060 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1267 : mixedVector B (Sum.inr 1267) = Sparse.eval nodeValue1267 (mixedVector B) := by
    change mixedMoment B node1267 node1267Labels = _
    exact sound1267 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  simpa only [sourceForm1723, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h786, h810, h811, h827, h980, h981, h990, h1021, h1023, h1041, h1042, h1044, h1045, h1058, h1060, h1086, h1087, h1216, h1267, h1270, h1305, reducedSource1470] using sourceEq1723 B hB

theorem rowSound1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1470 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1470, numericCheck1470, reducedZero1470 B hB hF, mul_zero]

theorem reducedZero1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1471 (mixedVector B) = 0 := by
  have h4150 : mixedVector B (Sum.inr 4150) = Sparse.eval nodeValue4150 (mixedVector B) := by
    change mixedMoment B node4150 node4150Labels = _
    exact sound4150 B hB hF
  have h4153 : mixedVector B (Sum.inr 4153) = Sparse.eval nodeValue4153 (mixedVector B) := by
    change mixedMoment B node4153 node4153Labels = _
    exact sound4153 B hB hF
  have h4155 : mixedVector B (Sum.inr 4155) = Sparse.eval nodeValue4155 (mixedVector B) := by
    change mixedMoment B node4155 node4155Labels = _
    exact sound4155 B hB hF
  have h4158 : mixedVector B (Sum.inr 4158) = Sparse.eval nodeValue4158 (mixedVector B) := by
    change mixedMoment B node4158 node4158Labels = _
    exact sound4158 B hB hF
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4329 : mixedVector B (Sum.inr 4329) = Sparse.eval nodeValue4329 (mixedVector B) := by
    change mixedMoment B node4329 node4329Labels = _
    exact sound4329 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4364 : mixedVector B (Sum.inr 4364) = Sparse.eval nodeValue4364 (mixedVector B) := by
    change mixedMoment B node4364 node4364Labels = _
    exact sound4364 B hB hF
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4372 : mixedVector B (Sum.inr 4372) = Sparse.eval nodeValue4372 (mixedVector B) := by
    change mixedMoment B node4372 node4372Labels = _
    exact sound4372 B hB hF
  have h4438 : mixedVector B (Sum.inr 4438) = Sparse.eval nodeValue4438 (mixedVector B) := by
    change mixedMoment B node4438 node4438Labels = _
    exact sound4438 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1724, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4150, h4153, h4155, h4158, h4175, h4327, h4329, h4332, h4344, h4364, h4367, h4369, h4372, h4438, h4440, h4444, h4456, h4458, h4461, h4463, h4467, h4497, h4502, h4802, h4866, h4888, h4893, h4895, reducedSource1471] using sourceEq1724 B hB

theorem rowSound1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1471 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1471, numericCheck1471, reducedZero1471 B hB hF, mul_zero]

theorem sourceRowsAt1456 : MixedData.sourceRows (1456 : Fin 2425) =
    MixedData.row1456 := by decide +kernel

theorem sourceRowsAt1457 : MixedData.sourceRows (1457 : Fin 2425) =
    MixedData.row1457 := by decide +kernel

theorem sourceRowsAt1458 : MixedData.sourceRows (1458 : Fin 2425) =
    MixedData.row1458 := by decide +kernel

theorem sourceRowsAt1459 : MixedData.sourceRows (1459 : Fin 2425) =
    MixedData.row1459 := by decide +kernel

theorem sourceRowsAt1460 : MixedData.sourceRows (1460 : Fin 2425) =
    MixedData.row1460 := by decide +kernel

theorem sourceRowsAt1461 : MixedData.sourceRows (1461 : Fin 2425) =
    MixedData.row1461 := by decide +kernel

theorem sourceRowsAt1462 : MixedData.sourceRows (1462 : Fin 2425) =
    MixedData.row1462 := by decide +kernel

theorem sourceRowsAt1463 : MixedData.sourceRows (1463 : Fin 2425) =
    MixedData.row1463 := by decide +kernel

theorem sourceRowsAt1464 : MixedData.sourceRows (1464 : Fin 2425) =
    MixedData.row1464 := by decide +kernel

theorem sourceRowsAt1465 : MixedData.sourceRows (1465 : Fin 2425) =
    MixedData.row1465 := by decide +kernel

theorem sourceRowsAt1466 : MixedData.sourceRows (1466 : Fin 2425) =
    MixedData.row1466 := by decide +kernel

theorem sourceRowsAt1467 : MixedData.sourceRows (1467 : Fin 2425) =
    MixedData.row1467 := by decide +kernel

theorem sourceRowsAt1468 : MixedData.sourceRows (1468 : Fin 2425) =
    MixedData.row1468 := by decide +kernel

theorem sourceRowsAt1469 : MixedData.sourceRows (1469 : Fin 2425) =
    MixedData.row1469 := by decide +kernel

theorem sourceRowsAt1470 : MixedData.sourceRows (1470 : Fin 2425) =
    MixedData.row1470 := by decide +kernel

theorem sourceRowsAt1471 : MixedData.sourceRows (1471 : Fin 2425) =
    MixedData.row1471 := by decide +kernel

theorem chunkSound91 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 91) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1456 ∨ k.val = 1457 ∨ k.val = 1458 ∨ k.val = 1459 ∨ k.val = 1460 ∨ k.val = 1461 ∨ k.val = 1462 ∨ k.val = 1463 ∨ k.val = 1464 ∨ k.val = 1465 ∨ k.val = 1466 ∨ k.val = 1467 ∨ k.val = 1468 ∨ k.val = 1469 ∨ k.val = 1470 ∨ k.val = 1471 := by omega
  rcases heq with h1456 | h1457 | h1458 | h1459 | h1460 | h1461 | h1462 | h1463 | h1464 | h1465 | h1466 | h1467 | h1468 | h1469 | h1470 | h1471
  · have he : k = (1456 : Fin 2425) := Fin.ext h1456
    subst k
    rw [sourceRowsAt1456]
    exact rowSound1456 B hB hF
  · have he : k = (1457 : Fin 2425) := Fin.ext h1457
    subst k
    rw [sourceRowsAt1457]
    exact rowSound1457 B hB hF
  · have he : k = (1458 : Fin 2425) := Fin.ext h1458
    subst k
    rw [sourceRowsAt1458]
    exact rowSound1458 B hB hF
  · have he : k = (1459 : Fin 2425) := Fin.ext h1459
    subst k
    rw [sourceRowsAt1459]
    exact rowSound1459 B hB hF
  · have he : k = (1460 : Fin 2425) := Fin.ext h1460
    subst k
    rw [sourceRowsAt1460]
    exact rowSound1460 B hB hF
  · have he : k = (1461 : Fin 2425) := Fin.ext h1461
    subst k
    rw [sourceRowsAt1461]
    exact rowSound1461 B hB hF
  · have he : k = (1462 : Fin 2425) := Fin.ext h1462
    subst k
    rw [sourceRowsAt1462]
    exact rowSound1462 B hB hF
  · have he : k = (1463 : Fin 2425) := Fin.ext h1463
    subst k
    rw [sourceRowsAt1463]
    exact rowSound1463 B hB hF
  · have he : k = (1464 : Fin 2425) := Fin.ext h1464
    subst k
    rw [sourceRowsAt1464]
    exact rowSound1464 B hB hF
  · have he : k = (1465 : Fin 2425) := Fin.ext h1465
    subst k
    rw [sourceRowsAt1465]
    exact rowSound1465 B hB hF
  · have he : k = (1466 : Fin 2425) := Fin.ext h1466
    subst k
    rw [sourceRowsAt1466]
    exact rowSound1466 B hB hF
  · have he : k = (1467 : Fin 2425) := Fin.ext h1467
    subst k
    rw [sourceRowsAt1467]
    exact rowSound1467 B hB hF
  · have he : k = (1468 : Fin 2425) := Fin.ext h1468
    subst k
    rw [sourceRowsAt1468]
    exact rowSound1468 B hB hF
  · have he : k = (1469 : Fin 2425) := Fin.ext h1469
    subst k
    rw [sourceRowsAt1469]
    exact rowSound1469 B hB hF
  · have he : k = (1470 : Fin 2425) := Fin.ext h1470
    subst k
    rw [sourceRowsAt1470]
    exact rowSound1470 B hB hF
  · have he : k = (1471 : Fin 2425) := Fin.ext h1471
    subst k
    rw [sourceRowsAt1471]
    exact rowSound1471 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
