import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources3

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource64 (mixedVector B) = 0 := by
  have h1224 : mixedVector B (Sum.inr 1224) = Sparse.eval nodeValue1224 (mixedVector B) := by
    change mixedMoment B node1224 node1224Labels = _
    exact sound1224 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm78, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1224, h2495, h2547, h2647, h2731, h2734, h4092, reducedSource64] using sourceEq78 B hB

theorem rowSound64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row64 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck64, numericCheck64, reducedZero64 B hB hF, mul_zero]

theorem reducedZero65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource65 (mixedVector B) = 0 := by
  have h1359 : mixedVector B (Sum.inr 1359) = Sparse.eval nodeValue1359 (mixedVector B) := by
    change mixedMoment B node1359 node1359Labels = _
    exact sound1359 B hB hF
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2579 : mixedVector B (Sum.inr 2579) = Sparse.eval nodeValue2579 (mixedVector B) := by
    change mixedMoment B node2579 node2579Labels = _
    exact sound2579 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm79, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1359, h2547, h2558, h2579, h2734, h3038, h4092, reducedSource65] using sourceEq79 B hB

theorem rowSound65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row65 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck65, numericCheck65, reducedZero65 B hB hF, mul_zero]

theorem reducedZero66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource66 (mixedVector B) = 0 := by
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm80, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1243, h2519, h2558, h2734, h2743, h4092, reducedSource66] using sourceEq80 B hB

theorem rowSound66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row66 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck66, numericCheck66, reducedZero66 B hB hF, mul_zero]

theorem reducedZero67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource67 (mixedVector B) = 0 := by
  have h1424 : mixedVector B (Sum.inr 1424) = Sparse.eval nodeValue1424 (mixedVector B) := by
    change mixedMoment B node1424 node1424Labels = _
    exact sound1424 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2651 : mixedVector B (Sum.inr 2651) = Sparse.eval nodeValue2651 (mixedVector B) := by
    change mixedMoment B node2651 node2651Labels = _
    exact sound2651 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm81, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1424, h2647, h2651, h2734, h2777, h4092, reducedSource67] using sourceEq81 B hB

theorem rowSound67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row67 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck67, numericCheck67, reducedZero67 B hB hF, mul_zero]

theorem reducedZero68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource68 (mixedVector B) = 0 := by
  have h1227 : mixedVector B (Sum.inr 1227) = Sparse.eval nodeValue1227 (mixedVector B) := by
    change mixedMoment B node1227 node1227Labels = _
    exact sound1227 B hB hF
  have h1359 : mixedVector B (Sum.inr 1359) = Sparse.eval nodeValue1359 (mixedVector B) := by
    change mixedMoment B node1359 node1359Labels = _
    exact sound1359 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h1424 : mixedVector B (Sum.inr 1424) = Sparse.eval nodeValue1424 (mixedVector B) := by
    change mixedMoment B node1424 node1424Labels = _
    exact sound1424 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm82, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1227, h1359, h1372, h1424, h2734, h4092, reducedSource68] using sourceEq82 B hB

theorem rowSound68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row68 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck68, numericCheck68, reducedZero68 B hB hF, mul_zero]

theorem reducedZero69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource69 (mixedVector B) = 0 := by
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h3396 : mixedVector B (Sum.inr 3396) = Sparse.eval nodeValue3396 (mixedVector B) := by
    change mixedMoment B node3396 node3396Labels = _
    exact sound3396 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm85, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2065, h3389, h3396, h3545, h3549, h4085, reducedSource69] using sourceEq85 B hB

theorem rowSound69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row69 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck69, numericCheck69, reducedZero69 B hB hF, mul_zero]

theorem reducedZero70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource70 (mixedVector B) = 0 := by
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm86, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2055, h2063, h2065, h2294, h3549, h4085, reducedSource70] using sourceEq86 B hB

theorem rowSound70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row70 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck70, numericCheck70, reducedZero70 B hB hF, mul_zero]

theorem reducedZero71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource71 (mixedVector B) = 0 := by
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3634 : mixedVector B (Sum.inr 3634) = Sparse.eval nodeValue3634 (mixedVector B) := by
    change mixedMoment B node3634 node3634Labels = _
    exact sound3634 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm87, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2294, h3549, h3634, h4085, reducedSource71] using sourceEq87 B hB

theorem rowSound71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row71 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck71, numericCheck71, reducedZero71 B hB hF, mul_zero]

theorem reducedZero72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource72 (mixedVector B) = 0 := by
  have h3160 : mixedVector B (Sum.inr 3160) = Sparse.eval nodeValue3160 (mixedVector B) := by
    change mixedMoment B node3160 node3160Labels = _
    exact sound3160 B hB hF
  have h3393 : mixedVector B (Sum.inr 3393) = Sparse.eval nodeValue3393 (mixedVector B) := by
    change mixedMoment B node3393 node3393Labels = _
    exact sound3393 B hB hF
  have h3396 : mixedVector B (Sum.inr 3396) = Sparse.eval nodeValue3396 (mixedVector B) := by
    change mixedMoment B node3396 node3396Labels = _
    exact sound3396 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm88, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3160, h3393, h3396, h3549, h4085, reducedSource72] using sourceEq88 B hB

theorem rowSound72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row72 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck72, numericCheck72, reducedZero72 B hB hF, mul_zero]

theorem reducedZero73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource73 (mixedVector B) = 0 := by
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h3393 : mixedVector B (Sum.inr 3393) = Sparse.eval nodeValue3393 (mixedVector B) := by
    change mixedMoment B node3393 node3393Labels = _
    exact sound3393 B hB hF
  have h3495 : mixedVector B (Sum.inr 3495) = Sparse.eval nodeValue3495 (mixedVector B) := by
    change mixedMoment B node3495 node3495Labels = _
    exact sound3495 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm89, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2055, h3393, h3495, h3543, h3549, h4085, reducedSource73] using sourceEq89 B hB

theorem rowSound73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row73 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck73, numericCheck73, reducedZero73 B hB hF, mul_zero]

theorem reducedZero74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource74 (mixedVector B) = 0 := by
  have h3154 : mixedVector B (Sum.inr 3154) = Sparse.eval nodeValue3154 (mixedVector B) := by
    change mixedMoment B node3154 node3154Labels = _
    exact sound3154 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h3495 : mixedVector B (Sum.inr 3495) = Sparse.eval nodeValue3495 (mixedVector B) := by
    change mixedMoment B node3495 node3495Labels = _
    exact sound3495 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm90, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3154, h3389, h3495, h3549, h4085, reducedSource74] using sourceEq90 B hB

theorem rowSound74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row74 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck74, numericCheck74, reducedZero74 B hB hF, mul_zero]

theorem reducedZero75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource75 (mixedVector B) = 0 := by
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h3154 : mixedVector B (Sum.inr 3154) = Sparse.eval nodeValue3154 (mixedVector B) := by
    change mixedMoment B node3154 node3154Labels = _
    exact sound3154 B hB hF
  have h3160 : mixedVector B (Sum.inr 3160) = Sparse.eval nodeValue3160 (mixedVector B) := by
    change mixedMoment B node3160 node3160Labels = _
    exact sound3160 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm91, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2063, h3154, h3160, h3549, h4085, reducedSource75] using sourceEq91 B hB

theorem rowSound75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row75 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck75, numericCheck75, reducedZero75 B hB hF, mul_zero]

theorem reducedZero76 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource76 (mixedVector B) = 0 := by
  have h1613 : mixedVector B (Sum.inr 1613) = Sparse.eval nodeValue1613 (mixedVector B) := by
    change mixedMoment B node1613 node1613Labels = _
    exact sound1613 B hB hF
  have h1615 : mixedVector B (Sum.inr 1615) = Sparse.eval nodeValue1615 (mixedVector B) := by
    change mixedMoment B node1615 node1615Labels = _
    exact sound1615 B hB hF
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h3279 : mixedVector B (Sum.inr 3279) = Sparse.eval nodeValue3279 (mixedVector B) := by
    change mixedMoment B node3279 node3279Labels = _
    exact sound3279 B hB hF
  have h3283 : mixedVector B (Sum.inr 3283) = Sparse.eval nodeValue3283 (mixedVector B) := by
    change mixedMoment B node3283 node3283Labels = _
    exact sound3283 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3350 : mixedVector B (Sum.inr 3350) = Sparse.eval nodeValue3350 (mixedVector B) := by
    change mixedMoment B node3350 node3350Labels = _
    exact sound3350 B hB hF
  have h3355 : mixedVector B (Sum.inr 3355) = Sparse.eval nodeValue3355 (mixedVector B) := by
    change mixedMoment B node3355 node3355Labels = _
    exact sound3355 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  simpa only [sourceForm94, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1613, h1615, h1619, h1723, h3279, h3283, h3291, h3350, h3355, h3434, h3466, h3481, h3519, h3523, h3531, h3539, h3540, h3544, h3580, h3625, h3858, reducedSource76] using sourceEq94 B hB

theorem rowSound76 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row76 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck76, numericCheck76, reducedZero76 B hB hF, mul_zero]

theorem reducedZero77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource77 (mixedVector B) = 0 := by
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm95, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2712, h3064, h3077, h3086, h3902, h4091, reducedSource77] using sourceEq95 B hB

theorem rowSound77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row77 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck77, numericCheck77, reducedZero77 B hB hF, mul_zero]

theorem reducedZero78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource78 (mixedVector B) = 0 := by
  have h1206 : mixedVector B (Sum.inr 1206) = Sparse.eval nodeValue1206 (mixedVector B) := by
    change mixedMoment B node1206 node1206Labels = _
    exact sound1206 B hB hF
  have h1209 : mixedVector B (Sum.inr 1209) = Sparse.eval nodeValue1209 (mixedVector B) := by
    change mixedMoment B node1209 node1209Labels = _
    exact sound1209 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1249 : mixedVector B (Sum.inr 1249) = Sparse.eval nodeValue1249 (mixedVector B) := by
    change mixedMoment B node1249 node1249Labels = _
    exact sound1249 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm96, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1206, h1209, h1217, h1249, h2712, h4091, reducedSource78] using sourceEq96 B hB

theorem rowSound78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row78 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck78, numericCheck78, reducedZero78 B hB hF, mul_zero]

theorem reducedZero79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource79 (mixedVector B) = 0 := by
  have h1249 : mixedVector B (Sum.inr 1249) = Sparse.eval nodeValue1249 (mixedVector B) := by
    change mixedMoment B node1249 node1249Labels = _
    exact sound1249 B hB hF
  have h2562 : mixedVector B (Sum.inr 2562) = Sparse.eval nodeValue2562 (mixedVector B) := by
    change mixedMoment B node2562 node2562Labels = _
    exact sound2562 B hB hF
  have h2624 : mixedVector B (Sum.inr 2624) = Sparse.eval nodeValue2624 (mixedVector B) := by
    change mixedMoment B node2624 node2624Labels = _
    exact sound2624 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm97, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1249, h2562, h2624, h2712, h2751, h4091, reducedSource79] using sourceEq97 B hB

theorem rowSound79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row79 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck79, numericCheck79, reducedZero79 B hB hF, mul_zero]

theorem sourceRowsAt64 : MixedData.sourceRows (64 : Fin 2425) =
    MixedData.row64 := by decide +kernel

theorem sourceRowsAt65 : MixedData.sourceRows (65 : Fin 2425) =
    MixedData.row65 := by decide +kernel

theorem sourceRowsAt66 : MixedData.sourceRows (66 : Fin 2425) =
    MixedData.row66 := by decide +kernel

theorem sourceRowsAt67 : MixedData.sourceRows (67 : Fin 2425) =
    MixedData.row67 := by decide +kernel

theorem sourceRowsAt68 : MixedData.sourceRows (68 : Fin 2425) =
    MixedData.row68 := by decide +kernel

theorem sourceRowsAt69 : MixedData.sourceRows (69 : Fin 2425) =
    MixedData.row69 := by decide +kernel

theorem sourceRowsAt70 : MixedData.sourceRows (70 : Fin 2425) =
    MixedData.row70 := by decide +kernel

theorem sourceRowsAt71 : MixedData.sourceRows (71 : Fin 2425) =
    MixedData.row71 := by decide +kernel

theorem sourceRowsAt72 : MixedData.sourceRows (72 : Fin 2425) =
    MixedData.row72 := by decide +kernel

theorem sourceRowsAt73 : MixedData.sourceRows (73 : Fin 2425) =
    MixedData.row73 := by decide +kernel

theorem sourceRowsAt74 : MixedData.sourceRows (74 : Fin 2425) =
    MixedData.row74 := by decide +kernel

theorem sourceRowsAt75 : MixedData.sourceRows (75 : Fin 2425) =
    MixedData.row75 := by decide +kernel

theorem sourceRowsAt76 : MixedData.sourceRows (76 : Fin 2425) =
    MixedData.row76 := by decide +kernel

theorem sourceRowsAt77 : MixedData.sourceRows (77 : Fin 2425) =
    MixedData.row77 := by decide +kernel

theorem sourceRowsAt78 : MixedData.sourceRows (78 : Fin 2425) =
    MixedData.row78 := by decide +kernel

theorem sourceRowsAt79 : MixedData.sourceRows (79 : Fin 2425) =
    MixedData.row79 := by decide +kernel

theorem chunkSound4 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 4) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 64 ∨ k.val = 65 ∨ k.val = 66 ∨ k.val = 67 ∨ k.val = 68 ∨ k.val = 69 ∨ k.val = 70 ∨ k.val = 71 ∨ k.val = 72 ∨ k.val = 73 ∨ k.val = 74 ∨ k.val = 75 ∨ k.val = 76 ∨ k.val = 77 ∨ k.val = 78 ∨ k.val = 79 := by omega
  rcases heq with h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79
  · have he : k = (64 : Fin 2425) := Fin.ext h64
    subst k
    rw [sourceRowsAt64]
    exact rowSound64 B hB hF
  · have he : k = (65 : Fin 2425) := Fin.ext h65
    subst k
    rw [sourceRowsAt65]
    exact rowSound65 B hB hF
  · have he : k = (66 : Fin 2425) := Fin.ext h66
    subst k
    rw [sourceRowsAt66]
    exact rowSound66 B hB hF
  · have he : k = (67 : Fin 2425) := Fin.ext h67
    subst k
    rw [sourceRowsAt67]
    exact rowSound67 B hB hF
  · have he : k = (68 : Fin 2425) := Fin.ext h68
    subst k
    rw [sourceRowsAt68]
    exact rowSound68 B hB hF
  · have he : k = (69 : Fin 2425) := Fin.ext h69
    subst k
    rw [sourceRowsAt69]
    exact rowSound69 B hB hF
  · have he : k = (70 : Fin 2425) := Fin.ext h70
    subst k
    rw [sourceRowsAt70]
    exact rowSound70 B hB hF
  · have he : k = (71 : Fin 2425) := Fin.ext h71
    subst k
    rw [sourceRowsAt71]
    exact rowSound71 B hB hF
  · have he : k = (72 : Fin 2425) := Fin.ext h72
    subst k
    rw [sourceRowsAt72]
    exact rowSound72 B hB hF
  · have he : k = (73 : Fin 2425) := Fin.ext h73
    subst k
    rw [sourceRowsAt73]
    exact rowSound73 B hB hF
  · have he : k = (74 : Fin 2425) := Fin.ext h74
    subst k
    rw [sourceRowsAt74]
    exact rowSound74 B hB hF
  · have he : k = (75 : Fin 2425) := Fin.ext h75
    subst k
    rw [sourceRowsAt75]
    exact rowSound75 B hB hF
  · have he : k = (76 : Fin 2425) := Fin.ext h76
    subst k
    rw [sourceRowsAt76]
    exact rowSound76 B hB hF
  · have he : k = (77 : Fin 2425) := Fin.ext h77
    subst k
    rw [sourceRowsAt77]
    exact rowSound77 B hB hF
  · have he : k = (78 : Fin 2425) := Fin.ext h78
    subst k
    rw [sourceRowsAt78]
    exact rowSound78 B hB hF
  · have he : k = (79 : Fin 2425) := Fin.ext h79
    subst k
    rw [sourceRowsAt79]
    exact rowSound79 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
