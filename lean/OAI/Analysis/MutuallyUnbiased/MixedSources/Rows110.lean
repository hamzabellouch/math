import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic110
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources66

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1760 (mixedVector B) = 0 := by
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2108, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3476, h3478, h3480, h3482, h3522, h3612, h4082, reducedSource1760] using sourceEq2108 B hB

theorem rowSound1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1760 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1760, numericCheck1760, reducedZero1760 B hB hF, mul_zero]

theorem reducedZero1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1761 (mixedVector B) = 0 := by
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h2674 : mixedVector B (Sum.inr 2674) = Sparse.eval nodeValue2674 (mixedVector B) := by
    change mixedMoment B node2674 node2674Labels = _
    exact sound2674 B hB hF
  have h3348 : mixedVector B (Sum.inr 3348) = Sparse.eval nodeValue3348 (mixedVector B) := by
    change mixedMoment B node3348 node3348Labels = _
    exact sound3348 B hB hF
  have h3430 : mixedVector B (Sum.inr 3430) = Sparse.eval nodeValue3430 (mixedVector B) := by
    change mixedMoment B node3430 node3430Labels = _
    exact sound3430 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2110, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1928, h2674, h3348, h3430, h3478, h3480, h4082, reducedSource1761] using sourceEq2110 B hB

theorem rowSound1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1761 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1761, numericCheck1761, reducedZero1761 B hB hF, mul_zero]

theorem reducedZero1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1762 (mixedVector B) = 0 := by
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h2324 : mixedVector B (Sum.inr 2324) = Sparse.eval nodeValue2324 (mixedVector B) := by
    change mixedMoment B node2324 node2324Labels = _
    exact sound2324 B hB hF
  have h2441 : mixedVector B (Sum.inr 2441) = Sparse.eval nodeValue2441 (mixedVector B) := by
    change mixedMoment B node2441 node2441Labels = _
    exact sound2441 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2111, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1117, h2324, h2441, h2473, h2480, h2483, h4091, reducedSource1762] using sourceEq2111 B hB

theorem rowSound1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1762 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1762, numericCheck1762, reducedZero1762 B hB hF, mul_zero]

theorem reducedZero1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1763 (mixedVector B) = 0 := by
  have h2320 : mixedVector B (Sum.inr 2320) = Sparse.eval nodeValue2320 (mixedVector B) := by
    change mixedMoment B node2320 node2320Labels = _
    exact sound2320 B hB hF
  have h2797 : mixedVector B (Sum.inr 2797) = Sparse.eval nodeValue2797 (mixedVector B) := by
    change mixedMoment B node2797 node2797Labels = _
    exact sound2797 B hB hF
  have h2900 : mixedVector B (Sum.inr 2900) = Sparse.eval nodeValue2900 (mixedVector B) := by
    change mixedMoment B node2900 node2900Labels = _
    exact sound2900 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2112, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2320, h2797, h2900, h2931, h2981, h3690, h4091, reducedSource1763] using sourceEq2112 B hB

theorem rowSound1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1763 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1763, numericCheck1763, reducedZero1763 B hB hF, mul_zero]

theorem reducedZero1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1764 (mixedVector B) = 0 := by
  have h1941 : mixedVector B (Sum.inr 1941) = Sparse.eval nodeValue1941 (mixedVector B) := by
    change mixedMoment B node1941 node1941Labels = _
    exact sound1941 B hB hF
  have h3351 : mixedVector B (Sum.inr 3351) = Sparse.eval nodeValue3351 (mixedVector B) := by
    change mixedMoment B node3351 node3351Labels = _
    exact sound3351 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2114, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1941, h3351, h3476, h3482, h4082, reducedSource1764] using sourceEq2114 B hB

theorem rowSound1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1764 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1764, numericCheck1764, reducedZero1764 B hB hF, mul_zero]

theorem reducedZero1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1765 (mixedVector B) = 0 := by
  have h1921 : mixedVector B (Sum.inr 1921) = Sparse.eval nodeValue1921 (mixedVector B) := by
    change mixedMoment B node1921 node1921Labels = _
    exact sound1921 B hB hF
  have h2668 : mixedVector B (Sum.inr 2668) = Sparse.eval nodeValue2668 (mixedVector B) := by
    change mixedMoment B node2668 node2668Labels = _
    exact sound2668 B hB hF
  have h3345 : mixedVector B (Sum.inr 3345) = Sparse.eval nodeValue3345 (mixedVector B) := by
    change mixedMoment B node3345 node3345Labels = _
    exact sound3345 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2115, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1921, h2668, h3345, h3476, h3478, h4082, reducedSource1765] using sourceEq2115 B hB

theorem rowSound1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1765 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1765, numericCheck1765, reducedZero1765 B hB hF, mul_zero]

theorem reducedZero1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1766 (mixedVector B) = 0 := by
  have h1807 : mixedVector B (Sum.inr 1807) = Sparse.eval nodeValue1807 (mixedVector B) := by
    change mixedMoment B node1807 node1807Labels = _
    exact sound1807 B hB hF
  have h2427 : mixedVector B (Sum.inr 2427) = Sparse.eval nodeValue2427 (mixedVector B) := by
    change mixedMoment B node2427 node2427Labels = _
    exact sound2427 B hB hF
  have h2435 : mixedVector B (Sum.inr 2435) = Sparse.eval nodeValue2435 (mixedVector B) := by
    change mixedMoment B node2435 node2435Labels = _
    exact sound2435 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2118, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1807, h2427, h2435, h2522, h2560, h3391, h4084, reducedSource1766] using sourceEq2118 B hB

theorem rowSound1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1766 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1766, numericCheck1766, reducedZero1766 B hB hF, mul_zero]

theorem reducedZero1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1767 (mixedVector B) = 0 := by
  have h1347 : mixedVector B (Sum.inr 1347) = Sparse.eval nodeValue1347 (mixedVector B) := by
    change mixedMoment B node1347 node1347Labels = _
    exact sound1347 B hB hF
  have h2831 : mixedVector B (Sum.inr 2831) = Sparse.eval nodeValue2831 (mixedVector B) := by
    change mixedMoment B node2831 node2831Labels = _
    exact sound2831 B hB hF
  have h2902 : mixedVector B (Sum.inr 2902) = Sparse.eval nodeValue2902 (mixedVector B) := by
    change mixedMoment B node2902 node2902Labels = _
    exact sound2902 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2964 : mixedVector B (Sum.inr 2964) = Sparse.eval nodeValue2964 (mixedVector B) := by
    change mixedMoment B node2964 node2964Labels = _
    exact sound2964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2119, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1347, h2831, h2902, h2942, h2954, h2964, h4091, reducedSource1767] using sourceEq2119 B hB

theorem rowSound1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1767 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1767, numericCheck1767, reducedZero1767 B hB hF, mul_zero]

theorem reducedZero1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1768 (mixedVector B) = 0 := by
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2668 : mixedVector B (Sum.inr 2668) = Sparse.eval nodeValue2668 (mixedVector B) := by
    change mixedMoment B node2668 node2668Labels = _
    exact sound2668 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2674 : mixedVector B (Sum.inr 2674) = Sparse.eval nodeValue2674 (mixedVector B) := by
    change mixedMoment B node2674 node2674Labels = _
    exact sound2674 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2120, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2584, h2668, h2670, h2674, h2681, h3478, h4082, reducedSource1768] using sourceEq2120 B hB

theorem rowSound1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1768 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1768, numericCheck1768, reducedZero1768 B hB hF, mul_zero]

theorem reducedZero1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1769 (mixedVector B) = 0 := by
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3614 : mixedVector B (Sum.inr 3614) = Sparse.eval nodeValue3614 (mixedVector B) := by
    change mixedMoment B node3614 node3614Labels = _
    exact sound3614 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2121, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2670, h3478, h3516, h3522, h3538, h3614, h4082, reducedSource1769] using sourceEq2121 B hB

theorem rowSound1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1769 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1769, numericCheck1769, reducedZero1769 B hB hF, mul_zero]

theorem reducedZero1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1770 (mixedVector B) = 0 := by
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2122, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2347, h2423, h2431, h2488, h2545, h3719, h4092, reducedSource1770] using sourceEq2122 B hB

theorem rowSound1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1770 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1770, numericCheck1770, reducedZero1770 B hB hF, mul_zero]

theorem reducedZero1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1771 (mixedVector B) = 0 := by
  have h1151 : mixedVector B (Sum.inr 1151) = Sparse.eval nodeValue1151 (mixedVector B) := by
    change mixedMoment B node1151 node1151Labels = _
    exact sound1151 B hB hF
  have h2350 : mixedVector B (Sum.inr 2350) = Sparse.eval nodeValue2350 (mixedVector B) := by
    change mixedMoment B node2350 node2350Labels = _
    exact sound2350 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2123, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1151, h2350, h2431, h2545, h2553, h2557, h4092, reducedSource1771] using sourceEq2123 B hB

theorem rowSound1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1771 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1771, numericCheck1771, reducedZero1771 B hB hF, mul_zero]

theorem reducedZero1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1772 (mixedVector B) = 0 := by
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h2824 : mixedVector B (Sum.inr 2824) = Sparse.eval nodeValue2824 (mixedVector B) := by
    change mixedMoment B node2824 node2824Labels = _
    exact sound2824 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2124, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1330, h2824, h2896, h2916, h2924, h2928, h4091, reducedSource1772] using sourceEq2124 B hB

theorem rowSound1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1772 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1772, numericCheck1772, reducedZero1772 B hB hF, mul_zero]

theorem reducedZero1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1773 (mixedVector B) = 0 := by
  have h2349 : mixedVector B (Sum.inr 2349) = Sparse.eval nodeValue2349 (mixedVector B) := by
    change mixedMoment B node2349 node2349Labels = _
    exact sound2349 B hB hF
  have h2890 : mixedVector B (Sum.inr 2890) = Sparse.eval nodeValue2890 (mixedVector B) := by
    change mixedMoment B node2890 node2890Labels = _
    exact sound2890 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2125, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2349, h2890, h2896, h2916, h3721, h4091, reducedSource1773] using sourceEq2125 B hB

theorem rowSound1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1773 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1773, numericCheck1773, reducedZero1773 B hB hF, mul_zero]

theorem reducedZero1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1774 (mixedVector B) = 0 := by
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h3430 : mixedVector B (Sum.inr 3430) = Sparse.eval nodeValue3430 (mixedVector B) := by
    change mixedMoment B node3430 node3430Labels = _
    exact sound3430 B hB hF
  have h3433 : mixedVector B (Sum.inr 3433) = Sparse.eval nodeValue3433 (mixedVector B) := by
    change mixedMoment B node3433 node3433Labels = _
    exact sound3433 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2126, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2534, h3430, h3433, h3478, h3516, h4082, reducedSource1774] using sourceEq2126 B hB

theorem rowSound1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1774 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1774, numericCheck1774, reducedZero1774 B hB hF, mul_zero]

theorem reducedZero1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1775 (mixedVector B) = 0 := by
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2432 : mixedVector B (Sum.inr 2432) = Sparse.eval nodeValue2432 (mixedVector B) := by
    change mixedMoment B node2432 node2432Labels = _
    exact sound2432 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h2546 : mixedVector B (Sum.inr 2546) = Sparse.eval nodeValue2546 (mixedVector B) := by
    change mixedMoment B node2546 node2546Labels = _
    exact sound2546 B hB hF
  have h3779 : mixedVector B (Sum.inr 3779) = Sparse.eval nodeValue3779 (mixedVector B) := by
    change mixedMoment B node3779 node3779Labels = _
    exact sound3779 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2129, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2422, h2432, h2489, h2546, h3779, h4091, reducedSource1775] using sourceEq2129 B hB

theorem rowSound1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1775 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1775, numericCheck1775, reducedZero1775 B hB hF, mul_zero]

theorem sourceRowsAt1760 : MixedData.sourceRows (1760 : Fin 2425) =
    MixedData.row1760 := by decide +kernel

theorem sourceRowsAt1761 : MixedData.sourceRows (1761 : Fin 2425) =
    MixedData.row1761 := by decide +kernel

theorem sourceRowsAt1762 : MixedData.sourceRows (1762 : Fin 2425) =
    MixedData.row1762 := by decide +kernel

theorem sourceRowsAt1763 : MixedData.sourceRows (1763 : Fin 2425) =
    MixedData.row1763 := by decide +kernel

theorem sourceRowsAt1764 : MixedData.sourceRows (1764 : Fin 2425) =
    MixedData.row1764 := by decide +kernel

theorem sourceRowsAt1765 : MixedData.sourceRows (1765 : Fin 2425) =
    MixedData.row1765 := by decide +kernel

theorem sourceRowsAt1766 : MixedData.sourceRows (1766 : Fin 2425) =
    MixedData.row1766 := by decide +kernel

theorem sourceRowsAt1767 : MixedData.sourceRows (1767 : Fin 2425) =
    MixedData.row1767 := by decide +kernel

theorem sourceRowsAt1768 : MixedData.sourceRows (1768 : Fin 2425) =
    MixedData.row1768 := by decide +kernel

theorem sourceRowsAt1769 : MixedData.sourceRows (1769 : Fin 2425) =
    MixedData.row1769 := by decide +kernel

theorem sourceRowsAt1770 : MixedData.sourceRows (1770 : Fin 2425) =
    MixedData.row1770 := by decide +kernel

theorem sourceRowsAt1771 : MixedData.sourceRows (1771 : Fin 2425) =
    MixedData.row1771 := by decide +kernel

theorem sourceRowsAt1772 : MixedData.sourceRows (1772 : Fin 2425) =
    MixedData.row1772 := by decide +kernel

theorem sourceRowsAt1773 : MixedData.sourceRows (1773 : Fin 2425) =
    MixedData.row1773 := by decide +kernel

theorem sourceRowsAt1774 : MixedData.sourceRows (1774 : Fin 2425) =
    MixedData.row1774 := by decide +kernel

theorem sourceRowsAt1775 : MixedData.sourceRows (1775 : Fin 2425) =
    MixedData.row1775 := by decide +kernel

theorem chunkSound110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 110) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1760 ∨ k.val = 1761 ∨ k.val = 1762 ∨ k.val = 1763 ∨ k.val = 1764 ∨ k.val = 1765 ∨ k.val = 1766 ∨ k.val = 1767 ∨ k.val = 1768 ∨ k.val = 1769 ∨ k.val = 1770 ∨ k.val = 1771 ∨ k.val = 1772 ∨ k.val = 1773 ∨ k.val = 1774 ∨ k.val = 1775 := by omega
  rcases heq with h1760 | h1761 | h1762 | h1763 | h1764 | h1765 | h1766 | h1767 | h1768 | h1769 | h1770 | h1771 | h1772 | h1773 | h1774 | h1775
  · have he : k = (1760 : Fin 2425) := Fin.ext h1760
    subst k
    rw [sourceRowsAt1760]
    exact rowSound1760 B hB hF
  · have he : k = (1761 : Fin 2425) := Fin.ext h1761
    subst k
    rw [sourceRowsAt1761]
    exact rowSound1761 B hB hF
  · have he : k = (1762 : Fin 2425) := Fin.ext h1762
    subst k
    rw [sourceRowsAt1762]
    exact rowSound1762 B hB hF
  · have he : k = (1763 : Fin 2425) := Fin.ext h1763
    subst k
    rw [sourceRowsAt1763]
    exact rowSound1763 B hB hF
  · have he : k = (1764 : Fin 2425) := Fin.ext h1764
    subst k
    rw [sourceRowsAt1764]
    exact rowSound1764 B hB hF
  · have he : k = (1765 : Fin 2425) := Fin.ext h1765
    subst k
    rw [sourceRowsAt1765]
    exact rowSound1765 B hB hF
  · have he : k = (1766 : Fin 2425) := Fin.ext h1766
    subst k
    rw [sourceRowsAt1766]
    exact rowSound1766 B hB hF
  · have he : k = (1767 : Fin 2425) := Fin.ext h1767
    subst k
    rw [sourceRowsAt1767]
    exact rowSound1767 B hB hF
  · have he : k = (1768 : Fin 2425) := Fin.ext h1768
    subst k
    rw [sourceRowsAt1768]
    exact rowSound1768 B hB hF
  · have he : k = (1769 : Fin 2425) := Fin.ext h1769
    subst k
    rw [sourceRowsAt1769]
    exact rowSound1769 B hB hF
  · have he : k = (1770 : Fin 2425) := Fin.ext h1770
    subst k
    rw [sourceRowsAt1770]
    exact rowSound1770 B hB hF
  · have he : k = (1771 : Fin 2425) := Fin.ext h1771
    subst k
    rw [sourceRowsAt1771]
    exact rowSound1771 B hB hF
  · have he : k = (1772 : Fin 2425) := Fin.ext h1772
    subst k
    rw [sourceRowsAt1772]
    exact rowSound1772 B hB hF
  · have he : k = (1773 : Fin 2425) := Fin.ext h1773
    subst k
    rw [sourceRowsAt1773]
    exact rowSound1773 B hB hF
  · have he : k = (1774 : Fin 2425) := Fin.ext h1774
    subst k
    rw [sourceRowsAt1774]
    exact rowSound1774 B hB hF
  · have he : k = (1775 : Fin 2425) := Fin.ext h1775
    subst k
    rw [sourceRowsAt1775]
    exact rowSound1775 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
