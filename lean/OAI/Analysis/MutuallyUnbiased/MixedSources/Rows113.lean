import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic113
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources68

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1808 (mixedVector B) = 0 := by
  have h2799 : mixedVector B (Sum.inr 2799) = Sparse.eval nodeValue2799 (mixedVector B) := by
    change mixedMoment B node2799 node2799Labels = _
    exact sound2799 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2818 : mixedVector B (Sum.inr 2818) = Sparse.eval nodeValue2818 (mixedVector B) := by
    change mixedMoment B node2818 node2818Labels = _
    exact sound2818 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2175, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2799, h2802, h2818, h2868, h3694, h4091, reducedSource1808] using sourceEq2175 B hB

theorem rowSound1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1808 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1808, numericCheck1808, reducedZero1808 B hB hF, mul_zero]

theorem reducedZero1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1809 (mixedVector B) = 0 := by
  have h1322 : mixedVector B (Sum.inr 1322) = Sparse.eval nodeValue1322 (mixedVector B) := by
    change mixedMoment B node1322 node1322Labels = _
    exact sound1322 B hB hF
  have h2818 : mixedVector B (Sum.inr 2818) = Sparse.eval nodeValue2818 (mixedVector B) := by
    change mixedMoment B node2818 node2818Labels = _
    exact sound2818 B hB hF
  have h2849 : mixedVector B (Sum.inr 2849) = Sparse.eval nodeValue2849 (mixedVector B) := by
    change mixedMoment B node2849 node2849Labels = _
    exact sound2849 B hB hF
  have h2868 : mixedVector B (Sum.inr 2868) = Sparse.eval nodeValue2868 (mixedVector B) := by
    change mixedMoment B node2868 node2868Labels = _
    exact sound2868 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2176, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1322, h2818, h2849, h2868, h2884, h4091, reducedSource1809] using sourceEq2176 B hB

theorem rowSound1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1809 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1809, numericCheck1809, reducedZero1809 B hB hF, mul_zero]

theorem reducedZero1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1810 (mixedVector B) = 0 := by
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h2812 : mixedVector B (Sum.inr 2812) = Sparse.eval nodeValue2812 (mixedVector B) := by
    change mixedMoment B node2812 node2812Labels = _
    exact sound2812 B hB hF
  have h2821 : mixedVector B (Sum.inr 2821) = Sparse.eval nodeValue2821 (mixedVector B) := by
    change mixedMoment B node2821 node2821Labels = _
    exact sound2821 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2177, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1819, h2812, h2821, h2888, h3397, h4084, reducedSource1810] using sourceEq2177 B hB

theorem rowSound1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1810 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1810, numericCheck1810, reducedZero1810 B hB hF, mul_zero]

theorem reducedZero1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1811 (mixedVector B) = 0 := by
  have h4372 : mixedVector B (Sum.inr 4372) = Sparse.eval nodeValue4372 (mixedVector B) := by
    change mixedMoment B node4372 node4372Labels = _
    exact sound4372 B hB hF
  have h4373 : mixedVector B (Sum.inr 4373) = Sparse.eval nodeValue4373 (mixedVector B) := by
    change mixedMoment B node4373 node4373Labels = _
    exact sound4373 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4480 : mixedVector B (Sum.inr 4480) = Sparse.eval nodeValue4480 (mixedVector B) := by
    change mixedMoment B node4480 node4480Labels = _
    exact sound4480 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4965 : mixedVector B (Sum.inr 4965) = Sparse.eval nodeValue4965 (mixedVector B) := by
    change mixedMoment B node4965 node4965Labels = _
    exact sound4965 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h4979 : mixedVector B (Sum.inr 4979) = Sparse.eval nodeValue4979 (mixedVector B) := by
    change mixedMoment B node4979 node4979Labels = _
    exact sound4979 B hB hF
  have h5044 : mixedVector B (Sum.inr 5044) = Sparse.eval nodeValue5044 (mixedVector B) := by
    change mixedMoment B node5044 node5044Labels = _
    exact sound5044 B hB hF
  have h5090 : mixedVector B (Sum.inr 5090) = Sparse.eval nodeValue5090 (mixedVector B) := by
    change mixedMoment B node5090 node5090Labels = _
    exact sound5090 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5199 : mixedVector B (Sum.inr 5199) = Sparse.eval nodeValue5199 (mixedVector B) := by
    change mixedMoment B node5199 node5199Labels = _
    exact sound5199 B hB hF
  have h5201 : mixedVector B (Sum.inr 5201) = Sparse.eval nodeValue5201 (mixedVector B) := by
    change mixedMoment B node5201 node5201Labels = _
    exact sound5201 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5300 : mixedVector B (Sum.inr 5300) = Sparse.eval nodeValue5300 (mixedVector B) := by
    change mixedMoment B node5300 node5300Labels = _
    exact sound5300 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  have h5475 : mixedVector B (Sum.inr 5475) = Sparse.eval nodeValue5475 (mixedVector B) := by
    change mixedMoment B node5475 node5475Labels = _
    exact sound5475 B hB hF
  simpa only [sourceForm2180, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4372, h4373, h4374, h4480, h4944, h4953, h4965, h4977, h4979, h5044, h5090, h5109, h5199, h5201, h5204, h5300, h5302, h5368, h5371, h5413, h5475, reducedSource1811] using sourceEq2180 B hB

theorem rowSound1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1811 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1811, numericCheck1811, reducedZero1811 B hB hF, mul_zero]

theorem reducedZero1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1812 (mixedVector B) = 0 := by
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3474 : mixedVector B (Sum.inr 3474) = Sparse.eval nodeValue3474 (mixedVector B) := by
    change mixedMoment B node3474 node3474Labels = _
    exact sound3474 B hB hF
  have h3475 : mixedVector B (Sum.inr 3475) = Sparse.eval nodeValue3475 (mixedVector B) := by
    change mixedMoment B node3475 node3475Labels = _
    exact sound3475 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3579 : mixedVector B (Sum.inr 3579) = Sparse.eval nodeValue3579 (mixedVector B) := by
    change mixedMoment B node3579 node3579Labels = _
    exact sound3579 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h3596 : mixedVector B (Sum.inr 3596) = Sparse.eval nodeValue3596 (mixedVector B) := by
    change mixedMoment B node3596 node3596Labels = _
    exact sound3596 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3767 : mixedVector B (Sum.inr 3767) = Sparse.eval nodeValue3767 (mixedVector B) := by
    change mixedMoment B node3767 node3767Labels = _
    exact sound3767 B hB hF
  have h3775 : mixedVector B (Sum.inr 3775) = Sparse.eval nodeValue3775 (mixedVector B) := by
    change mixedMoment B node3775 node3775Labels = _
    exact sound3775 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  simpa only [sourceForm2181, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1734, h1735, h1740, h1748, h3413, h3423, h3474, h3475, h3480, h3486, h3578, h3579, h3584, h3595, h3596, h3624, h3626, h3767, h3775, h3817, h3963, reducedSource1812] using sourceEq2181 B hB

theorem rowSound1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1812 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1812, numericCheck1812, reducedZero1812 B hB hF, mul_zero]

theorem reducedZero1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1813 (mixedVector B) = 0 := by
  have h2345 : mixedVector B (Sum.inr 2345) = Sparse.eval nodeValue2345 (mixedVector B) := by
    change mixedMoment B node2345 node2345Labels = _
    exact sound2345 B hB hF
  have h2813 : mixedVector B (Sum.inr 2813) = Sparse.eval nodeValue2813 (mixedVector B) := by
    change mixedMoment B node2813 node2813Labels = _
    exact sound2813 B hB hF
  have h2820 : mixedVector B (Sum.inr 2820) = Sparse.eval nodeValue2820 (mixedVector B) := by
    change mixedMoment B node2820 node2820Labels = _
    exact sound2820 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h3707 : mixedVector B (Sum.inr 3707) = Sparse.eval nodeValue3707 (mixedVector B) := by
    change mixedMoment B node3707 node3707Labels = _
    exact sound3707 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2182, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2345, h2813, h2820, h2889, h3707, h4092, reducedSource1813] using sourceEq2182 B hB

theorem rowSound1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1813 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1813, numericCheck1813, reducedZero1813 B hB hF, mul_zero]

theorem reducedZero1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1814 (mixedVector B) = 0 := by
  have h2533 : mixedVector B (Sum.inr 2533) = Sparse.eval nodeValue2533 (mixedVector B) := by
    change mixedMoment B node2533 node2533Labels = _
    exact sound2533 B hB hF
  have h3679 : mixedVector B (Sum.inr 3679) = Sparse.eval nodeValue3679 (mixedVector B) := by
    change mixedMoment B node3679 node3679Labels = _
    exact sound3679 B hB hF
  have h3681 : mixedVector B (Sum.inr 3681) = Sparse.eval nodeValue3681 (mixedVector B) := by
    change mixedMoment B node3681 node3681Labels = _
    exact sound3681 B hB hF
  have h3695 : mixedVector B (Sum.inr 3695) = Sparse.eval nodeValue3695 (mixedVector B) := by
    change mixedMoment B node3695 node3695Labels = _
    exact sound3695 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2189, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2533, h3679, h3681, h3695, h3795, h3832, h4088, reducedSource1814] using sourceEq2189 B hB

theorem rowSound1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1814 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1814, numericCheck1814, reducedZero1814 B hB hF, mul_zero]

theorem reducedZero1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1815 (mixedVector B) = 0 := by
  have h4533 : mixedVector B (Sum.inr 4533) = Sparse.eval nodeValue4533 (mixedVector B) := by
    change mixedMoment B node4533 node4533Labels = _
    exact sound4533 B hB hF
  have h4534 : mixedVector B (Sum.inr 4534) = Sparse.eval nodeValue4534 (mixedVector B) := by
    change mixedMoment B node4534 node4534Labels = _
    exact sound4534 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4556 : mixedVector B (Sum.inr 4556) = Sparse.eval nodeValue4556 (mixedVector B) := by
    change mixedMoment B node4556 node4556Labels = _
    exact sound4556 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4929 : mixedVector B (Sum.inr 4929) = Sparse.eval nodeValue4929 (mixedVector B) := by
    change mixedMoment B node4929 node4929Labels = _
    exact sound4929 B hB hF
  have h4934 : mixedVector B (Sum.inr 4934) = Sparse.eval nodeValue4934 (mixedVector B) := by
    change mixedMoment B node4934 node4934Labels = _
    exact sound4934 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4955 : mixedVector B (Sum.inr 4955) = Sparse.eval nodeValue4955 (mixedVector B) := by
    change mixedMoment B node4955 node4955Labels = _
    exact sound4955 B hB hF
  have h4956 : mixedVector B (Sum.inr 4956) = Sparse.eval nodeValue4956 (mixedVector B) := by
    change mixedMoment B node4956 node4956Labels = _
    exact sound4956 B hB hF
  have h4959 : mixedVector B (Sum.inr 4959) = Sparse.eval nodeValue4959 (mixedVector B) := by
    change mixedMoment B node4959 node4959Labels = _
    exact sound4959 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5112 : mixedVector B (Sum.inr 5112) = Sparse.eval nodeValue5112 (mixedVector B) := by
    change mixedMoment B node5112 node5112Labels = _
    exact sound5112 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5135 : mixedVector B (Sum.inr 5135) = Sparse.eval nodeValue5135 (mixedVector B) := by
    change mixedMoment B node5135 node5135Labels = _
    exact sound5135 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  simpa only [sourceForm2190, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4533, h4534, h4535, h4556, h4612, h4929, h4934, h4943, h4955, h4956, h4959, h4966, h4972, h5036, h5075, h5111, h5112, h5134, h5135, h5139, h5141, h5163, h5164, h5274, h5275, h5351, h5355, h5367, h5409, h5428, reducedSource1815] using sourceEq2190 B hB

theorem rowSound1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1815 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1815, numericCheck1815, reducedZero1815 B hB hF, mul_zero]

theorem reducedZero1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1816 (mixedVector B) = 0 := by
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h1120 : mixedVector B (Sum.inr 1120) = Sparse.eval nodeValue1120 (mixedVector B) := by
    change mixedMoment B node1120 node1120Labels = _
    exact sound1120 B hB hF
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h1274 : mixedVector B (Sum.inr 1274) = Sparse.eval nodeValue1274 (mixedVector B) := by
    change mixedMoment B node1274 node1274Labels = _
    exact sound1274 B hB hF
  have h2349 : mixedVector B (Sum.inr 2349) = Sparse.eval nodeValue2349 (mixedVector B) := by
    change mixedMoment B node2349 node2349Labels = _
    exact sound2349 B hB hF
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2358 : mixedVector B (Sum.inr 2358) = Sparse.eval nodeValue2358 (mixedVector B) := by
    change mixedMoment B node2358 node2358Labels = _
    exact sound2358 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2819 : mixedVector B (Sum.inr 2819) = Sparse.eval nodeValue2819 (mixedVector B) := by
    change mixedMoment B node2819 node2819Labels = _
    exact sound2819 B hB hF
  have h2823 : mixedVector B (Sum.inr 2823) = Sparse.eval nodeValue2823 (mixedVector B) := by
    change mixedMoment B node2823 node2823Labels = _
    exact sound2823 B hB hF
  have h2828 : mixedVector B (Sum.inr 2828) = Sparse.eval nodeValue2828 (mixedVector B) := by
    change mixedMoment B node2828 node2828Labels = _
    exact sound2828 B hB hF
  have h2898 : mixedVector B (Sum.inr 2898) = Sparse.eval nodeValue2898 (mixedVector B) := by
    change mixedMoment B node2898 node2898Labels = _
    exact sound2898 B hB hF
  have h2903 : mixedVector B (Sum.inr 2903) = Sparse.eval nodeValue2903 (mixedVector B) := by
    change mixedMoment B node2903 node2903Labels = _
    exact sound2903 B hB hF
  have h2934 : mixedVector B (Sum.inr 2934) = Sparse.eval nodeValue2934 (mixedVector B) := by
    change mixedMoment B node2934 node2934Labels = _
    exact sound2934 B hB hF
  have h2937 : mixedVector B (Sum.inr 2937) = Sparse.eval nodeValue2937 (mixedVector B) := by
    change mixedMoment B node2937 node2937Labels = _
    exact sound2937 B hB hF
  have h2939 : mixedVector B (Sum.inr 2939) = Sparse.eval nodeValue2939 (mixedVector B) := by
    change mixedMoment B node2939 node2939Labels = _
    exact sound2939 B hB hF
  have h2943 : mixedVector B (Sum.inr 2943) = Sparse.eval nodeValue2943 (mixedVector B) := by
    change mixedMoment B node2943 node2943Labels = _
    exact sound2943 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h2961 : mixedVector B (Sum.inr 2961) = Sparse.eval nodeValue2961 (mixedVector B) := by
    change mixedMoment B node2961 node2961Labels = _
    exact sound2961 B hB hF
  have h3006 : mixedVector B (Sum.inr 3006) = Sparse.eval nodeValue3006 (mixedVector B) := by
    change mixedMoment B node3006 node3006Labels = _
    exact sound3006 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h3728 : mixedVector B (Sum.inr 3728) = Sparse.eval nodeValue3728 (mixedVector B) := by
    change mixedMoment B node3728 node3728Labels = _
    exact sound3728 B hB hF
  have h3937 : mixedVector B (Sum.inr 3937) = Sparse.eval nodeValue3937 (mixedVector B) := by
    change mixedMoment B node3937 node3937Labels = _
    exact sound3937 B hB hF
  have h3941 : mixedVector B (Sum.inr 3941) = Sparse.eval nodeValue3941 (mixedVector B) := by
    change mixedMoment B node3941 node3941Labels = _
    exact sound3941 B hB hF
  have h4003 : mixedVector B (Sum.inr 4003) = Sparse.eval nodeValue4003 (mixedVector B) := by
    change mixedMoment B node4003 node4003Labels = _
    exact sound4003 B hB hF
  have h4035 : mixedVector B (Sum.inr 4035) = Sparse.eval nodeValue4035 (mixedVector B) := by
    change mixedMoment B node4035 node4035Labels = _
    exact sound4035 B hB hF
  simpa only [sourceForm2191, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1117, h1119, h1120, h1141, h1274, h2349, h2352, h2358, h2618, h2801, h2802, h2819, h2823, h2828, h2898, h2903, h2934, h2937, h2939, h2943, h2955, h2961, h3006, h3110, h3112, h3728, h3937, h3941, h4003, h4035, reducedSource1816] using sourceEq2191 B hB

theorem rowSound1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1816 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1816, numericCheck1816, reducedZero1816 B hB hF, mul_zero]

theorem reducedZero1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1817 (mixedVector B) = 0 := by
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3271 : mixedVector B (Sum.inr 3271) = Sparse.eval nodeValue3271 (mixedVector B) := by
    change mixedMoment B node3271 node3271Labels = _
    exact sound3271 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3403 : mixedVector B (Sum.inr 3403) = Sparse.eval nodeValue3403 (mixedVector B) := by
    change mixedMoment B node3403 node3403Labels = _
    exact sound3403 B hB hF
  have h3411 : mixedVector B (Sum.inr 3411) = Sparse.eval nodeValue3411 (mixedVector B) := by
    change mixedMoment B node3411 node3411Labels = _
    exact sound3411 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3450 : mixedVector B (Sum.inr 3450) = Sparse.eval nodeValue3450 (mixedVector B) := by
    change mixedMoment B node3450 node3450Labels = _
    exact sound3450 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h3512 : mixedVector B (Sum.inr 3512) = Sparse.eval nodeValue3512 (mixedVector B) := by
    change mixedMoment B node3512 node3512Labels = _
    exact sound3512 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3515 : mixedVector B (Sum.inr 3515) = Sparse.eval nodeValue3515 (mixedVector B) := by
    change mixedMoment B node3515 node3515Labels = _
    exact sound3515 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3556 : mixedVector B (Sum.inr 3556) = Sparse.eval nodeValue3556 (mixedVector B) := by
    change mixedMoment B node3556 node3556Labels = _
    exact sound3556 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  simpa only [sourceForm2192, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3267, h3268, h3271, h3272, h3301, h3403, h3411, h3415, h3450, h3457, h3468, h3485, h3508, h3510, h3512, h3514, h3515, h3522, h3523, h3547, h3548, h3555, h3556, h3564, h3565, h3757, h3766, h3770, h3807, h3845, reducedSource1817] using sourceEq2192 B hB

theorem rowSound1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1817 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1817, numericCheck1817, reducedZero1817 B hB hF, mul_zero]

theorem reducedZero1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1818 (mixedVector B) = 0 := by
  have h2325 : mixedVector B (Sum.inr 2325) = Sparse.eval nodeValue2325 (mixedVector B) := by
    change mixedMoment B node2325 node2325Labels = _
    exact sound2325 B hB hF
  have h2348 : mixedVector B (Sum.inr 2348) = Sparse.eval nodeValue2348 (mixedVector B) := by
    change mixedMoment B node2348 node2348Labels = _
    exact sound2348 B hB hF
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2356 : mixedVector B (Sum.inr 2356) = Sparse.eval nodeValue2356 (mixedVector B) := by
    change mixedMoment B node2356 node2356Labels = _
    exact sound2356 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2193, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2325, h2348, h2352, h2356, h2561, h3693, h4092, reducedSource1818] using sourceEq2193 B hB

theorem rowSound1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1818 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1818, numericCheck1818, reducedZero1818 B hB hF, mul_zero]

theorem reducedZero1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1819 (mixedVector B) = 0 := by
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h2348 : mixedVector B (Sum.inr 2348) = Sparse.eval nodeValue2348 (mixedVector B) := by
    change mixedMoment B node2348 node2348Labels = _
    exact sound2348 B hB hF
  have h2428 : mixedVector B (Sum.inr 2428) = Sparse.eval nodeValue2428 (mixedVector B) := by
    change mixedMoment B node2428 node2428Labels = _
    exact sound2428 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2194, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1149, h2348, h2428, h2553, h2554, h2561, h4092, reducedSource1819] using sourceEq2194 B hB

theorem rowSound1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1819 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1819, numericCheck1819, reducedZero1819 B hB hF, mul_zero]

theorem reducedZero1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1820 (mixedVector B) = 0 := by
  have h2319 : mixedVector B (Sum.inr 2319) = Sparse.eval nodeValue2319 (mixedVector B) := by
    change mixedMoment B node2319 node2319Labels = _
    exact sound2319 B hB hF
  have h2524 : mixedVector B (Sum.inr 2524) = Sparse.eval nodeValue2524 (mixedVector B) := by
    change mixedMoment B node2524 node2524Labels = _
    exact sound2524 B hB hF
  have h2525 : mixedVector B (Sum.inr 2525) = Sparse.eval nodeValue2525 (mixedVector B) := by
    change mixedMoment B node2525 node2525Labels = _
    exact sound2525 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h3689 : mixedVector B (Sum.inr 3689) = Sparse.eval nodeValue3689 (mixedVector B) := by
    change mixedMoment B node3689 node3689Labels = _
    exact sound3689 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2195, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2319, h2524, h2525, h2561, h3689, h4092, reducedSource1820] using sourceEq2195 B hB

theorem rowSound1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1820 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1820, numericCheck1820, reducedZero1820 B hB hF, mul_zero]

theorem reducedZero1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1821 (mixedVector B) = 0 := by
  have h1160 : mixedVector B (Sum.inr 1160) = Sparse.eval nodeValue1160 (mixedVector B) := by
    change mixedMoment B node1160 node1160Labels = _
    exact sound1160 B hB hF
  have h2356 : mixedVector B (Sum.inr 2356) = Sparse.eval nodeValue2356 (mixedVector B) := by
    change mixedMoment B node2356 node2356Labels = _
    exact sound2356 B hB hF
  have h2525 : mixedVector B (Sum.inr 2525) = Sparse.eval nodeValue2525 (mixedVector B) := by
    change mixedMoment B node2525 node2525Labels = _
    exact sound2525 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2196, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1160, h2356, h2525, h2561, h2590, h2591, h4092, reducedSource1821] using sourceEq2196 B hB

theorem rowSound1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1821 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1821, numericCheck1821, reducedZero1821 B hB hF, mul_zero]

theorem reducedZero1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1822 (mixedVector B) = 0 := by
  have h4323 : mixedVector B (Sum.inr 4323) = Sparse.eval nodeValue4323 (mixedVector B) := by
    change mixedMoment B node4323 node4323Labels = _
    exact sound4323 B hB hF
  have h4324 : mixedVector B (Sum.inr 4324) = Sparse.eval nodeValue4324 (mixedVector B) := by
    change mixedMoment B node4324 node4324Labels = _
    exact sound4324 B hB hF
  have h4325 : mixedVector B (Sum.inr 4325) = Sparse.eval nodeValue4325 (mixedVector B) := by
    change mixedMoment B node4325 node4325Labels = _
    exact sound4325 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4902 : mixedVector B (Sum.inr 4902) = Sparse.eval nodeValue4902 (mixedVector B) := by
    change mixedMoment B node4902 node4902Labels = _
    exact sound4902 B hB hF
  have h4907 : mixedVector B (Sum.inr 4907) = Sparse.eval nodeValue4907 (mixedVector B) := by
    change mixedMoment B node4907 node4907Labels = _
    exact sound4907 B hB hF
  have h4913 : mixedVector B (Sum.inr 4913) = Sparse.eval nodeValue4913 (mixedVector B) := by
    change mixedMoment B node4913 node4913Labels = _
    exact sound4913 B hB hF
  have h4928 : mixedVector B (Sum.inr 4928) = Sparse.eval nodeValue4928 (mixedVector B) := by
    change mixedMoment B node4928 node4928Labels = _
    exact sound4928 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4987 : mixedVector B (Sum.inr 4987) = Sparse.eval nodeValue4987 (mixedVector B) := by
    change mixedMoment B node4987 node4987Labels = _
    exact sound4987 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  simpa only [sourceForm2197, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4323, h4324, h4325, h4349, h4404, h4631, h4637, h4644, h4804, h4902, h4907, h4913, h4928, h4946, h4987, h5003, h5036, h5050, h5075, h5134, h5137, h5168, h5169, h5258, h5259, h5352, h5356, h5368, h5434, h5483, reducedSource1822] using sourceEq2197 B hB

theorem rowSound1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1822 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1822, numericCheck1822, reducedZero1822 B hB hF, mul_zero]

theorem reducedZero1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1823 (mixedVector B) = 0 := by
  have h2541 : mixedVector B (Sum.inr 2541) = Sparse.eval nodeValue2541 (mixedVector B) := by
    change mixedMoment B node2541 node2541Labels = _
    exact sound2541 B hB hF
  have h3646 : mixedVector B (Sum.inr 3646) = Sparse.eval nodeValue3646 (mixedVector B) := by
    change mixedMoment B node3646 node3646Labels = _
    exact sound3646 B hB hF
  have h3650 : mixedVector B (Sum.inr 3650) = Sparse.eval nodeValue3650 (mixedVector B) := by
    change mixedMoment B node3650 node3650Labels = _
    exact sound3650 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2203, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2541, h3646, h3650, h3757, h4088, reducedSource1823] using sourceEq2203 B hB

theorem rowSound1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1823 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1823, numericCheck1823, reducedZero1823 B hB hF, mul_zero]

theorem sourceRowsAt1808 : MixedData.sourceRows (1808 : Fin 2425) =
    MixedData.row1808 := by decide +kernel

theorem sourceRowsAt1809 : MixedData.sourceRows (1809 : Fin 2425) =
    MixedData.row1809 := by decide +kernel

theorem sourceRowsAt1810 : MixedData.sourceRows (1810 : Fin 2425) =
    MixedData.row1810 := by decide +kernel

theorem sourceRowsAt1811 : MixedData.sourceRows (1811 : Fin 2425) =
    MixedData.row1811 := by decide +kernel

theorem sourceRowsAt1812 : MixedData.sourceRows (1812 : Fin 2425) =
    MixedData.row1812 := by decide +kernel

theorem sourceRowsAt1813 : MixedData.sourceRows (1813 : Fin 2425) =
    MixedData.row1813 := by decide +kernel

theorem sourceRowsAt1814 : MixedData.sourceRows (1814 : Fin 2425) =
    MixedData.row1814 := by decide +kernel

theorem sourceRowsAt1815 : MixedData.sourceRows (1815 : Fin 2425) =
    MixedData.row1815 := by decide +kernel

theorem sourceRowsAt1816 : MixedData.sourceRows (1816 : Fin 2425) =
    MixedData.row1816 := by decide +kernel

theorem sourceRowsAt1817 : MixedData.sourceRows (1817 : Fin 2425) =
    MixedData.row1817 := by decide +kernel

theorem sourceRowsAt1818 : MixedData.sourceRows (1818 : Fin 2425) =
    MixedData.row1818 := by decide +kernel

theorem sourceRowsAt1819 : MixedData.sourceRows (1819 : Fin 2425) =
    MixedData.row1819 := by decide +kernel

theorem sourceRowsAt1820 : MixedData.sourceRows (1820 : Fin 2425) =
    MixedData.row1820 := by decide +kernel

theorem sourceRowsAt1821 : MixedData.sourceRows (1821 : Fin 2425) =
    MixedData.row1821 := by decide +kernel

theorem sourceRowsAt1822 : MixedData.sourceRows (1822 : Fin 2425) =
    MixedData.row1822 := by decide +kernel

theorem sourceRowsAt1823 : MixedData.sourceRows (1823 : Fin 2425) =
    MixedData.row1823 := by decide +kernel

theorem chunkSound113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 113) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1808 ∨ k.val = 1809 ∨ k.val = 1810 ∨ k.val = 1811 ∨ k.val = 1812 ∨ k.val = 1813 ∨ k.val = 1814 ∨ k.val = 1815 ∨ k.val = 1816 ∨ k.val = 1817 ∨ k.val = 1818 ∨ k.val = 1819 ∨ k.val = 1820 ∨ k.val = 1821 ∨ k.val = 1822 ∨ k.val = 1823 := by omega
  rcases heq with h1808 | h1809 | h1810 | h1811 | h1812 | h1813 | h1814 | h1815 | h1816 | h1817 | h1818 | h1819 | h1820 | h1821 | h1822 | h1823
  · have he : k = (1808 : Fin 2425) := Fin.ext h1808
    subst k
    rw [sourceRowsAt1808]
    exact rowSound1808 B hB hF
  · have he : k = (1809 : Fin 2425) := Fin.ext h1809
    subst k
    rw [sourceRowsAt1809]
    exact rowSound1809 B hB hF
  · have he : k = (1810 : Fin 2425) := Fin.ext h1810
    subst k
    rw [sourceRowsAt1810]
    exact rowSound1810 B hB hF
  · have he : k = (1811 : Fin 2425) := Fin.ext h1811
    subst k
    rw [sourceRowsAt1811]
    exact rowSound1811 B hB hF
  · have he : k = (1812 : Fin 2425) := Fin.ext h1812
    subst k
    rw [sourceRowsAt1812]
    exact rowSound1812 B hB hF
  · have he : k = (1813 : Fin 2425) := Fin.ext h1813
    subst k
    rw [sourceRowsAt1813]
    exact rowSound1813 B hB hF
  · have he : k = (1814 : Fin 2425) := Fin.ext h1814
    subst k
    rw [sourceRowsAt1814]
    exact rowSound1814 B hB hF
  · have he : k = (1815 : Fin 2425) := Fin.ext h1815
    subst k
    rw [sourceRowsAt1815]
    exact rowSound1815 B hB hF
  · have he : k = (1816 : Fin 2425) := Fin.ext h1816
    subst k
    rw [sourceRowsAt1816]
    exact rowSound1816 B hB hF
  · have he : k = (1817 : Fin 2425) := Fin.ext h1817
    subst k
    rw [sourceRowsAt1817]
    exact rowSound1817 B hB hF
  · have he : k = (1818 : Fin 2425) := Fin.ext h1818
    subst k
    rw [sourceRowsAt1818]
    exact rowSound1818 B hB hF
  · have he : k = (1819 : Fin 2425) := Fin.ext h1819
    subst k
    rw [sourceRowsAt1819]
    exact rowSound1819 B hB hF
  · have he : k = (1820 : Fin 2425) := Fin.ext h1820
    subst k
    rw [sourceRowsAt1820]
    exact rowSound1820 B hB hF
  · have he : k = (1821 : Fin 2425) := Fin.ext h1821
    subst k
    rw [sourceRowsAt1821]
    exact rowSound1821 B hB hF
  · have he : k = (1822 : Fin 2425) := Fin.ext h1822
    subst k
    rw [sourceRowsAt1822]
    exact rowSound1822 B hB hF
  · have he : k = (1823 : Fin 2425) := Fin.ext h1823
    subst k
    rw [sourceRowsAt1823]
    exact rowSound1823 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
