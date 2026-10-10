import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources79

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2032 (mixedVector B) = 0 := by
  have h2351 : mixedVector B (Sum.inr 2351) = Sparse.eval nodeValue2351 (mixedVector B) := by
    change mixedMoment B node2351 node2351Labels = _
    exact sound2351 B hB hF
  have h3135 : mixedVector B (Sum.inr 3135) = Sparse.eval nodeValue3135 (mixedVector B) := by
    change mixedMoment B node3135 node3135Labels = _
    exact sound3135 B hB hF
  have h3709 : mixedVector B (Sum.inr 3709) = Sparse.eval nodeValue3709 (mixedVector B) := by
    change mixedMoment B node3709 node3709Labels = _
    exact sound3709 B hB hF
  have h3716 : mixedVector B (Sum.inr 3716) = Sparse.eval nodeValue3716 (mixedVector B) := by
    change mixedMoment B node3716 node3716Labels = _
    exact sound3716 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2523, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2351, h3135, h3709, h3716, h3721, h4091, reducedSource2032] using sourceEq2523 B hB

theorem rowSound2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2032 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2032, numericCheck2032, reducedZero2032 B hB hF, mul_zero]

theorem reducedZero2033 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2033 (mixedVector B) = 0 := by
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4691 : mixedVector B (Sum.inr 4691) = Sparse.eval nodeValue4691 (mixedVector B) := by
    change mixedMoment B node4691 node4691Labels = _
    exact sound4691 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h4979 : mixedVector B (Sum.inr 4979) = Sparse.eval nodeValue4979 (mixedVector B) := by
    change mixedMoment B node4979 node4979Labels = _
    exact sound4979 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5372 : mixedVector B (Sum.inr 5372) = Sparse.eval nodeValue5372 (mixedVector B) := by
    change mixedMoment B node5372 node5372Labels = _
    exact sound5372 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5449 : mixedVector B (Sum.inr 5449) = Sparse.eval nodeValue5449 (mixedVector B) := by
    change mixedMoment B node5449 node5449Labels = _
    exact sound5449 B hB hF
  simpa only [sourceForm2524, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4688, h4691, h4693, h4874, h4973, h4979, h5176, h5372, h5384, h5387, h5441, h5443, h5449, reducedSource2033] using sourceEq2524 B hB

theorem rowSound2033 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2033 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2033, numericCheck2033, reducedZero2033 B hB hF, mul_zero]

theorem reducedZero2034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2034 (mixedVector B) = 0 := by
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h1817 : mixedVector B (Sum.inr 1817) = Sparse.eval nodeValue1817 (mixedVector B) := by
    change mixedMoment B node1817 node1817Labels = _
    exact sound1817 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2820 : mixedVector B (Sum.inr 2820) = Sparse.eval nodeValue2820 (mixedVector B) := by
    change mixedMoment B node2820 node2820Labels = _
    exact sound2820 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3708 : mixedVector B (Sum.inr 3708) = Sparse.eval nodeValue3708 (mixedVector B) := by
    change mixedMoment B node3708 node3708Labels = _
    exact sound3708 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3739 : mixedVector B (Sum.inr 3739) = Sparse.eval nodeValue3739 (mixedVector B) := by
    change mixedMoment B node3739 node3739Labels = _
    exact sound3739 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  have h4037 : mixedVector B (Sum.inr 4037) = Sparse.eval nodeValue4037 (mixedVector B) := by
    change mixedMoment B node4037 node4037Labels = _
    exact sound4037 B hB hF
  simpa only [sourceForm2525, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1814, h1817, h1819, h2115, h2817, h2820, h2968, h3708, h3732, h3739, h3886, h3889, h4037, reducedSource2034] using sourceEq2525 B hB

theorem rowSound2034 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2034 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2034, numericCheck2034, reducedZero2034 B hB hF, mul_zero]

theorem reducedZero2035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2035 (mixedVector B) = 0 := by
  have h5232 : mixedVector B (Sum.inr 5232) = Sparse.eval nodeValue5232 (mixedVector B) := by
    change mixedMoment B node5232 node5232Labels = _
    exact sound5232 B hB hF
  have h5235 : mixedVector B (Sum.inr 5235) = Sparse.eval nodeValue5235 (mixedVector B) := by
    change mixedMoment B node5235 node5235Labels = _
    exact sound5235 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5297 : mixedVector B (Sum.inr 5297) = Sparse.eval nodeValue5297 (mixedVector B) := by
    change mixedMoment B node5297 node5297Labels = _
    exact sound5297 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  have h5376 : mixedVector B (Sum.inr 5376) = Sparse.eval nodeValue5376 (mixedVector B) := by
    change mixedMoment B node5376 node5376Labels = _
    exact sound5376 B hB hF
  have h5390 : mixedVector B (Sum.inr 5390) = Sparse.eval nodeValue5390 (mixedVector B) := by
    change mixedMoment B node5390 node5390Labels = _
    exact sound5390 B hB hF
  simpa only [sourceForm2526, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5232, h5235, h5238, h5297, h5355, h5371, h5376, h5390, reducedSource2035] using sourceEq2526 B hB

theorem rowSound2035 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2035 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2035, numericCheck2035, reducedZero2035 B hB hF, mul_zero]

theorem reducedZero2036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2036 (mixedVector B) = 0 := by
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4974 : mixedVector B (Sum.inr 4974) = Sparse.eval nodeValue4974 (mixedVector B) := by
    change mixedMoment B node4974 node4974Labels = _
    exact sound4974 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5373 : mixedVector B (Sum.inr 5373) = Sparse.eval nodeValue5373 (mixedVector B) := by
    change mixedMoment B node5373 node5373Labels = _
    exact sound5373 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  simpa only [sourceForm2527, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4689, h4692, h4875, h4949, h4953, h4974, h5176, h5177, h5373, h5388, h5404, h5418, h5442, h5451, reducedSource2036] using sourceEq2527 B hB

theorem rowSound2036 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2036 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2036, numericCheck2036, reducedZero2036 B hB hF, mul_zero]

theorem reducedZero2037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2037 (mixedVector B) = 0 := by
  have h1815 : mixedVector B (Sum.inr 1815) = Sparse.eval nodeValue1815 (mixedVector B) := by
    change mixedMoment B node1815 node1815Labels = _
    exact sound1815 B hB hF
  have h1818 : mixedVector B (Sum.inr 1818) = Sparse.eval nodeValue1818 (mixedVector B) := by
    change mixedMoment B node1818 node1818Labels = _
    exact sound1818 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h2341 : mixedVector B (Sum.inr 2341) = Sparse.eval nodeValue2341 (mixedVector B) := by
    change mixedMoment B node2341 node2341Labels = _
    exact sound2341 B hB hF
  have h2345 : mixedVector B (Sum.inr 2345) = Sparse.eval nodeValue2345 (mixedVector B) := by
    change mixedMoment B node2345 node2345Labels = _
    exact sound2345 B hB hF
  have h2604 : mixedVector B (Sum.inr 2604) = Sparse.eval nodeValue2604 (mixedVector B) := by
    change mixedMoment B node2604 node2604Labels = _
    exact sound2604 B hB hF
  have h2818 : mixedVector B (Sum.inr 2818) = Sparse.eval nodeValue2818 (mixedVector B) := by
    change mixedMoment B node2818 node2818Labels = _
    exact sound2818 B hB hF
  have h2969 : mixedVector B (Sum.inr 2969) = Sparse.eval nodeValue2969 (mixedVector B) := by
    change mixedMoment B node2969 node2969Labels = _
    exact sound2969 B hB hF
  have h3709 : mixedVector B (Sum.inr 3709) = Sparse.eval nodeValue3709 (mixedVector B) := by
    change mixedMoment B node3709 node3709Labels = _
    exact sound3709 B hB hF
  have h3737 : mixedVector B (Sum.inr 3737) = Sparse.eval nodeValue3737 (mixedVector B) := by
    change mixedMoment B node3737 node3737Labels = _
    exact sound3737 B hB hF
  have h3790 : mixedVector B (Sum.inr 3790) = Sparse.eval nodeValue3790 (mixedVector B) := by
    change mixedMoment B node3790 node3790Labels = _
    exact sound3790 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h3933 : mixedVector B (Sum.inr 3933) = Sparse.eval nodeValue3933 (mixedVector B) := by
    change mixedMoment B node3933 node3933Labels = _
    exact sound3933 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  simpa only [sourceForm2528, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1815, h1818, h2116, h2341, h2345, h2604, h2818, h2969, h3709, h3737, h3790, h3888, h3933, h4001, reducedSource2037] using sourceEq2528 B hB

theorem rowSound2037 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2037 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2037, numericCheck2037, reducedZero2037 B hB hF, mul_zero]

theorem reducedZero2038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2038 (mixedVector B) = 0 := by
  have h5236 : mixedVector B (Sum.inr 5236) = Sparse.eval nodeValue5236 (mixedVector B) := by
    change mixedMoment B node5236 node5236Labels = _
    exact sound5236 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5303 : mixedVector B (Sum.inr 5303) = Sparse.eval nodeValue5303 (mixedVector B) := by
    change mixedMoment B node5303 node5303Labels = _
    exact sound5303 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  have h5377 : mixedVector B (Sum.inr 5377) = Sparse.eval nodeValue5377 (mixedVector B) := by
    change mixedMoment B node5377 node5377Labels = _
    exact sound5377 B hB hF
  have h5389 : mixedVector B (Sum.inr 5389) = Sparse.eval nodeValue5389 (mixedVector B) := by
    change mixedMoment B node5389 node5389Labels = _
    exact sound5389 B hB hF
  have h5466 : mixedVector B (Sum.inr 5466) = Sparse.eval nodeValue5466 (mixedVector B) := by
    change mixedMoment B node5466 node5466Labels = _
    exact sound5466 B hB hF
  simpa only [sourceForm2529, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5236, h5238, h5303, h5355, h5356, h5371, h5377, h5389, h5466, reducedSource2038] using sourceEq2529 B hB

theorem rowSound2038 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2038 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2038, numericCheck2038, reducedZero2038 B hB hF, mul_zero]

theorem reducedZero2039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2039 (mixedVector B) = 0 := by
  have h4668 : mixedVector B (Sum.inr 4668) = Sparse.eval nodeValue4668 (mixedVector B) := by
    change mixedMoment B node4668 node4668Labels = _
    exact sound4668 B hB hF
  have h4669 : mixedVector B (Sum.inr 4669) = Sparse.eval nodeValue4669 (mixedVector B) := by
    change mixedMoment B node4669 node4669Labels = _
    exact sound4669 B hB hF
  have h4670 : mixedVector B (Sum.inr 4670) = Sparse.eval nodeValue4670 (mixedVector B) := by
    change mixedMoment B node4670 node4670Labels = _
    exact sound4670 B hB hF
  have h4690 : mixedVector B (Sum.inr 4690) = Sparse.eval nodeValue4690 (mixedVector B) := by
    change mixedMoment B node4690 node4690Labels = _
    exact sound4690 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4931 : mixedVector B (Sum.inr 4931) = Sparse.eval nodeValue4931 (mixedVector B) := by
    change mixedMoment B node4931 node4931Labels = _
    exact sound4931 B hB hF
  have h4934 : mixedVector B (Sum.inr 4934) = Sparse.eval nodeValue4934 (mixedVector B) := by
    change mixedMoment B node4934 node4934Labels = _
    exact sound4934 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h4955 : mixedVector B (Sum.inr 4955) = Sparse.eval nodeValue4955 (mixedVector B) := by
    change mixedMoment B node4955 node4955Labels = _
    exact sound4955 B hB hF
  have h4957 : mixedVector B (Sum.inr 4957) = Sparse.eval nodeValue4957 (mixedVector B) := by
    change mixedMoment B node4957 node4957Labels = _
    exact sound4957 B hB hF
  have h4959 : mixedVector B (Sum.inr 4959) = Sparse.eval nodeValue4959 (mixedVector B) := by
    change mixedMoment B node4959 node4959Labels = _
    exact sound4959 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5336 : mixedVector B (Sum.inr 5336) = Sparse.eval nodeValue5336 (mixedVector B) := by
    change mixedMoment B node5336 node5336Labels = _
    exact sound5336 B hB hF
  have h5339 : mixedVector B (Sum.inr 5339) = Sparse.eval nodeValue5339 (mixedVector B) := by
    change mixedMoment B node5339 node5339Labels = _
    exact sound5339 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5385 : mixedVector B (Sum.inr 5385) = Sparse.eval nodeValue5385 (mixedVector B) := by
    change mixedMoment B node5385 node5385Labels = _
    exact sound5385 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  simpa only [sourceForm2532, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4668, h4669, h4670, h4690, h4856, h4931, h4934, h4949, h4955, h4957, h4959, h4966, h4973, h5080, h5141, h5188, h5336, h5339, h5351, h5353, h5367, h5370, h5378, h5379, h5384, h5385, h5409, h5411, h5428, h5446, reducedSource2039] using sourceEq2532 B hB

theorem rowSound2039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2039 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2039, numericCheck2039, reducedZero2039 B hB hF, mul_zero]

theorem reducedZero2040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2040 (mixedVector B) = 0 := by
  have h1794 : mixedVector B (Sum.inr 1794) = Sparse.eval nodeValue1794 (mixedVector B) := by
    change mixedMoment B node1794 node1794Labels = _
    exact sound1794 B hB hF
  have h1795 : mixedVector B (Sum.inr 1795) = Sparse.eval nodeValue1795 (mixedVector B) := by
    change mixedMoment B node1795 node1795Labels = _
    exact sound1795 B hB hF
  have h1796 : mixedVector B (Sum.inr 1796) = Sparse.eval nodeValue1796 (mixedVector B) := by
    change mixedMoment B node1796 node1796Labels = _
    exact sound1796 B hB hF
  have h1816 : mixedVector B (Sum.inr 1816) = Sparse.eval nodeValue1816 (mixedVector B) := by
    change mixedMoment B node1816 node1816Labels = _
    exact sound1816 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2350 : mixedVector B (Sum.inr 2350) = Sparse.eval nodeValue2350 (mixedVector B) := by
    change mixedMoment B node2350 node2350Labels = _
    exact sound2350 B hB hF
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2359 : mixedVector B (Sum.inr 2359) = Sparse.eval nodeValue2359 (mixedVector B) := by
    change mixedMoment B node2359 node2359Labels = _
    exact sound2359 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2819 : mixedVector B (Sum.inr 2819) = Sparse.eval nodeValue2819 (mixedVector B) := by
    change mixedMoment B node2819 node2819Labels = _
    exact sound2819 B hB hF
  have h2824 : mixedVector B (Sum.inr 2824) = Sparse.eval nodeValue2824 (mixedVector B) := by
    change mixedMoment B node2824 node2824Labels = _
    exact sound2824 B hB hF
  have h2829 : mixedVector B (Sum.inr 2829) = Sparse.eval nodeValue2829 (mixedVector B) := by
    change mixedMoment B node2829 node2829Labels = _
    exact sound2829 B hB hF
  have h2943 : mixedVector B (Sum.inr 2943) = Sparse.eval nodeValue2943 (mixedVector B) := by
    change mixedMoment B node2943 node2943Labels = _
    exact sound2943 B hB hF
  have h2990 : mixedVector B (Sum.inr 2990) = Sparse.eval nodeValue2990 (mixedVector B) := by
    change mixedMoment B node2990 node2990Labels = _
    exact sound2990 B hB hF
  have h3710 : mixedVector B (Sum.inr 3710) = Sparse.eval nodeValue3710 (mixedVector B) := by
    change mixedMoment B node3710 node3710Labels = _
    exact sound3710 B hB hF
  have h3711 : mixedVector B (Sum.inr 3711) = Sparse.eval nodeValue3711 (mixedVector B) := by
    change mixedMoment B node3711 node3711Labels = _
    exact sound3711 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3727 : mixedVector B (Sum.inr 3727) = Sparse.eval nodeValue3727 (mixedVector B) := by
    change mixedMoment B node3727 node3727Labels = _
    exact sound3727 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h3738 : mixedVector B (Sum.inr 3738) = Sparse.eval nodeValue3738 (mixedVector B) := by
    change mixedMoment B node3738 node3738Labels = _
    exact sound3738 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3831 : mixedVector B (Sum.inr 3831) = Sparse.eval nodeValue3831 (mixedVector B) := by
    change mixedMoment B node3831 node3831Labels = _
    exact sound3831 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
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
  simpa only [sourceForm2533, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1794, h1795, h1796, h1816, h2094, h2350, h2352, h2359, h2620, h2801, h2802, h2819, h2824, h2829, h2943, h2990, h3710, h3711, h3724, h3727, h3733, h3738, h3783, h3831, h3881, h3883, h3937, h3941, h4003, h4035, reducedSource2040] using sourceEq2533 B hB

theorem rowSound2040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2040 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2040, numericCheck2040, reducedZero2040 B hB hF, mul_zero]

theorem reducedZero2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2041 (mixedVector B) = 0 := by
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3417 : mixedVector B (Sum.inr 3417) = Sparse.eval nodeValue3417 (mixedVector B) := by
    change mixedMoment B node3417 node3417Labels = _
    exact sound3417 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3509 : mixedVector B (Sum.inr 3509) = Sparse.eval nodeValue3509 (mixedVector B) := by
    change mixedMoment B node3509 node3509Labels = _
    exact sound3509 B hB hF
  have h3512 : mixedVector B (Sum.inr 3512) = Sparse.eval nodeValue3512 (mixedVector B) := by
    change mixedMoment B node3512 node3512Labels = _
    exact sound3512 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h3754 : mixedVector B (Sum.inr 3754) = Sparse.eval nodeValue3754 (mixedVector B) := by
    change mixedMoment B node3754 node3754Labels = _
    exact sound3754 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h3760 : mixedVector B (Sum.inr 3760) = Sparse.eval nodeValue3760 (mixedVector B) := by
    change mixedMoment B node3760 node3760Labels = _
    exact sound3760 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3868 : mixedVector B (Sum.inr 3868) = Sparse.eval nodeValue3868 (mixedVector B) := by
    change mixedMoment B node3868 node3868Labels = _
    exact sound3868 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  simpa only [sourceForm2534, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2154, h2155, h2158, h2164, h2274, h3406, h3415, h3417, h3478, h3508, h3509, h3512, h3522, h3538, h3555, h3591, h3754, h3757, h3760, h3761, h3766, h3771, h3795, h3807, h3811, h3813, h3832, h3845, h3868, h3884, reducedSource2041] using sourceEq2534 B hB

theorem rowSound2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2041 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2041, numericCheck2041, reducedZero2041 B hB hF, mul_zero]

theorem reducedZero2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2042 (mixedVector B) = 0 := by
  have h2348 : mixedVector B (Sum.inr 2348) = Sparse.eval nodeValue2348 (mixedVector B) := by
    change mixedMoment B node2348 node2348Labels = _
    exact sound2348 B hB hF
  have h3133 : mixedVector B (Sum.inr 3133) = Sparse.eval nodeValue3133 (mixedVector B) := by
    change mixedMoment B node3133 node3133Labels = _
    exact sound3133 B hB hF
  have h3671 : mixedVector B (Sum.inr 3671) = Sparse.eval nodeValue3671 (mixedVector B) := by
    change mixedMoment B node3671 node3671Labels = _
    exact sound3671 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3720 : mixedVector B (Sum.inr 3720) = Sparse.eval nodeValue3720 (mixedVector B) := by
    change mixedMoment B node3720 node3720Labels = _
    exact sound3720 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2535, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2348, h3133, h3671, h3693, h3719, h3720, h4092, reducedSource2042] using sourceEq2535 B hB

theorem rowSound2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2042 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2042, numericCheck2042, reducedZero2042 B hB hF, mul_zero]

theorem reducedZero2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2043 (mixedVector B) = 0 := by
  have h2321 : mixedVector B (Sum.inr 2321) = Sparse.eval nodeValue2321 (mixedVector B) := by
    change mixedMoment B node2321 node2321Labels = _
    exact sound2321 B hB hF
  have h2798 : mixedVector B (Sum.inr 2798) = Sparse.eval nodeValue2798 (mixedVector B) := by
    change mixedMoment B node2798 node2798Labels = _
    exact sound2798 B hB hF
  have h3674 : mixedVector B (Sum.inr 3674) = Sparse.eval nodeValue3674 (mixedVector B) := by
    change mixedMoment B node3674 node3674Labels = _
    exact sound3674 B hB hF
  have h3689 : mixedVector B (Sum.inr 3689) = Sparse.eval nodeValue3689 (mixedVector B) := by
    change mixedMoment B node3689 node3689Labels = _
    exact sound3689 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2536, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2321, h2798, h3674, h3689, h3691, h3693, h4092, reducedSource2043] using sourceEq2536 B hB

theorem rowSound2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2043 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2043, numericCheck2043, reducedZero2043 B hB hF, mul_zero]

theorem reducedZero2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2044 (mixedVector B) = 0 := by
  have h2356 : mixedVector B (Sum.inr 2356) = Sparse.eval nodeValue2356 (mixedVector B) := by
    change mixedMoment B node2356 node2356Labels = _
    exact sound2356 B hB hF
  have h3138 : mixedVector B (Sum.inr 3138) = Sparse.eval nodeValue3138 (mixedVector B) := by
    change mixedMoment B node3138 node3138Labels = _
    exact sound3138 B hB hF
  have h3674 : mixedVector B (Sum.inr 3674) = Sparse.eval nodeValue3674 (mixedVector B) := by
    change mixedMoment B node3674 node3674Labels = _
    exact sound3674 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2537, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2356, h3138, h3674, h3693, h3732, h3733, h4092, reducedSource2044] using sourceEq2537 B hB

theorem rowSound2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2044 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2044, numericCheck2044, reducedZero2044 B hB hF, mul_zero]

theorem reducedZero2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2045 (mixedVector B) = 0 := by
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4703 : mixedVector B (Sum.inr 4703) = Sparse.eval nodeValue4703 (mixedVector B) := by
    change mixedMoment B node4703 node4703Labels = _
    exact sound4703 B hB hF
  have h4704 : mixedVector B (Sum.inr 4704) = Sparse.eval nodeValue4704 (mixedVector B) := by
    change mixedMoment B node4704 node4704Labels = _
    exact sound4704 B hB hF
  have h4705 : mixedVector B (Sum.inr 4705) = Sparse.eval nodeValue4705 (mixedVector B) := by
    change mixedMoment B node4705 node4705Labels = _
    exact sound4705 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4884 : mixedVector B (Sum.inr 4884) = Sparse.eval nodeValue4884 (mixedVector B) := by
    change mixedMoment B node4884 node4884Labels = _
    exact sound4884 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h4976 : mixedVector B (Sum.inr 4976) = Sparse.eval nodeValue4976 (mixedVector B) := by
    change mixedMoment B node4976 node4976Labels = _
    exact sound4976 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5206 : mixedVector B (Sum.inr 5206) = Sparse.eval nodeValue5206 (mixedVector B) := by
    change mixedMoment B node5206 node5206Labels = _
    exact sound5206 B hB hF
  have h5215 : mixedVector B (Sum.inr 5215) = Sparse.eval nodeValue5215 (mixedVector B) := by
    change mixedMoment B node5215 node5215Labels = _
    exact sound5215 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5287 : mixedVector B (Sum.inr 5287) = Sparse.eval nodeValue5287 (mixedVector B) := by
    change mixedMoment B node5287 node5287Labels = _
    exact sound5287 B hB hF
  have h5300 : mixedVector B (Sum.inr 5300) = Sparse.eval nodeValue5300 (mixedVector B) := by
    change mixedMoment B node5300 node5300Labels = _
    exact sound5300 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm2545, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4684, h4692, h4693, h4703, h4704, h4705, h4846, h4884, h4945, h4976, h5110, h5206, h5215, h5228, h5229, h5248, h5274, h5275, h5287, h5300, h5302, reducedSource2045] using sourceEq2545 B hB

theorem rowSound2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2045 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2045, numericCheck2045, reducedZero2045 B hB hF, mul_zero]

theorem reducedZero2046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2046 (mixedVector B) = 0 := by
  have h1829 : mixedVector B (Sum.inr 1829) = Sparse.eval nodeValue1829 (mixedVector B) := by
    change mixedMoment B node1829 node1829Labels = _
    exact sound1829 B hB hF
  have h1830 : mixedVector B (Sum.inr 1830) = Sparse.eval nodeValue1830 (mixedVector B) := by
    change mixedMoment B node1830 node1830Labels = _
    exact sound1830 B hB hF
  have h1831 : mixedVector B (Sum.inr 1831) = Sparse.eval nodeValue1831 (mixedVector B) := by
    change mixedMoment B node1831 node1831Labels = _
    exact sound1831 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2362 : mixedVector B (Sum.inr 2362) = Sparse.eval nodeValue2362 (mixedVector B) := by
    change mixedMoment B node2362 node2362Labels = _
    exact sound2362 B hB hF
  have h2363 : mixedVector B (Sum.inr 2363) = Sparse.eval nodeValue2363 (mixedVector B) := by
    change mixedMoment B node2363 node2363Labels = _
    exact sound2363 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h2831 : mixedVector B (Sum.inr 2831) = Sparse.eval nodeValue2831 (mixedVector B) := by
    change mixedMoment B node2831 node2831Labels = _
    exact sound2831 B hB hF
  have h2832 : mixedVector B (Sum.inr 2832) = Sparse.eval nodeValue2832 (mixedVector B) := by
    change mixedMoment B node2832 node2832Labels = _
    exact sound2832 B hB hF
  have h3005 : mixedVector B (Sum.inr 3005) = Sparse.eval nodeValue3005 (mixedVector B) := by
    change mixedMoment B node3005 node3005Labels = _
    exact sound3005 B hB hF
  have h3083 : mixedVector B (Sum.inr 3083) = Sparse.eval nodeValue3083 (mixedVector B) := by
    change mixedMoment B node3083 node3083Labels = _
    exact sound3083 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3094 : mixedVector B (Sum.inr 3094) = Sparse.eval nodeValue3094 (mixedVector B) := by
    change mixedMoment B node3094 node3094Labels = _
    exact sound3094 B hB hF
  have h3106 : mixedVector B (Sum.inr 3106) = Sparse.eval nodeValue3106 (mixedVector B) := by
    change mixedMoment B node3106 node3106Labels = _
    exact sound3106 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h3144 : mixedVector B (Sum.inr 3144) = Sparse.eval nodeValue3144 (mixedVector B) := by
    change mixedMoment B node3144 node3144Labels = _
    exact sound3144 B hB hF
  have h3216 : mixedVector B (Sum.inr 3216) = Sparse.eval nodeValue3216 (mixedVector B) := by
    change mixedMoment B node3216 node3216Labels = _
    exact sound3216 B hB hF
  simpa only [sourceForm2546, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1829, h1830, h1831, h2138, h2362, h2363, h2643, h2758, h2774, h2776, h2831, h2832, h3005, h3083, h3092, h3094, h3106, h3110, h3112, h3144, h3216, reducedSource2046] using sourceEq2546 B hB

theorem rowSound2046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2046 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2046, numericCheck2046, reducedZero2046 B hB hF, mul_zero]

theorem reducedZero2047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2047 (mixedVector B) = 0 := by
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h2273 : mixedVector B (Sum.inr 2273) = Sparse.eval nodeValue2273 (mixedVector B) := by
    change mixedMoment B node2273 node2273Labels = _
    exact sound2273 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2659 : mixedVector B (Sum.inr 2659) = Sparse.eval nodeValue2659 (mixedVector B) := by
    change mixedMoment B node2659 node2659Labels = _
    exact sound2659 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  simpa only [sourceForm2547, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2152, h2168, h2169, h2229, h2272, h2273, h2280, h2286, h2653, h2658, h2659, h2672, h2673, h2685, h2687, h2705, h2742, h2743, h3025, h3054, h3055, reducedSource2047] using sourceEq2547 B hB

theorem rowSound2047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2047 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2047, numericCheck2047, reducedZero2047 B hB hF, mul_zero]

theorem sourceRowsAt2032 : MixedData.sourceRows (2032 : Fin 2425) =
    MixedData.row2032 := by decide +kernel

theorem sourceRowsAt2033 : MixedData.sourceRows (2033 : Fin 2425) =
    MixedData.row2033 := by decide +kernel

theorem sourceRowsAt2034 : MixedData.sourceRows (2034 : Fin 2425) =
    MixedData.row2034 := by decide +kernel

theorem sourceRowsAt2035 : MixedData.sourceRows (2035 : Fin 2425) =
    MixedData.row2035 := by decide +kernel

theorem sourceRowsAt2036 : MixedData.sourceRows (2036 : Fin 2425) =
    MixedData.row2036 := by decide +kernel

theorem sourceRowsAt2037 : MixedData.sourceRows (2037 : Fin 2425) =
    MixedData.row2037 := by decide +kernel

theorem sourceRowsAt2038 : MixedData.sourceRows (2038 : Fin 2425) =
    MixedData.row2038 := by decide +kernel

theorem sourceRowsAt2039 : MixedData.sourceRows (2039 : Fin 2425) =
    MixedData.row2039 := by decide +kernel

theorem sourceRowsAt2040 : MixedData.sourceRows (2040 : Fin 2425) =
    MixedData.row2040 := by decide +kernel

theorem sourceRowsAt2041 : MixedData.sourceRows (2041 : Fin 2425) =
    MixedData.row2041 := by decide +kernel

theorem sourceRowsAt2042 : MixedData.sourceRows (2042 : Fin 2425) =
    MixedData.row2042 := by decide +kernel

theorem sourceRowsAt2043 : MixedData.sourceRows (2043 : Fin 2425) =
    MixedData.row2043 := by decide +kernel

theorem sourceRowsAt2044 : MixedData.sourceRows (2044 : Fin 2425) =
    MixedData.row2044 := by decide +kernel

theorem sourceRowsAt2045 : MixedData.sourceRows (2045 : Fin 2425) =
    MixedData.row2045 := by decide +kernel

theorem sourceRowsAt2046 : MixedData.sourceRows (2046 : Fin 2425) =
    MixedData.row2046 := by decide +kernel

theorem sourceRowsAt2047 : MixedData.sourceRows (2047 : Fin 2425) =
    MixedData.row2047 := by decide +kernel

theorem chunkSound127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 127) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2032 ∨ k.val = 2033 ∨ k.val = 2034 ∨ k.val = 2035 ∨ k.val = 2036 ∨ k.val = 2037 ∨ k.val = 2038 ∨ k.val = 2039 ∨ k.val = 2040 ∨ k.val = 2041 ∨ k.val = 2042 ∨ k.val = 2043 ∨ k.val = 2044 ∨ k.val = 2045 ∨ k.val = 2046 ∨ k.val = 2047 := by omega
  rcases heq with h2032 | h2033 | h2034 | h2035 | h2036 | h2037 | h2038 | h2039 | h2040 | h2041 | h2042 | h2043 | h2044 | h2045 | h2046 | h2047
  · have he : k = (2032 : Fin 2425) := Fin.ext h2032
    subst k
    rw [sourceRowsAt2032]
    exact rowSound2032 B hB hF
  · have he : k = (2033 : Fin 2425) := Fin.ext h2033
    subst k
    rw [sourceRowsAt2033]
    exact rowSound2033 B hB hF
  · have he : k = (2034 : Fin 2425) := Fin.ext h2034
    subst k
    rw [sourceRowsAt2034]
    exact rowSound2034 B hB hF
  · have he : k = (2035 : Fin 2425) := Fin.ext h2035
    subst k
    rw [sourceRowsAt2035]
    exact rowSound2035 B hB hF
  · have he : k = (2036 : Fin 2425) := Fin.ext h2036
    subst k
    rw [sourceRowsAt2036]
    exact rowSound2036 B hB hF
  · have he : k = (2037 : Fin 2425) := Fin.ext h2037
    subst k
    rw [sourceRowsAt2037]
    exact rowSound2037 B hB hF
  · have he : k = (2038 : Fin 2425) := Fin.ext h2038
    subst k
    rw [sourceRowsAt2038]
    exact rowSound2038 B hB hF
  · have he : k = (2039 : Fin 2425) := Fin.ext h2039
    subst k
    rw [sourceRowsAt2039]
    exact rowSound2039 B hB hF
  · have he : k = (2040 : Fin 2425) := Fin.ext h2040
    subst k
    rw [sourceRowsAt2040]
    exact rowSound2040 B hB hF
  · have he : k = (2041 : Fin 2425) := Fin.ext h2041
    subst k
    rw [sourceRowsAt2041]
    exact rowSound2041 B hB hF
  · have he : k = (2042 : Fin 2425) := Fin.ext h2042
    subst k
    rw [sourceRowsAt2042]
    exact rowSound2042 B hB hF
  · have he : k = (2043 : Fin 2425) := Fin.ext h2043
    subst k
    rw [sourceRowsAt2043]
    exact rowSound2043 B hB hF
  · have he : k = (2044 : Fin 2425) := Fin.ext h2044
    subst k
    rw [sourceRowsAt2044]
    exact rowSound2044 B hB hF
  · have he : k = (2045 : Fin 2425) := Fin.ext h2045
    subst k
    rw [sourceRowsAt2045]
    exact rowSound2045 B hB hF
  · have he : k = (2046 : Fin 2425) := Fin.ext h2046
    subst k
    rw [sourceRowsAt2046]
    exact rowSound2046 B hB hF
  · have he : k = (2047 : Fin 2425) := Fin.ext h2047
    subst k
    rw [sourceRowsAt2047]
    exact rowSound2047 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
