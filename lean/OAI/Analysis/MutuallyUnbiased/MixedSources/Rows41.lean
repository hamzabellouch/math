import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources24

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource656 (mixedVector B) = 0 := by
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452 B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  simpa only [sourceForm757, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4601, h4602, h4606, h4622, h5148, h5149, h5167, h5202, h5203, h5204, h5283, h5284, h5292, h5293, h5294, h5307, h5433, h5450, h5452, h5454, reducedSource656] using sourceEq757 B hB

theorem rowSound656 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row656 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck656, numericCheck656, reducedZero656 B hB hF, mul_zero]

theorem reducedZero657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource657 (mixedVector B) = 0 := by
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2927 : mixedVector B (Sum.inr 2927) = Sparse.eval nodeValue2927 (mixedVector B) := by
    change mixedMoment B node2927 node2927Labels = _
    exact sound2927 B hB hF
  have h2958 : mixedVector B (Sum.inr 2958) = Sparse.eval nodeValue2958 (mixedVector B) := by
    change mixedMoment B node2958 node2958Labels = _
    exact sound2958 B hB hF
  have h3076 : mixedVector B (Sum.inr 3076) = Sparse.eval nodeValue3076 (mixedVector B) := by
    change mixedMoment B node3076 node3076Labels = _
    exact sound3076 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  have h3122 : mixedVector B (Sum.inr 3122) = Sparse.eval nodeValue3122 (mixedVector B) := by
    change mixedMoment B node3122 node3122Labels = _
    exact sound3122 B hB hF
  have h4029 : mixedVector B (Sum.inr 4029) = Sparse.eval nodeValue4029 (mixedVector B) := by
    change mixedMoment B node4029 node4029Labels = _
    exact sound4029 B hB hF
  have h4033 : mixedVector B (Sum.inr 4033) = Sparse.eval nodeValue4033 (mixedVector B) := by
    change mixedMoment B node4033 node4033Labels = _
    exact sound4033 B hB hF
  have h4039 : mixedVector B (Sum.inr 4039) = Sparse.eval nodeValue4039 (mixedVector B) := by
    change mixedMoment B node4039 node4039Labels = _
    exact sound4039 B hB hF
  have h4040 : mixedVector B (Sum.inr 4040) = Sparse.eval nodeValue4040 (mixedVector B) := by
    change mixedMoment B node4040 node4040Labels = _
    exact sound4040 B hB hF
  simpa only [sourceForm758, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1235, h1236, h1240, h1299, h2880, h2881, h2884, h2924, h2927, h2958, h3076, h3077, h3100, h3101, h3102, h3122, h4029, h4033, h4039, h4040, reducedSource657] using sourceEq758 B hB

theorem rowSound657 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row657 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck657, numericCheck657, reducedZero657 B hB hF, mul_zero]

theorem reducedZero658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource658 (mixedVector B) = 0 := by
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5098 : mixedVector B (Sum.inr 5098) = Sparse.eval nodeValue5098 (mixedVector B) := by
    change mixedMoment B node5098 node5098Labels = _
    exact sound5098 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490 B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  simpa only [sourceForm759, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4456, h4457, h4458, h4495, h5072, h5073, h5098, h5167, h5168, h5169, h5257, h5258, h5259, h5271, h5292, h5293, h5306, h5482, h5486, h5490, h5493, reducedSource658] using sourceEq759 B hB

theorem rowSound658 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row658 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck658, numericCheck658, reducedZero658 B hB hF, mul_zero]

theorem reducedZero659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource659 (mixedVector B) = 0 := by
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2593 : mixedVector B (Sum.inr 2593) = Sparse.eval nodeValue2593 (mixedVector B) := by
    change mixedMoment B node2593 node2593Labels = _
    exact sound2593 B hB hF
  have h2594 : mixedVector B (Sum.inr 2594) = Sparse.eval nodeValue2594 (mixedVector B) := by
    change mixedMoment B node2594 node2594Labels = _
    exact sound2594 B hB hF
  have h2595 : mixedVector B (Sum.inr 2595) = Sparse.eval nodeValue2595 (mixedVector B) := by
    change mixedMoment B node2595 node2595Labels = _
    exact sound2595 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2784 : mixedVector B (Sum.inr 2784) = Sparse.eval nodeValue2784 (mixedVector B) := by
    change mixedMoment B node2784 node2784Labels = _
    exact sound2784 B hB hF
  have h3980 : mixedVector B (Sum.inr 3980) = Sparse.eval nodeValue3980 (mixedVector B) := by
    change mixedMoment B node3980 node3980Labels = _
    exact sound3980 B hB hF
  have h3999 : mixedVector B (Sum.inr 3999) = Sparse.eval nodeValue3999 (mixedVector B) := by
    change mixedMoment B node3999 node3999Labels = _
    exact sound3999 B hB hF
  have h4013 : mixedVector B (Sum.inr 4013) = Sparse.eval nodeValue4013 (mixedVector B) := by
    change mixedMoment B node4013 node4013Labels = _
    exact sound4013 B hB hF
  have h4018 : mixedVector B (Sum.inr 4018) = Sparse.eval nodeValue4018 (mixedVector B) := by
    change mixedMoment B node4018 node4018Labels = _
    exact sound4018 B hB hF
  simpa only [sourceForm760, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1039, h1040, h1041, h1079, h2479, h2480, h2508, h2593, h2594, h2595, h2721, h2722, h2723, h2739, h2766, h2767, h2784, h3980, h3999, h4013, h4018, reducedSource659] using sourceEq760 B hB

theorem rowSound659 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row659 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck659, numericCheck659, reducedZero659 B hB hF, mul_zero]

theorem reducedZero660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource660 (mixedVector B) = 0 := by
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  simpa only [sourceForm761, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4887, h4888, h4889, h4893, h5256, h5257, h5265, h5271, h5273, h5281, h5283, h5289, h5290, h5292, h5299, h5301, h5306, h5307, reducedSource660] using sourceEq761 B hB

theorem rowSound660 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row660 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck660, numericCheck660, reducedZero660 B hB hF, mul_zero]

theorem reducedZero661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource661 (mixedVector B) = 0 := by
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3622 : mixedVector B (Sum.inr 3622) = Sparse.eval nodeValue3622 (mixedVector B) := by
    change mixedMoment B node3622 node3622Labels = _
    exact sound3622 B hB hF
  have h3628 : mixedVector B (Sum.inr 3628) = Sparse.eval nodeValue3628 (mixedVector B) := by
    change mixedMoment B node3628 node3628Labels = _
    exact sound3628 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm762, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3532, h3534, h3546, h3622, h3628, h4083, reducedSource661] using sourceEq762 B hB

theorem rowSound661 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row661 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck661, numericCheck661, reducedZero661 B hB hF, mul_zero]

theorem reducedZero662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource662 (mixedVector B) = 0 := by
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3618 : mixedVector B (Sum.inr 3618) = Sparse.eval nodeValue3618 (mixedVector B) := by
    change mixedMoment B node3618 node3618Labels = _
    exact sound3618 B hB hF
  have h3622 : mixedVector B (Sum.inr 3622) = Sparse.eval nodeValue3622 (mixedVector B) := by
    change mixedMoment B node3622 node3622Labels = _
    exact sound3622 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm763, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2243, h3571, h3618, h3622, h4083, reducedSource662] using sourceEq763 B hB

theorem rowSound662 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row662 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck662, numericCheck662, reducedZero662 B hB hF, mul_zero]

theorem reducedZero663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource663 (mixedVector B) = 0 := by
  have h1183 : mixedVector B (Sum.inr 1183) = Sparse.eval nodeValue1183 (mixedVector B) := by
    change mixedMoment B node1183 node1183Labels = _
    exact sound1183 B hB hF
  have h1184 : mixedVector B (Sum.inr 1184) = Sparse.eval nodeValue1184 (mixedVector B) := by
    change mixedMoment B node1184 node1184Labels = _
    exact sound1184 B hB hF
  have h1185 : mixedVector B (Sum.inr 1185) = Sparse.eval nodeValue1185 (mixedVector B) := by
    change mixedMoment B node1185 node1185Labels = _
    exact sound1185 B hB hF
  have h1189 : mixedVector B (Sum.inr 1189) = Sparse.eval nodeValue1189 (mixedVector B) := by
    change mixedMoment B node1189 node1189Labels = _
    exact sound1189 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h2836 : mixedVector B (Sum.inr 2836) = Sparse.eval nodeValue2836 (mixedVector B) := by
    change mixedMoment B node2836 node2836Labels = _
    exact sound2836 B hB hF
  have h2837 : mixedVector B (Sum.inr 2837) = Sparse.eval nodeValue2837 (mixedVector B) := by
    change mixedMoment B node2837 node2837Labels = _
    exact sound2837 B hB hF
  have h2838 : mixedVector B (Sum.inr 2838) = Sparse.eval nodeValue2838 (mixedVector B) := by
    change mixedMoment B node2838 node2838Labels = _
    exact sound2838 B hB hF
  have h2841 : mixedVector B (Sum.inr 2841) = Sparse.eval nodeValue2841 (mixedVector B) := by
    change mixedMoment B node2841 node2841Labels = _
    exact sound2841 B hB hF
  have h2906 : mixedVector B (Sum.inr 2906) = Sparse.eval nodeValue2906 (mixedVector B) := by
    change mixedMoment B node2906 node2906Labels = _
    exact sound2906 B hB hF
  have h2907 : mixedVector B (Sum.inr 2907) = Sparse.eval nodeValue2907 (mixedVector B) := by
    change mixedMoment B node2907 node2907Labels = _
    exact sound2907 B hB hF
  have h2909 : mixedVector B (Sum.inr 2909) = Sparse.eval nodeValue2909 (mixedVector B) := by
    change mixedMoment B node2909 node2909Labels = _
    exact sound2909 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  simpa only [sourceForm765, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1183, h1184, h1185, h1189, h1291, h2836, h2837, h2838, h2841, h2906, h2907, h2909, h2951, h3023, h3024, h3025, h3037, h3038, h3039, h3051, h3052, h3055, h3097, h3109, h3119, h3535, h3809, h3839, h3853, h3862, reducedSource663] using sourceEq765 B hB

theorem rowSound663 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row663 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck663, numericCheck663, reducedZero663 B hB hF, mul_zero]

theorem reducedZero664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource664 (mixedVector B) = 0 := by
  have h2463 : mixedVector B (Sum.inr 2463) = Sparse.eval nodeValue2463 (mixedVector B) := by
    change mixedMoment B node2463 node2463Labels = _
    exact sound2463 B hB hF
  have h2465 : mixedVector B (Sum.inr 2465) = Sparse.eval nodeValue2465 (mixedVector B) := by
    change mixedMoment B node2465 node2465Labels = _
    exact sound2465 B hB hF
  have h2466 : mixedVector B (Sum.inr 2466) = Sparse.eval nodeValue2466 (mixedVector B) := by
    change mixedMoment B node2466 node2466Labels = _
    exact sound2466 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2834 : mixedVector B (Sum.inr 2834) = Sparse.eval nodeValue2834 (mixedVector B) := by
    change mixedMoment B node2834 node2834Labels = _
    exact sound2834 B hB hF
  have h2835 : mixedVector B (Sum.inr 2835) = Sparse.eval nodeValue2835 (mixedVector B) := by
    change mixedMoment B node2835 node2835Labels = _
    exact sound2835 B hB hF
  have h2841 : mixedVector B (Sum.inr 2841) = Sparse.eval nodeValue2841 (mixedVector B) := by
    change mixedMoment B node2841 node2841Labels = _
    exact sound2841 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3239 : mixedVector B (Sum.inr 3239) = Sparse.eval nodeValue3239 (mixedVector B) := by
    change mixedMoment B node3239 node3239Labels = _
    exact sound3239 B hB hF
  have h3240 : mixedVector B (Sum.inr 3240) = Sparse.eval nodeValue3240 (mixedVector B) := by
    change mixedMoment B node3240 node3240Labels = _
    exact sound3240 B hB hF
  have h3246 : mixedVector B (Sum.inr 3246) = Sparse.eval nodeValue3246 (mixedVector B) := by
    change mixedMoment B node3246 node3246Labels = _
    exact sound3246 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3559 : mixedVector B (Sum.inr 3559) = Sparse.eval nodeValue3559 (mixedVector B) := by
    change mixedMoment B node3559 node3559Labels = _
    exact sound3559 B hB hF
  have h3561 : mixedVector B (Sum.inr 3561) = Sparse.eval nodeValue3561 (mixedVector B) := by
    change mixedMoment B node3561 node3561Labels = _
    exact sound3561 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm766, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2463, h2465, h2466, h2513, h2744, h2834, h2835, h2841, h3039, h3239, h3240, h3246, h3303, h3526, h3534, h3535, h3541, h3558, h3559, h3561, h3567, h3572, h3573, h3577, h3583, h3584, h3853, h3872, h3883, h3889, reducedSource664] using sourceEq766 B hB

theorem rowSound664 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row664 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck664, numericCheck664, reducedZero664 B hB hF, mul_zero]

theorem reducedZero665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource665 (mixedVector B) = 0 := by
  have h1276 : mixedVector B (Sum.inr 1276) = Sparse.eval nodeValue1276 (mixedVector B) := by
    change mixedMoment B node1276 node1276Labels = _
    exact sound1276 B hB hF
  have h1277 : mixedVector B (Sum.inr 1277) = Sparse.eval nodeValue1277 (mixedVector B) := by
    change mixedMoment B node1277 node1277Labels = _
    exact sound1277 B hB hF
  have h1278 : mixedVector B (Sum.inr 1278) = Sparse.eval nodeValue1278 (mixedVector B) := by
    change mixedMoment B node1278 node1278Labels = _
    exact sound1278 B hB hF
  have h1280 : mixedVector B (Sum.inr 1280) = Sparse.eval nodeValue1280 (mixedVector B) := by
    change mixedMoment B node1280 node1280Labels = _
    exact sound1280 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm767, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1276, h1277, h1278, h1280, h1291, h2773, h4092, reducedSource665] using sourceEq767 B hB

theorem rowSound665 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row665 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck665, numericCheck665, reducedZero665 B hB hF, mul_zero]

theorem reducedZero666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource666 (mixedVector B) = 0 := by
  have h4469 : mixedVector B (Sum.inr 4469) = Sparse.eval nodeValue4469 (mixedVector B) := by
    change mixedMoment B node4469 node4469Labels = _
    exact sound4469 B hB hF
  have h4470 : mixedVector B (Sum.inr 4470) = Sparse.eval nodeValue4470 (mixedVector B) := by
    change mixedMoment B node4470 node4470Labels = _
    exact sound4470 B hB hF
  have h4471 : mixedVector B (Sum.inr 4471) = Sparse.eval nodeValue4471 (mixedVector B) := by
    change mixedMoment B node4471 node4471Labels = _
    exact sound4471 B hB hF
  have h4475 : mixedVector B (Sum.inr 4475) = Sparse.eval nodeValue4475 (mixedVector B) := by
    change mixedMoment B node4475 node4475Labels = _
    exact sound4475 B hB hF
  have h4486 : mixedVector B (Sum.inr 4486) = Sparse.eval nodeValue4486 (mixedVector B) := by
    change mixedMoment B node4486 node4486Labels = _
    exact sound4486 B hB hF
  have h5082 : mixedVector B (Sum.inr 5082) = Sparse.eval nodeValue5082 (mixedVector B) := by
    change mixedMoment B node5082 node5082Labels = _
    exact sound5082 B hB hF
  have h5083 : mixedVector B (Sum.inr 5083) = Sparse.eval nodeValue5083 (mixedVector B) := by
    change mixedMoment B node5083 node5083Labels = _
    exact sound5083 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5091 : mixedVector B (Sum.inr 5091) = Sparse.eval nodeValue5091 (mixedVector B) := by
    change mixedMoment B node5091 node5091Labels = _
    exact sound5091 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5197 : mixedVector B (Sum.inr 5197) = Sparse.eval nodeValue5197 (mixedVector B) := by
    change mixedMoment B node5197 node5197Labels = _
    exact sound5197 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5199 : mixedVector B (Sum.inr 5199) = Sparse.eval nodeValue5199 (mixedVector B) := by
    change mixedMoment B node5199 node5199Labels = _
    exact sound5199 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5232 : mixedVector B (Sum.inr 5232) = Sparse.eval nodeValue5232 (mixedVector B) := by
    change mixedMoment B node5232 node5232Labels = _
    exact sound5232 B hB hF
  have h5233 : mixedVector B (Sum.inr 5233) = Sparse.eval nodeValue5233 (mixedVector B) := by
    change mixedMoment B node5233 node5233Labels = _
    exact sound5233 B hB hF
  have h5263 : mixedVector B (Sum.inr 5263) = Sparse.eval nodeValue5263 (mixedVector B) := by
    change mixedMoment B node5263 node5263Labels = _
    exact sound5263 B hB hF
  have h5264 : mixedVector B (Sum.inr 5264) = Sparse.eval nodeValue5264 (mixedVector B) := by
    change mixedMoment B node5264 node5264Labels = _
    exact sound5264 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5300 : mixedVector B (Sum.inr 5300) = Sparse.eval nodeValue5300 (mixedVector B) := by
    change mixedMoment B node5300 node5300Labels = _
    exact sound5300 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm768, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4469, h4470, h4471, h4475, h4486, h5082, h5083, h5086, h5091, h5151, h5173, h5197, h5198, h5199, h5204, h5231, h5232, h5233, h5263, h5264, h5267, h5295, h5299, h5300, h5302, h5430, h5432, h5438, h5451, h5473, reducedSource666] using sourceEq768 B hB

theorem rowSound666 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row666 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck666, numericCheck666, reducedZero666 B hB hF, mul_zero]

theorem reducedZero667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource667 (mixedVector B) = 0 := by
  have h1052 : mixedVector B (Sum.inr 1052) = Sparse.eval nodeValue1052 (mixedVector B) := by
    change mixedMoment B node1052 node1052Labels = _
    exact sound1052 B hB hF
  have h1053 : mixedVector B (Sum.inr 1053) = Sparse.eval nodeValue1053 (mixedVector B) := by
    change mixedMoment B node1053 node1053Labels = _
    exact sound1053 B hB hF
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h1070 : mixedVector B (Sum.inr 1070) = Sparse.eval nodeValue1070 (mixedVector B) := by
    change mixedMoment B node1070 node1070Labels = _
    exact sound1070 B hB hF
  have h2490 : mixedVector B (Sum.inr 2490) = Sparse.eval nodeValue2490 (mixedVector B) := by
    change mixedMoment B node2490 node2490Labels = _
    exact sound2490 B hB hF
  have h2491 : mixedVector B (Sum.inr 2491) = Sparse.eval nodeValue2491 (mixedVector B) := by
    change mixedMoment B node2491 node2491Labels = _
    exact sound2491 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2500 : mixedVector B (Sum.inr 2500) = Sparse.eval nodeValue2500 (mixedVector B) := by
    change mixedMoment B node2500 node2500Labels = _
    exact sound2500 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2633 : mixedVector B (Sum.inr 2633) = Sparse.eval nodeValue2633 (mixedVector B) := by
    change mixedMoment B node2633 node2633Labels = _
    exact sound2633 B hB hF
  have h2638 : mixedVector B (Sum.inr 2638) = Sparse.eval nodeValue2638 (mixedVector B) := by
    change mixedMoment B node2638 node2638Labels = _
    exact sound2638 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995 B hB hF
  simpa only [sourceForm769, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1052, h1053, h1054, h1058, h1070, h2490, h2491, h2494, h2500, h2631, h2632, h2633, h2638, h2676, h2677, h2678, h2681, h2728, h2729, h2732, h2735, h2773, h2774, h2776, h2781, h3850, h3871, h3876, h3888, h3995, reducedSource667] using sourceEq769 B hB

theorem rowSound667 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row667 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck667, numericCheck667, reducedZero667 B hB hF, mul_zero]

theorem reducedZero668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource668 (mixedVector B) = 0 := by
  have h1638 : mixedVector B (Sum.inr 1638) = Sparse.eval nodeValue1638 (mixedVector B) := by
    change mixedMoment B node1638 node1638Labels = _
    exact sound1638 B hB hF
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1640 : mixedVector B (Sum.inr 1640) = Sparse.eval nodeValue1640 (mixedVector B) := by
    change mixedMoment B node1640 node1640Labels = _
    exact sound1640 B hB hF
  have h1649 : mixedVector B (Sum.inr 1649) = Sparse.eval nodeValue1649 (mixedVector B) := by
    change mixedMoment B node1649 node1649Labels = _
    exact sound1649 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h2921 : mixedVector B (Sum.inr 2921) = Sparse.eval nodeValue2921 (mixedVector B) := by
    change mixedMoment B node2921 node2921Labels = _
    exact sound2921 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3441 : mixedVector B (Sum.inr 3441) = Sparse.eval nodeValue3441 (mixedVector B) := by
    change mixedMoment B node3441 node3441Labels = _
    exact sound3441 B hB hF
  have h3447 : mixedVector B (Sum.inr 3447) = Sparse.eval nodeValue3447 (mixedVector B) := by
    change mixedMoment B node3447 node3447Labels = _
    exact sound3447 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3569 : mixedVector B (Sum.inr 3569) = Sparse.eval nodeValue3569 (mixedVector B) := by
    change mixedMoment B node3569 node3569Labels = _
    exact sound3569 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h3987 : mixedVector B (Sum.inr 3987) = Sparse.eval nodeValue3987 (mixedVector B) := by
    change mixedMoment B node3987 node3987Labels = _
    exact sound3987 B hB hF
  have h3993 : mixedVector B (Sum.inr 3993) = Sparse.eval nodeValue3993 (mixedVector B) := by
    change mixedMoment B node3993 node3993Labels = _
    exact sound3993 B hB hF
  have h4027 : mixedVector B (Sum.inr 4027) = Sparse.eval nodeValue4027 (mixedVector B) := by
    change mixedMoment B node4027 node4027Labels = _
    exact sound4027 B hB hF
  simpa only [sourceForm770, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1638, h1639, h1640, h1649, h1715, h2921, h2930, h2952, h3098, h3378, h3379, h3395, h3441, h3447, h3464, h3505, h3506, h3541, h3569, h3570, h3573, h3578, h3584, h3624, h3626, h3958, h3972, h3987, h3993, h4027, reducedSource668] using sourceEq770 B hB

theorem rowSound668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row668 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck668, numericCheck668, reducedZero668 B hB hF, mul_zero]

theorem reducedZero669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource669 (mixedVector B) = 0 := by
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm771, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3051, h3848, h3850, h3857, h3913, h3961, h4092, reducedSource669] using sourceEq771 B hB

theorem rowSound669 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row669 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck669, numericCheck669, reducedZero669 B hB hF, mul_zero]

theorem reducedZero670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource670 (mixedVector B) = 0 := by
  have h1364 : mixedVector B (Sum.inr 1364) = Sparse.eval nodeValue1364 (mixedVector B) := by
    change mixedMoment B node1364 node1364Labels = _
    exact sound1364 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1368 : mixedVector B (Sum.inr 1368) = Sparse.eval nodeValue1368 (mixedVector B) := by
    change mixedMoment B node1368 node1368Labels = _
    exact sound1368 B hB hF
  have h1371 : mixedVector B (Sum.inr 1371) = Sparse.eval nodeValue1371 (mixedVector B) := by
    change mixedMoment B node1371 node1371Labels = _
    exact sound1371 B hB hF
  have h1433 : mixedVector B (Sum.inr 1433) = Sparse.eval nodeValue1433 (mixedVector B) := by
    change mixedMoment B node1433 node1433Labels = _
    exact sound1433 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm772, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1364, h1367, h1368, h1371, h1433, h3051, h4092, reducedSource670] using sourceEq772 B hB

theorem rowSound670 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row670 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck670, numericCheck670, reducedZero670 B hB hF, mul_zero]

theorem reducedZero671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource671 (mixedVector B) = 0 := by
  have h1364 : mixedVector B (Sum.inr 1364) = Sparse.eval nodeValue1364 (mixedVector B) := by
    change mixedMoment B node1364 node1364Labels = _
    exact sound1364 B hB hF
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h3036 : mixedVector B (Sum.inr 3036) = Sparse.eval nodeValue3036 (mixedVector B) := by
    change mixedMoment B node3036 node3036Labels = _
    exact sound3036 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm773, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1364, h2878, h3036, h3043, h3051, h4092, reducedSource671] using sourceEq773 B hB

theorem rowSound671 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row671 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck671, numericCheck671, reducedZero671 B hB hF, mul_zero]

theorem sourceRowsAt656 : MixedData.sourceRows (656 : Fin 2425) =
    MixedData.row656 := by decide +kernel

theorem sourceRowsAt657 : MixedData.sourceRows (657 : Fin 2425) =
    MixedData.row657 := by decide +kernel

theorem sourceRowsAt658 : MixedData.sourceRows (658 : Fin 2425) =
    MixedData.row658 := by decide +kernel

theorem sourceRowsAt659 : MixedData.sourceRows (659 : Fin 2425) =
    MixedData.row659 := by decide +kernel

theorem sourceRowsAt660 : MixedData.sourceRows (660 : Fin 2425) =
    MixedData.row660 := by decide +kernel

theorem sourceRowsAt661 : MixedData.sourceRows (661 : Fin 2425) =
    MixedData.row661 := by decide +kernel

theorem sourceRowsAt662 : MixedData.sourceRows (662 : Fin 2425) =
    MixedData.row662 := by decide +kernel

theorem sourceRowsAt663 : MixedData.sourceRows (663 : Fin 2425) =
    MixedData.row663 := by decide +kernel

theorem sourceRowsAt664 : MixedData.sourceRows (664 : Fin 2425) =
    MixedData.row664 := by decide +kernel

theorem sourceRowsAt665 : MixedData.sourceRows (665 : Fin 2425) =
    MixedData.row665 := by decide +kernel

theorem sourceRowsAt666 : MixedData.sourceRows (666 : Fin 2425) =
    MixedData.row666 := by decide +kernel

theorem sourceRowsAt667 : MixedData.sourceRows (667 : Fin 2425) =
    MixedData.row667 := by decide +kernel

theorem sourceRowsAt668 : MixedData.sourceRows (668 : Fin 2425) =
    MixedData.row668 := by decide +kernel

theorem sourceRowsAt669 : MixedData.sourceRows (669 : Fin 2425) =
    MixedData.row669 := by decide +kernel

theorem sourceRowsAt670 : MixedData.sourceRows (670 : Fin 2425) =
    MixedData.row670 := by decide +kernel

theorem sourceRowsAt671 : MixedData.sourceRows (671 : Fin 2425) =
    MixedData.row671 := by decide +kernel

theorem chunkSound41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 41) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 656 ∨ k.val = 657 ∨ k.val = 658 ∨ k.val = 659 ∨ k.val = 660 ∨ k.val = 661 ∨ k.val = 662 ∨ k.val = 663 ∨ k.val = 664 ∨ k.val = 665 ∨ k.val = 666 ∨ k.val = 667 ∨ k.val = 668 ∨ k.val = 669 ∨ k.val = 670 ∨ k.val = 671 := by omega
  rcases heq with h656 | h657 | h658 | h659 | h660 | h661 | h662 | h663 | h664 | h665 | h666 | h667 | h668 | h669 | h670 | h671
  · have he : k = (656 : Fin 2425) := Fin.ext h656
    subst k
    rw [sourceRowsAt656]
    exact rowSound656 B hB hF
  · have he : k = (657 : Fin 2425) := Fin.ext h657
    subst k
    rw [sourceRowsAt657]
    exact rowSound657 B hB hF
  · have he : k = (658 : Fin 2425) := Fin.ext h658
    subst k
    rw [sourceRowsAt658]
    exact rowSound658 B hB hF
  · have he : k = (659 : Fin 2425) := Fin.ext h659
    subst k
    rw [sourceRowsAt659]
    exact rowSound659 B hB hF
  · have he : k = (660 : Fin 2425) := Fin.ext h660
    subst k
    rw [sourceRowsAt660]
    exact rowSound660 B hB hF
  · have he : k = (661 : Fin 2425) := Fin.ext h661
    subst k
    rw [sourceRowsAt661]
    exact rowSound661 B hB hF
  · have he : k = (662 : Fin 2425) := Fin.ext h662
    subst k
    rw [sourceRowsAt662]
    exact rowSound662 B hB hF
  · have he : k = (663 : Fin 2425) := Fin.ext h663
    subst k
    rw [sourceRowsAt663]
    exact rowSound663 B hB hF
  · have he : k = (664 : Fin 2425) := Fin.ext h664
    subst k
    rw [sourceRowsAt664]
    exact rowSound664 B hB hF
  · have he : k = (665 : Fin 2425) := Fin.ext h665
    subst k
    rw [sourceRowsAt665]
    exact rowSound665 B hB hF
  · have he : k = (666 : Fin 2425) := Fin.ext h666
    subst k
    rw [sourceRowsAt666]
    exact rowSound666 B hB hF
  · have he : k = (667 : Fin 2425) := Fin.ext h667
    subst k
    rw [sourceRowsAt667]
    exact rowSound667 B hB hF
  · have he : k = (668 : Fin 2425) := Fin.ext h668
    subst k
    rw [sourceRowsAt668]
    exact rowSound668 B hB hF
  · have he : k = (669 : Fin 2425) := Fin.ext h669
    subst k
    rw [sourceRowsAt669]
    exact rowSound669 B hB hF
  · have he : k = (670 : Fin 2425) := Fin.ext h670
    subst k
    rw [sourceRowsAt670]
    exact rowSound670 B hB hF
  · have he : k = (671 : Fin 2425) := Fin.ext h671
    subst k
    rw [sourceRowsAt671]
    exact rowSound671 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
