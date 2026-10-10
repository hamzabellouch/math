import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources17

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource448 (mixedVector B) = 0 := by
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  have h3984 : mixedVector B (Sum.inr 3984) = Sparse.eval nodeValue3984 (mixedVector B) := by
    change mixedMoment B node3984 node3984Labels = _
    exact sound3984 B hB hF
  simpa only [sourceForm534, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1713, h1714, h1723, h1736, h3463, h3466, h3476, h3481, h3539, h3540, h3543, h3571, h3572, h3580, h3605, h3606, h3612, h3805, h3816, h3858, h3984, reducedSource448] using sourceEq534 B hB

theorem rowSound448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row448 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck448, numericCheck448, reducedZero448 B hB hF, mul_zero]

theorem reducedZero449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource449 (mixedVector B) = 0 := by
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm535, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3077, h3800, h3808, h3902, h4010, h4091, reducedSource449] using sourceEq535 B hB

theorem rowSound449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row449 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck449, numericCheck449, reducedZero449 B hB hF, mul_zero]

theorem reducedZero450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource450 (mixedVector B) = 0 := by
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm536, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1383, h1388, h1391, h1406, h3077, h4091, reducedSource450] using sourceEq536 B hB

theorem rowSound450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row450 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck450, numericCheck450, reducedZero450 B hB hF, mul_zero]

theorem reducedZero451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource451 (mixedVector B) = 0 := by
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm537, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2470, h2981, h2984, h3077, h3800, h4091, reducedSource451] using sourceEq537 B hB

theorem rowSound451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row451 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck451, numericCheck451, reducedZero451 B hB hF, mul_zero]

theorem reducedZero452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource452 (mixedVector B) = 0 := by
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4891 : mixedVector B (Sum.inr 4891) = Sparse.eval nodeValue4891 (mixedVector B) := by
    change mixedMoment B node4891 node4891Labels = _
    exact sound4891 B hB hF
  have h5097 : mixedVector B (Sum.inr 5097) = Sparse.eval nodeValue5097 (mixedVector B) := by
    change mixedMoment B node5097 node5097Labels = _
    exact sound5097 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5103 : mixedVector B (Sum.inr 5103) = Sparse.eval nodeValue5103 (mixedVector B) := by
    change mixedMoment B node5103 node5103Labels = _
    exact sound5103 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5250 : mixedVector B (Sum.inr 5250) = Sparse.eval nodeValue5250 (mixedVector B) := by
    change mixedMoment B node5250 node5250Labels = _
    exact sound5250 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5277 : mixedVector B (Sum.inr 5277) = Sparse.eval nodeValue5277 (mixedVector B) := by
    change mixedMoment B node5277 node5277Labels = _
    exact sound5277 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5287 : mixedVector B (Sum.inr 5287) = Sparse.eval nodeValue5287 (mixedVector B) := by
    change mixedMoment B node5287 node5287Labels = _
    exact sound5287 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm538, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4885, h4888, h4889, h4891, h5097, h5099, h5103, h5241, h5248, h5250, h5251, h5254, h5270, h5274, h5277, h5282, h5284, h5287, h5293, h5294, h5302, reducedSource452] using sourceEq538 B hB

theorem rowSound452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row452 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck452, numericCheck452, reducedZero452 B hB hF, mul_zero]

theorem reducedZero453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource453 (mixedVector B) = 0 := by
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h2745 : mixedVector B (Sum.inr 2745) = Sparse.eval nodeValue2745 (mixedVector B) := by
    change mixedMoment B node2745 node2745Labels = _
    exact sound2745 B hB hF
  have h2746 : mixedVector B (Sum.inr 2746) = Sparse.eval nodeValue2746 (mixedVector B) := by
    change mixedMoment B node2746 node2746Labels = _
    exact sound2746 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3003 : mixedVector B (Sum.inr 3003) = Sparse.eval nodeValue3003 (mixedVector B) := by
    change mixedMoment B node3003 node3003Labels = _
    exact sound3003 B hB hF
  have h3081 : mixedVector B (Sum.inr 3081) = Sparse.eval nodeValue3081 (mixedVector B) := by
    change mixedMoment B node3081 node3081Labels = _
    exact sound3081 B hB hF
  have h3106 : mixedVector B (Sum.inr 3106) = Sparse.eval nodeValue3106 (mixedVector B) := by
    change mixedMoment B node3106 node3106Labels = _
    exact sound3106 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  simpa only [sourceForm539, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2233, h2244, h2245, h2253, h2709, h2710, h2714, h2745, h2746, h2751, h2753, h2754, h2758, h2759, h2767, h2768, h2776, h3003, h3081, h3106, h3112, reducedSource453] using sourceEq539 B hB

theorem rowSound453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row453 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck453, numericCheck453, reducedZero453 B hB hF, mul_zero]

theorem reducedZero454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource454 (mixedVector B) = 0 := by
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3058 : mixedVector B (Sum.inr 3058) = Sparse.eval nodeValue3058 (mixedVector B) := by
    change mixedMoment B node3058 node3058Labels = _
    exact sound3058 B hB hF
  have h3059 : mixedVector B (Sum.inr 3059) = Sparse.eval nodeValue3059 (mixedVector B) := by
    change mixedMoment B node3059 node3059Labels = _
    exact sound3059 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3065 : mixedVector B (Sum.inr 3065) = Sparse.eval nodeValue3065 (mixedVector B) := by
    change mixedMoment B node3065 node3065Labels = _
    exact sound3065 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  simpa only [sourceForm540, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2694, h2704, h2705, h2742, h3016, h3024, h3025, h3054, h3058, h3059, h3064, h3065, h3075, h3077, h3078, h3101, h3102, h3221, h3222, h3223, h3227, reducedSource454] using sourceEq540 B hB

theorem rowSound454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row454 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck454, numericCheck454, reducedZero454 B hB hF, mul_zero]

theorem reducedZero455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource455 (mixedVector B) = 0 := by
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h3493 : mixedVector B (Sum.inr 3493) = Sparse.eval nodeValue3493 (mixedVector B) := by
    change mixedMoment B node3493 node3493Labels = _
    exact sound3493 B hB hF
  have h3498 : mixedVector B (Sum.inr 3498) = Sparse.eval nodeValue3498 (mixedVector B) := by
    change mixedMoment B node3498 node3498Labels = _
    exact sound3498 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm541, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2509, h3493, h3498, h3547, h3625, h4084, reducedSource455] using sourceEq541 B hB

theorem rowSound455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row455 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck455, numericCheck455, reducedZero455 B hB hF, mul_zero]

theorem reducedZero456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource456 (mixedVector B) = 0 := by
  have h995 : mixedVector B (Sum.inr 995) = Sparse.eval nodeValue995 (mixedVector B) := by
    change mixedMoment B node995 node995Labels = _
    exact sound995 B hB hF
  have h997 : mixedVector B (Sum.inr 997) = Sparse.eval nodeValue997 (mixedVector B) := by
    change mixedMoment B node997 node997Labels = _
    exact sound997 B hB hF
  have h1001 : mixedVector B (Sum.inr 1001) = Sparse.eval nodeValue1001 (mixedVector B) := by
    change mixedMoment B node1001 node1001Labels = _
    exact sound1001 B hB hF
  have h1078 : mixedVector B (Sum.inr 1078) = Sparse.eval nodeValue1078 (mixedVector B) := by
    change mixedMoment B node1078 node1078Labels = _
    exact sound1078 B hB hF
  have h2396 : mixedVector B (Sum.inr 2396) = Sparse.eval nodeValue2396 (mixedVector B) := by
    change mixedMoment B node2396 node2396Labels = _
    exact sound2396 B hB hF
  have h2397 : mixedVector B (Sum.inr 2397) = Sparse.eval nodeValue2397 (mixedVector B) := by
    change mixedMoment B node2397 node2397Labels = _
    exact sound2397 B hB hF
  have h2401 : mixedVector B (Sum.inr 2401) = Sparse.eval nodeValue2401 (mixedVector B) := by
    change mixedMoment B node2401 node2401Labels = _
    exact sound2401 B hB hF
  have h2457 : mixedVector B (Sum.inr 2457) = Sparse.eval nodeValue2457 (mixedVector B) := by
    change mixedMoment B node2457 node2457Labels = _
    exact sound2457 B hB hF
  have h2460 : mixedVector B (Sum.inr 2460) = Sparse.eval nodeValue2460 (mixedVector B) := by
    change mixedMoment B node2460 node2460Labels = _
    exact sound2460 B hB hF
  have h2507 : mixedVector B (Sum.inr 2507) = Sparse.eval nodeValue2507 (mixedVector B) := by
    change mixedMoment B node2507 node2507Labels = _
    exact sound2507 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2775 : mixedVector B (Sum.inr 2775) = Sparse.eval nodeValue2775 (mixedVector B) := by
    change mixedMoment B node2775 node2775Labels = _
    exact sound2775 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3887 : mixedVector B (Sum.inr 3887) = Sparse.eval nodeValue3887 (mixedVector B) := by
    change mixedMoment B node3887 node3887Labels = _
    exact sound3887 B hB hF
  simpa only [sourceForm544, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h995, h997, h1001, h1078, h2396, h2397, h2401, h2457, h2460, h2507, h2700, h2702, h2706, h2730, h2731, h2738, h2775, h3571, h3580, h3581, h3887, reducedSource456] using sourceEq544 B hB

theorem rowSound456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row456 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck456, numericCheck456, reducedZero456 B hB hF, mul_zero]

theorem reducedZero457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource457 (mixedVector B) = 0 := by
  have h1250 : mixedVector B (Sum.inr 1250) = Sparse.eval nodeValue1250 (mixedVector B) := by
    change mixedMoment B node1250 node1250Labels = _
    exact sound1250 B hB hF
  have h1252 : mixedVector B (Sum.inr 1252) = Sparse.eval nodeValue1252 (mixedVector B) := by
    change mixedMoment B node1252 node1252Labels = _
    exact sound1252 B hB hF
  have h1253 : mixedVector B (Sum.inr 1253) = Sparse.eval nodeValue1253 (mixedVector B) := by
    change mixedMoment B node1253 node1253Labels = _
    exact sound1253 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm545, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1250, h1252, h1253, h1270, h2754, h4091, reducedSource457] using sourceEq545 B hB

theorem rowSound457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row457 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck457, numericCheck457, reducedZero457 B hB hF, mul_zero]

theorem reducedZero458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource458 (mixedVector B) = 0 := by
  have h1250 : mixedVector B (Sum.inr 1250) = Sparse.eval nodeValue1250 (mixedVector B) := by
    change mixedMoment B node1250 node1250Labels = _
    exact sound1250 B hB hF
  have h2625 : mixedVector B (Sum.inr 2625) = Sparse.eval nodeValue2625 (mixedVector B) := by
    change mixedMoment B node2625 node2625Labels = _
    exact sound2625 B hB hF
  have h2746 : mixedVector B (Sum.inr 2746) = Sparse.eval nodeValue2746 (mixedVector B) := by
    change mixedMoment B node2746 node2746Labels = _
    exact sound2746 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm546, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1250, h2625, h2746, h2750, h2754, h4091, reducedSource458] using sourceEq546 B hB

theorem rowSound458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row458 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck458, numericCheck458, reducedZero458 B hB hF, mul_zero]

theorem reducedZero459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource459 (mixedVector B) = 0 := by
  have h1421 : mixedVector B (Sum.inr 1421) = Sparse.eval nodeValue1421 (mixedVector B) := by
    change mixedMoment B node1421 node1421Labels = _
    exact sound1421 B hB hF
  have h2564 : mixedVector B (Sum.inr 2564) = Sparse.eval nodeValue2564 (mixedVector B) := by
    change mixedMoment B node2564 node2564Labels = _
    exact sound2564 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm547, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1421, h2564, h2573, h2754, h3037, h4091, reducedSource459] using sourceEq547 B hB

theorem rowSound459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row459 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck459, numericCheck459, reducedZero459 B hB hF, mul_zero]

theorem reducedZero460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource460 (mixedVector B) = 0 := by
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm548, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1270, h2573, h2641, h2754, h2764, h4091, reducedSource460] using sourceEq548 B hB

theorem rowSound460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row460 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck460, numericCheck460, reducedZero460 B hB hF, mul_zero]

theorem reducedZero461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource461 (mixedVector B) = 0 := by
  have h4441 : mixedVector B (Sum.inr 4441) = Sparse.eval nodeValue4441 (mixedVector B) := by
    change mixedMoment B node4441 node4441Labels = _
    exact sound4441 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4443 : mixedVector B (Sum.inr 4443) = Sparse.eval nodeValue4443 (mixedVector B) := by
    change mixedMoment B node4443 node4443Labels = _
    exact sound4443 B hB hF
  have h4462 : mixedVector B (Sum.inr 4462) = Sparse.eval nodeValue4462 (mixedVector B) := by
    change mixedMoment B node4462 node4462Labels = _
    exact sound4462 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h5066 : mixedVector B (Sum.inr 5066) = Sparse.eval nodeValue5066 (mixedVector B) := by
    change mixedMoment B node5066 node5066Labels = _
    exact sound5066 B hB hF
  have h5077 : mixedVector B (Sum.inr 5077) = Sparse.eval nodeValue5077 (mixedVector B) := by
    change mixedMoment B node5077 node5077Labels = _
    exact sound5077 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5278 : mixedVector B (Sum.inr 5278) = Sparse.eval nodeValue5278 (mixedVector B) := by
    change mixedMoment B node5278 node5278Labels = _
    exact sound5278 B hB hF
  have h5279 : mixedVector B (Sum.inr 5279) = Sparse.eval nodeValue5279 (mixedVector B) := by
    change mixedMoment B node5279 node5279Labels = _
    exact sound5279 B hB hF
  have h5288 : mixedVector B (Sum.inr 5288) = Sparse.eval nodeValue5288 (mixedVector B) := by
    change mixedMoment B node5288 node5288Labels = _
    exact sound5288 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  simpa only [sourceForm549, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4441, h4442, h4443, h4462, h4792, h4807, h4890, h5066, h5077, h5150, h5151, h5173, h5256, h5270, h5271, h5278, h5279, h5288, h5290, h5295, h5306, reducedSource461] using sourceEq549 B hB

theorem rowSound461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row461 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck461, numericCheck461, reducedZero461 B hB hF, mul_zero]

theorem reducedZero462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource462 (mixedVector B) = 0 := by
  have h1023 : mixedVector B (Sum.inr 1023) = Sparse.eval nodeValue1023 (mixedVector B) := by
    change mixedMoment B node1023 node1023Labels = _
    exact sound1023 B hB hF
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h1025 : mixedVector B (Sum.inr 1025) = Sparse.eval nodeValue1025 (mixedVector B) := by
    change mixedMoment B node1025 node1025Labels = _
    exact sound1025 B hB hF
  have h1045 : mixedVector B (Sum.inr 1045) = Sparse.eval nodeValue1045 (mixedVector B) := by
    change mixedMoment B node1045 node1045Labels = _
    exact sound1045 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2472 : mixedVector B (Sum.inr 2472) = Sparse.eval nodeValue2472 (mixedVector B) := by
    change mixedMoment B node2472 node2472Labels = _
    exact sound2472 B hB hF
  have h2484 : mixedVector B (Sum.inr 2484) = Sparse.eval nodeValue2484 (mixedVector B) := by
    change mixedMoment B node2484 node2484Labels = _
    exact sound2484 B hB hF
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h2574 : mixedVector B (Sum.inr 2574) = Sparse.eval nodeValue2574 (mixedVector B) := by
    change mixedMoment B node2574 node2574Labels = _
    exact sound2574 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h2747 : mixedVector B (Sum.inr 2747) = Sparse.eval nodeValue2747 (mixedVector B) := by
    change mixedMoment B node2747 node2747Labels = _
    exact sound2747 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2755 : mixedVector B (Sum.inr 2755) = Sparse.eval nodeValue2755 (mixedVector B) := by
    change mixedMoment B node2755 node2755Labels = _
    exact sound2755 B hB hF
  have h2760 : mixedVector B (Sum.inr 2760) = Sparse.eval nodeValue2760 (mixedVector B) := by
    change mixedMoment B node2760 node2760Labels = _
    exact sound2760 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  simpa only [sourceForm550, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1023, h1024, h1025, h1045, h2471, h2472, h2484, h2573, h2574, h2575, h2600, h2747, h2748, h2754, h2755, h2760, h2764, h2769, h3085, h3109, h3120, reducedSource462] using sourceEq550 B hB

theorem rowSound462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row462 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck462, numericCheck462, reducedZero462 B hB hF, mul_zero]

theorem reducedZero463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource463 (mixedVector B) = 0 := by
  have h1654 : mixedVector B (Sum.inr 1654) = Sparse.eval nodeValue1654 (mixedVector B) := by
    change mixedMoment B node1654 node1654Labels = _
    exact sound1654 B hB hF
  have h1655 : mixedVector B (Sum.inr 1655) = Sparse.eval nodeValue1655 (mixedVector B) := by
    change mixedMoment B node1655 node1655Labels = _
    exact sound1655 B hB hF
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2668 : mixedVector B (Sum.inr 2668) = Sparse.eval nodeValue2668 (mixedVector B) := by
    change mixedMoment B node2668 node2668Labels = _
    exact sound2668 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h2717 : mixedVector B (Sum.inr 2717) = Sparse.eval nodeValue2717 (mixedVector B) := by
    change mixedMoment B node2717 node2717Labels = _
    exact sound2717 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2784 : mixedVector B (Sum.inr 2784) = Sparse.eval nodeValue2784 (mixedVector B) := by
    change mixedMoment B node2784 node2784Labels = _
    exact sound2784 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h3073 : mixedVector B (Sum.inr 3073) = Sparse.eval nodeValue3073 (mixedVector B) := by
    change mixedMoment B node3073 node3073Labels = _
    exact sound3073 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3099 : mixedVector B (Sum.inr 3099) = Sparse.eval nodeValue3099 (mixedVector B) := by
    change mixedMoment B node3099 node3099Labels = _
    exact sound3099 B hB hF
  simpa only [sourceForm551, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1654, h1655, h1656, h1744, h2201, h2224, h2290, h2668, h2681, h2700, h2717, h2720, h2735, h2738, h2739, h2781, h2784, h3050, h3073, h3096, h3099, reducedSource463] using sourceEq551 B hB

theorem rowSound463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row463 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck463, numericCheck463, reducedZero463 B hB hF, mul_zero]

theorem sourceRowsAt448 : MixedData.sourceRows (448 : Fin 2425) =
    MixedData.row448 := by decide +kernel

theorem sourceRowsAt449 : MixedData.sourceRows (449 : Fin 2425) =
    MixedData.row449 := by decide +kernel

theorem sourceRowsAt450 : MixedData.sourceRows (450 : Fin 2425) =
    MixedData.row450 := by decide +kernel

theorem sourceRowsAt451 : MixedData.sourceRows (451 : Fin 2425) =
    MixedData.row451 := by decide +kernel

theorem sourceRowsAt452 : MixedData.sourceRows (452 : Fin 2425) =
    MixedData.row452 := by decide +kernel

theorem sourceRowsAt453 : MixedData.sourceRows (453 : Fin 2425) =
    MixedData.row453 := by decide +kernel

theorem sourceRowsAt454 : MixedData.sourceRows (454 : Fin 2425) =
    MixedData.row454 := by decide +kernel

theorem sourceRowsAt455 : MixedData.sourceRows (455 : Fin 2425) =
    MixedData.row455 := by decide +kernel

theorem sourceRowsAt456 : MixedData.sourceRows (456 : Fin 2425) =
    MixedData.row456 := by decide +kernel

theorem sourceRowsAt457 : MixedData.sourceRows (457 : Fin 2425) =
    MixedData.row457 := by decide +kernel

theorem sourceRowsAt458 : MixedData.sourceRows (458 : Fin 2425) =
    MixedData.row458 := by decide +kernel

theorem sourceRowsAt459 : MixedData.sourceRows (459 : Fin 2425) =
    MixedData.row459 := by decide +kernel

theorem sourceRowsAt460 : MixedData.sourceRows (460 : Fin 2425) =
    MixedData.row460 := by decide +kernel

theorem sourceRowsAt461 : MixedData.sourceRows (461 : Fin 2425) =
    MixedData.row461 := by decide +kernel

theorem sourceRowsAt462 : MixedData.sourceRows (462 : Fin 2425) =
    MixedData.row462 := by decide +kernel

theorem sourceRowsAt463 : MixedData.sourceRows (463 : Fin 2425) =
    MixedData.row463 := by decide +kernel

theorem chunkSound28 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 28) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 448 ∨ k.val = 449 ∨ k.val = 450 ∨ k.val = 451 ∨ k.val = 452 ∨ k.val = 453 ∨ k.val = 454 ∨ k.val = 455 ∨ k.val = 456 ∨ k.val = 457 ∨ k.val = 458 ∨ k.val = 459 ∨ k.val = 460 ∨ k.val = 461 ∨ k.val = 462 ∨ k.val = 463 := by omega
  rcases heq with h448 | h449 | h450 | h451 | h452 | h453 | h454 | h455 | h456 | h457 | h458 | h459 | h460 | h461 | h462 | h463
  · have he : k = (448 : Fin 2425) := Fin.ext h448
    subst k
    rw [sourceRowsAt448]
    exact rowSound448 B hB hF
  · have he : k = (449 : Fin 2425) := Fin.ext h449
    subst k
    rw [sourceRowsAt449]
    exact rowSound449 B hB hF
  · have he : k = (450 : Fin 2425) := Fin.ext h450
    subst k
    rw [sourceRowsAt450]
    exact rowSound450 B hB hF
  · have he : k = (451 : Fin 2425) := Fin.ext h451
    subst k
    rw [sourceRowsAt451]
    exact rowSound451 B hB hF
  · have he : k = (452 : Fin 2425) := Fin.ext h452
    subst k
    rw [sourceRowsAt452]
    exact rowSound452 B hB hF
  · have he : k = (453 : Fin 2425) := Fin.ext h453
    subst k
    rw [sourceRowsAt453]
    exact rowSound453 B hB hF
  · have he : k = (454 : Fin 2425) := Fin.ext h454
    subst k
    rw [sourceRowsAt454]
    exact rowSound454 B hB hF
  · have he : k = (455 : Fin 2425) := Fin.ext h455
    subst k
    rw [sourceRowsAt455]
    exact rowSound455 B hB hF
  · have he : k = (456 : Fin 2425) := Fin.ext h456
    subst k
    rw [sourceRowsAt456]
    exact rowSound456 B hB hF
  · have he : k = (457 : Fin 2425) := Fin.ext h457
    subst k
    rw [sourceRowsAt457]
    exact rowSound457 B hB hF
  · have he : k = (458 : Fin 2425) := Fin.ext h458
    subst k
    rw [sourceRowsAt458]
    exact rowSound458 B hB hF
  · have he : k = (459 : Fin 2425) := Fin.ext h459
    subst k
    rw [sourceRowsAt459]
    exact rowSound459 B hB hF
  · have he : k = (460 : Fin 2425) := Fin.ext h460
    subst k
    rw [sourceRowsAt460]
    exact rowSound460 B hB hF
  · have he : k = (461 : Fin 2425) := Fin.ext h461
    subst k
    rw [sourceRowsAt461]
    exact rowSound461 B hB hF
  · have he : k = (462 : Fin 2425) := Fin.ext h462
    subst k
    rw [sourceRowsAt462]
    exact rowSound462 B hB hF
  · have he : k = (463 : Fin 2425) := Fin.ext h463
    subst k
    rw [sourceRowsAt463]
    exact rowSound463 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
