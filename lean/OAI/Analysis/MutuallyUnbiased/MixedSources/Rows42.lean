import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources24

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource672 (mixedVector B) = 0 := by
  have h2571 : mixedVector B (Sum.inr 2571) = Sparse.eval nodeValue2571 (mixedVector B) := by
    change mixedMoment B node2571 node2571Labels = _
    exact sound2571 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h2977 : mixedVector B (Sum.inr 2977) = Sparse.eval nodeValue2977 (mixedVector B) := by
    change mixedMoment B node2977 node2977Labels = _
    exact sound2977 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm774, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2571, h2974, h2975, h2977, h3051, h3848, h4092, reducedSource672] using sourceEq774 B hB

theorem rowSound672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row672 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck672, numericCheck672, reducedZero672 B hB hF, mul_zero]

theorem reducedZero673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource673 (mixedVector B) = 0 := by
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm775, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2878, h2881, h2882, h2885, h3051, h3961, h4092, reducedSource673] using sourceEq775 B hB

theorem rowSound673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row673 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck673, numericCheck673, reducedZero673 B hB hF, mul_zero]

theorem reducedZero674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource674 (mixedVector B) = 0 := by
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm776, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2575, h3043, h3044, h3045, h3051, h3850, h4092, reducedSource674] using sourceEq776 B hB

theorem rowSound674 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row674 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck674, numericCheck674, reducedZero674 B hB hF, mul_zero]

theorem reducedZero675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource675 (mixedVector B) = 0 := by
  have h2118 : mixedVector B (Sum.inr 2118) = Sparse.eval nodeValue2118 (mixedVector B) := by
    change mixedMoment B node2118 node2118Labels = _
    exact sound2118 B hB hF
  have h2119 : mixedVector B (Sum.inr 2119) = Sparse.eval nodeValue2119 (mixedVector B) := by
    change mixedMoment B node2119 node2119Labels = _
    exact sound2119 B hB hF
  have h2123 : mixedVector B (Sum.inr 2123) = Sparse.eval nodeValue2123 (mixedVector B) := by
    change mixedMoment B node2123 node2123Labels = _
    exact sound2123 B hB hF
  have h2132 : mixedVector B (Sum.inr 2132) = Sparse.eval nodeValue2132 (mixedVector B) := by
    change mixedMoment B node2132 node2132Labels = _
    exact sound2132 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2565 : mixedVector B (Sum.inr 2565) = Sparse.eval nodeValue2565 (mixedVector B) := by
    change mixedMoment B node2565 node2565Labels = _
    exact sound2565 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2585 : mixedVector B (Sum.inr 2585) = Sparse.eval nodeValue2585 (mixedVector B) := by
    change mixedMoment B node2585 node2585Labels = _
    exact sound2585 B hB hF
  have h2727 : mixedVector B (Sum.inr 2727) = Sparse.eval nodeValue2727 (mixedVector B) := by
    change mixedMoment B node2727 node2727Labels = _
    exact sound2727 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2756 : mixedVector B (Sum.inr 2756) = Sparse.eval nodeValue2756 (mixedVector B) := by
    change mixedMoment B node2756 node2756Labels = _
    exact sound2756 B hB hF
  have h2757 : mixedVector B (Sum.inr 2757) = Sparse.eval nodeValue2757 (mixedVector B) := by
    change mixedMoment B node2757 node2757Labels = _
    exact sound2757 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h2772 : mixedVector B (Sum.inr 2772) = Sparse.eval nodeValue2772 (mixedVector B) := by
    change mixedMoment B node2772 node2772Labels = _
    exact sound2772 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2775 : mixedVector B (Sum.inr 2775) = Sparse.eval nodeValue2775 (mixedVector B) := by
    change mixedMoment B node2775 node2775Labels = _
    exact sound2775 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3115 : mixedVector B (Sum.inr 3115) = Sparse.eval nodeValue3115 (mixedVector B) := by
    change mixedMoment B node3115 node3115Labels = _
    exact sound3115 B hB hF
  have h3116 : mixedVector B (Sum.inr 3116) = Sparse.eval nodeValue3116 (mixedVector B) := by
    change mixedMoment B node3116 node3116Labels = _
    exact sound3116 B hB hF
  simpa only [sourceForm778, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2118, h2119, h2123, h2132, h2220, h2250, h2274, h2275, h2277, h2565, h2575, h2585, h2727, h2728, h2730, h2748, h2750, h2756, h2757, h2763, h2764, h2766, h2772, h2773, h2775, h3091, h3109, h3115, h3116, reducedSource675] using sourceEq778 B hB

theorem rowSound675 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row675 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck675, numericCheck675, reducedZero675 B hB hF, mul_zero]

theorem reducedZero676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource676 (mixedVector B) = 0 := by
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3380 : mixedVector B (Sum.inr 3380) = Sparse.eval nodeValue3380 (mixedVector B) := by
    change mixedMoment B node3380 node3380Labels = _
    exact sound3380 B hB hF
  have h3394 : mixedVector B (Sum.inr 3394) = Sparse.eval nodeValue3394 (mixedVector B) := by
    change mixedMoment B node3394 node3394Labels = _
    exact sound3394 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm780, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2930, h3376, h3380, h3394, h3534, h3573, h4083, reducedSource676] using sourceEq780 B hB

theorem rowSound676 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row676 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck676, numericCheck676, reducedZero676 B hB hF, mul_zero]

theorem reducedZero677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource677 (mixedVector B) = 0 := by
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2926 : mixedVector B (Sum.inr 2926) = Sparse.eval nodeValue2926 (mixedVector B) := by
    change mixedMoment B node2926 node2926Labels = _
    exact sound2926 B hB hF
  have h3551 : mixedVector B (Sum.inr 3551) = Sparse.eval nodeValue3551 (mixedVector B) := by
    change mixedMoment B node3551 node3551Labels = _
    exact sound3551 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm781, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2089, h2926, h3551, h3567, h3571, h3573, h4083, reducedSource677] using sourceEq781 B hB

theorem rowSound677 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row677 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck677, numericCheck677, reducedZero677 B hB hF, mul_zero]

theorem reducedZero678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource678 (mixedVector B) = 0 := by
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2929 : mixedVector B (Sum.inr 2929) = Sparse.eval nodeValue2929 (mixedVector B) := by
    change mixedMoment B node2929 node2929Labels = _
    exact sound2929 B hB hF
  have h3149 : mixedVector B (Sum.inr 3149) = Sparse.eval nodeValue3149 (mixedVector B) := by
    change mixedMoment B node3149 node3149Labels = _
    exact sound3149 B hB hF
  have h3152 : mixedVector B (Sum.inr 3152) = Sparse.eval nodeValue3152 (mixedVector B) := by
    change mixedMoment B node3152 node3152Labels = _
    exact sound3152 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm782, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2092, h2929, h3149, h3152, h3158, h3573, h4083, reducedSource678] using sourceEq782 B hB

theorem rowSound678 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row678 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck678, numericCheck678, reducedZero678 B hB hF, mul_zero]

theorem reducedZero679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource679 (mixedVector B) = 0 := by
  have h2926 : mixedVector B (Sum.inr 2926) = Sparse.eval nodeValue2926 (mixedVector B) := by
    change mixedMoment B node2926 node2926Labels = _
    exact sound2926 B hB hF
  have h2929 : mixedVector B (Sum.inr 2929) = Sparse.eval nodeValue2929 (mixedVector B) := by
    change mixedMoment B node2929 node2929Labels = _
    exact sound2929 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2956 : mixedVector B (Sum.inr 2956) = Sparse.eval nodeValue2956 (mixedVector B) := by
    change mixedMoment B node2956 node2956Labels = _
    exact sound2956 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm783, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2926, h2929, h2930, h2956, h3079, h3573, h4083, reducedSource679] using sourceEq783 B hB

theorem rowSound679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row679 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck679, numericCheck679, reducedZero679 B hB hF, mul_zero]

theorem reducedZero680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource680 (mixedVector B) = 0 := by
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm784, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2110, h3079, h3505, h3573, h3581, h4083, reducedSource680] using sourceEq784 B hB

theorem rowSound680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row680 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck680, numericCheck680, reducedZero680 B hB hF, mul_zero]

theorem reducedZero681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource681 (mixedVector B) = 0 := by
  have h3152 : mixedVector B (Sum.inr 3152) = Sparse.eval nodeValue3152 (mixedVector B) := by
    change mixedMoment B node3152 node3152Labels = _
    exact sound3152 B hB hF
  have h3380 : mixedVector B (Sum.inr 3380) = Sparse.eval nodeValue3380 (mixedVector B) := by
    change mixedMoment B node3380 node3380Labels = _
    exact sound3380 B hB hF
  have h3551 : mixedVector B (Sum.inr 3551) = Sparse.eval nodeValue3551 (mixedVector B) := by
    change mixedMoment B node3551 node3551Labels = _
    exact sound3551 B hB hF
  have h3552 : mixedVector B (Sum.inr 3552) = Sparse.eval nodeValue3552 (mixedVector B) := by
    change mixedMoment B node3552 node3552Labels = _
    exact sound3552 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm785, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3152, h3380, h3551, h3552, h3573, h4083, reducedSource681] using sourceEq785 B hB

theorem rowSound681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row681 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck681, numericCheck681, reducedZero681 B hB hF, mul_zero]

theorem reducedZero682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource682 (mixedVector B) = 0 := by
  have h4473 : mixedVector B (Sum.inr 4473) = Sparse.eval nodeValue4473 (mixedVector B) := by
    change mixedMoment B node4473 node4473Labels = _
    exact sound4473 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4494 : mixedVector B (Sum.inr 4494) = Sparse.eval nodeValue4494 (mixedVector B) := by
    change mixedMoment B node4494 node4494Labels = _
    exact sound4494 B hB hF
  have h5085 : mixedVector B (Sum.inr 5085) = Sparse.eval nodeValue5085 (mixedVector B) := by
    change mixedMoment B node5085 node5085Labels = _
    exact sound5085 B hB hF
  have h5097 : mixedVector B (Sum.inr 5097) = Sparse.eval nodeValue5097 (mixedVector B) := by
    change mixedMoment B node5097 node5097Labels = _
    exact sound5097 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  simpa only [sourceForm788, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4473, h4474, h4494, h5085, h5097, h5202, h5203, h5265, h5266, h5270, h5447, h5450, h5474, reducedSource682] using sourceEq788 B hB

theorem rowSound682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row682 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck682, numericCheck682, reducedZero682 B hB hF, mul_zero]

theorem reducedZero683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource683 (mixedVector B) = 0 := by
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h3058 : mixedVector B (Sum.inr 3058) = Sparse.eval nodeValue3058 (mixedVector B) := by
    change mixedMoment B node3058 node3058Labels = _
    exact sound3058 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3461 : mixedVector B (Sum.inr 3461) = Sparse.eval nodeValue3461 (mixedVector B) := by
    change mixedMoment B node3461 node3461Labels = _
    exact sound3461 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3617 : mixedVector B (Sum.inr 3617) = Sparse.eval nodeValue3617 (mixedVector B) := by
    change mixedMoment B node3617 node3617Labels = _
    exact sound3617 B hB hF
  have h3621 : mixedVector B (Sum.inr 3621) = Sparse.eval nodeValue3621 (mixedVector B) := by
    change mixedMoment B node3621 node3621Labels = _
    exact sound3621 B hB hF
  have h3962 : mixedVector B (Sum.inr 3962) = Sparse.eval nodeValue3962 (mixedVector B) := by
    change mixedMoment B node3962 node3962Labels = _
    exact sound3962 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4029 : mixedVector B (Sum.inr 4029) = Sparse.eval nodeValue4029 (mixedVector B) := by
    change mixedMoment B node4029 node4029Labels = _
    exact sound4029 B hB hF
  simpa only [sourceForm789, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1699, h1700, h1709, h3058, h3075, h3461, h3526, h3535, h3617, h3621, h3962, h4025, h4029, reducedSource683] using sourceEq789 B hB

theorem rowSound683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row683 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck683, numericCheck683, reducedZero683 B hB hF, mul_zero]

theorem reducedZero684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource684 (mixedVector B) = 0 := by
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3962 : mixedVector B (Sum.inr 3962) = Sparse.eval nodeValue3962 (mixedVector B) := by
    change mixedMoment B node3962 node3962Labels = _
    exact sound3962 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm790, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3053, h3909, h3910, h3962, h4091, reducedSource684] using sourceEq790 B hB

theorem rowSound684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row684 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck684, numericCheck684, reducedZero684 B hB hF, mul_zero]

theorem reducedZero685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource685 (mixedVector B) = 0 := by
  have h2746 : mixedVector B (Sum.inr 2746) = Sparse.eval nodeValue2746 (mixedVector B) := by
    change mixedMoment B node2746 node2746Labels = _
    exact sound2746 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm791, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2746, h2976, h3053, h3909, h4091, reducedSource685] using sourceEq791 B hB

theorem rowSound685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row685 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck685, numericCheck685, reducedZero685 B hB hF, mul_zero]

theorem reducedZero686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource686 (mixedVector B) = 0 := by
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h4879 : mixedVector B (Sum.inr 4879) = Sparse.eval nodeValue4879 (mixedVector B) := by
    change mixedMoment B node4879 node4879Labels = _
    exact sound4879 B hB hF
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h4886 : mixedVector B (Sum.inr 4886) = Sparse.eval nodeValue4886 (mixedVector B) := by
    change mixedMoment B node4886 node4886Labels = _
    exact sound4886 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5286 : mixedVector B (Sum.inr 5286) = Sparse.eval nodeValue5286 (mixedVector B) := by
    change mixedMoment B node5286 node5286Labels = _
    exact sound5286 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  simpa only [sourceForm792, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4878, h4879, h4885, h4886, h4889, h5227, h5237, h5265, h5273, h5283, h5286, h5292, h5299, reducedSource686] using sourceEq792 B hB

theorem rowSound686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row686 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck686, numericCheck686, reducedZero686 B hB hF, mul_zero]

theorem reducedZero687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource687 (mixedVector B) = 0 := by
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3076 : mixedVector B (Sum.inr 3076) = Sparse.eval nodeValue3076 (mixedVector B) := by
    change mixedMoment B node3076 node3076Labels = _
    exact sound3076 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223 B hB hF
  simpa only [sourceForm793, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2234, h2235, h2246, h2671, h2684, h2741, h3023, h3037, h3051, h3076, h3100, h3221, h3223, reducedSource687] using sourceEq793 B hB

theorem rowSound687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row687 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck687, numericCheck687, reducedZero687 B hB hF, mul_zero]

theorem sourceRowsAt672 : MixedData.sourceRows (672 : Fin 2425) =
    MixedData.row672 := by decide +kernel

theorem sourceRowsAt673 : MixedData.sourceRows (673 : Fin 2425) =
    MixedData.row673 := by decide +kernel

theorem sourceRowsAt674 : MixedData.sourceRows (674 : Fin 2425) =
    MixedData.row674 := by decide +kernel

theorem sourceRowsAt675 : MixedData.sourceRows (675 : Fin 2425) =
    MixedData.row675 := by decide +kernel

theorem sourceRowsAt676 : MixedData.sourceRows (676 : Fin 2425) =
    MixedData.row676 := by decide +kernel

theorem sourceRowsAt677 : MixedData.sourceRows (677 : Fin 2425) =
    MixedData.row677 := by decide +kernel

theorem sourceRowsAt678 : MixedData.sourceRows (678 : Fin 2425) =
    MixedData.row678 := by decide +kernel

theorem sourceRowsAt679 : MixedData.sourceRows (679 : Fin 2425) =
    MixedData.row679 := by decide +kernel

theorem sourceRowsAt680 : MixedData.sourceRows (680 : Fin 2425) =
    MixedData.row680 := by decide +kernel

theorem sourceRowsAt681 : MixedData.sourceRows (681 : Fin 2425) =
    MixedData.row681 := by decide +kernel

theorem sourceRowsAt682 : MixedData.sourceRows (682 : Fin 2425) =
    MixedData.row682 := by decide +kernel

theorem sourceRowsAt683 : MixedData.sourceRows (683 : Fin 2425) =
    MixedData.row683 := by decide +kernel

theorem sourceRowsAt684 : MixedData.sourceRows (684 : Fin 2425) =
    MixedData.row684 := by decide +kernel

theorem sourceRowsAt685 : MixedData.sourceRows (685 : Fin 2425) =
    MixedData.row685 := by decide +kernel

theorem sourceRowsAt686 : MixedData.sourceRows (686 : Fin 2425) =
    MixedData.row686 := by decide +kernel

theorem sourceRowsAt687 : MixedData.sourceRows (687 : Fin 2425) =
    MixedData.row687 := by decide +kernel

theorem chunkSound42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 42) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 672 ∨ k.val = 673 ∨ k.val = 674 ∨ k.val = 675 ∨ k.val = 676 ∨ k.val = 677 ∨ k.val = 678 ∨ k.val = 679 ∨ k.val = 680 ∨ k.val = 681 ∨ k.val = 682 ∨ k.val = 683 ∨ k.val = 684 ∨ k.val = 685 ∨ k.val = 686 ∨ k.val = 687 := by omega
  rcases heq with h672 | h673 | h674 | h675 | h676 | h677 | h678 | h679 | h680 | h681 | h682 | h683 | h684 | h685 | h686 | h687
  · have he : k = (672 : Fin 2425) := Fin.ext h672
    subst k
    rw [sourceRowsAt672]
    exact rowSound672 B hB hF
  · have he : k = (673 : Fin 2425) := Fin.ext h673
    subst k
    rw [sourceRowsAt673]
    exact rowSound673 B hB hF
  · have he : k = (674 : Fin 2425) := Fin.ext h674
    subst k
    rw [sourceRowsAt674]
    exact rowSound674 B hB hF
  · have he : k = (675 : Fin 2425) := Fin.ext h675
    subst k
    rw [sourceRowsAt675]
    exact rowSound675 B hB hF
  · have he : k = (676 : Fin 2425) := Fin.ext h676
    subst k
    rw [sourceRowsAt676]
    exact rowSound676 B hB hF
  · have he : k = (677 : Fin 2425) := Fin.ext h677
    subst k
    rw [sourceRowsAt677]
    exact rowSound677 B hB hF
  · have he : k = (678 : Fin 2425) := Fin.ext h678
    subst k
    rw [sourceRowsAt678]
    exact rowSound678 B hB hF
  · have he : k = (679 : Fin 2425) := Fin.ext h679
    subst k
    rw [sourceRowsAt679]
    exact rowSound679 B hB hF
  · have he : k = (680 : Fin 2425) := Fin.ext h680
    subst k
    rw [sourceRowsAt680]
    exact rowSound680 B hB hF
  · have he : k = (681 : Fin 2425) := Fin.ext h681
    subst k
    rw [sourceRowsAt681]
    exact rowSound681 B hB hF
  · have he : k = (682 : Fin 2425) := Fin.ext h682
    subst k
    rw [sourceRowsAt682]
    exact rowSound682 B hB hF
  · have he : k = (683 : Fin 2425) := Fin.ext h683
    subst k
    rw [sourceRowsAt683]
    exact rowSound683 B hB hF
  · have he : k = (684 : Fin 2425) := Fin.ext h684
    subst k
    rw [sourceRowsAt684]
    exact rowSound684 B hB hF
  · have he : k = (685 : Fin 2425) := Fin.ext h685
    subst k
    rw [sourceRowsAt685]
    exact rowSound685 B hB hF
  · have he : k = (686 : Fin 2425) := Fin.ext h686
    subst k
    rw [sourceRowsAt686]
    exact rowSound686 B hB hF
  · have he : k = (687 : Fin 2425) := Fin.ext h687
    subst k
    rw [sourceRowsAt687]
    exact rowSound687 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
