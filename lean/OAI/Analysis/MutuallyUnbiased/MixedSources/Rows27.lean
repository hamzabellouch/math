import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources16

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource432 (mixedVector B) = 0 := by
  have h2857 : mixedVector B (Sum.inr 2857) = Sparse.eval nodeValue2857 (mixedVector B) := by
    change mixedMoment B node2857 node2857Labels = _
    exact sound2857 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h2985 : mixedVector B (Sum.inr 2985) = Sparse.eval nodeValue2985 (mixedVector B) := by
    change mixedMoment B node2985 node2985Labels = _
    exact sound2985 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm516, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2857, h2981, h2985, h3078, h3953, h4091, reducedSource432] using sourceEq516 B hB

theorem rowSound432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row432 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck432, numericCheck432, reducedZero432 B hB hF, mul_zero]

theorem reducedZero433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource433 (mixedVector B) = 0 := by
  have h1407 : mixedVector B (Sum.inr 1407) = Sparse.eval nodeValue1407 (mixedVector B) := by
    change mixedMoment B node1407 node1407Labels = _
    exact sound1407 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h2985 : mixedVector B (Sum.inr 2985) = Sparse.eval nodeValue2985 (mixedVector B) := by
    change mixedMoment B node2985 node2985Labels = _
    exact sound2985 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm517, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1407, h2955, h2985, h3078, h3092, h3097, h4091, reducedSource433] using sourceEq517 B hB

theorem rowSound433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row433 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck433, numericCheck433, reducedZero433 B hB hF, mul_zero]

theorem reducedZero434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource434 (mixedVector B) = 0 := by
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm518, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2865, h2925, h2931, h2955, h3078, h3958, h4091, reducedSource434] using sourceEq518 B hB

theorem rowSound434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row434 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck434, numericCheck434, reducedZero434 B hB hF, mul_zero]

theorem reducedZero435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource435 (mixedVector B) = 0 := by
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm519, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1391, h2931, h2981, h3077, h3078, h4091, reducedSource435] using sourceEq519 B hB

theorem rowSound435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row435 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck435, numericCheck435, reducedZero435 B hB hF, mul_zero]

theorem reducedZero436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource436 (mixedVector B) = 0 := by
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm520, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3031, h3068, h3078, h3092, h3885, h4091, reducedSource436] using sourceEq520 B hB

theorem rowSound436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row436 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck436, numericCheck436, reducedZero436 B hB hF, mul_zero]

theorem reducedZero437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource437 (mixedVector B) = 0 := by
  have h1389 : mixedVector B (Sum.inr 1389) = Sparse.eval nodeValue1389 (mixedVector B) := by
    change mixedMoment B node1389 node1389Labels = _
    exact sound1389 B hB hF
  have h2857 : mixedVector B (Sum.inr 2857) = Sparse.eval nodeValue2857 (mixedVector B) := by
    change mixedMoment B node2857 node2857Labels = _
    exact sound2857 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm521, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1389, h2857, h2865, h3031, h3078, h4091, reducedSource437] using sourceEq521 B hB

theorem rowSound437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row437 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck437, numericCheck437, reducedZero437 B hB hF, mul_zero]

theorem reducedZero438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource438 (mixedVector B) = 0 := by
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2628 : mixedVector B (Sum.inr 2628) = Sparse.eval nodeValue2628 (mixedVector B) := by
    change mixedMoment B node2628 node2628Labels = _
    exact sound2628 B hB hF
  have h2629 : mixedVector B (Sum.inr 2629) = Sparse.eval nodeValue2629 (mixedVector B) := by
    change mixedMoment B node2629 node2629Labels = _
    exact sound2629 B hB hF
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2713 : mixedVector B (Sum.inr 2713) = Sparse.eval nodeValue2713 (mixedVector B) := by
    change mixedMoment B node2713 node2713Labels = _
    exact sound2713 B hB hF
  have h2745 : mixedVector B (Sum.inr 2745) = Sparse.eval nodeValue2745 (mixedVector B) := by
    change mixedMoment B node2745 node2745Labels = _
    exact sound2745 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h3080 : mixedVector B (Sum.inr 3080) = Sparse.eval nodeValue3080 (mixedVector B) := by
    change mixedMoment B node3080 node3080Labels = _
    exact sound3080 B hB hF
  have h3106 : mixedVector B (Sum.inr 3106) = Sparse.eval nodeValue3106 (mixedVector B) := by
    change mixedMoment B node3106 node3106Labels = _
    exact sound3106 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  simpa only [sourceForm523, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2232, h2242, h2244, h2251, h2628, h2629, h2641, h2708, h2709, h2713, h2745, h2748, h2751, h2753, h2758, h2765, h2767, h2774, h3080, h3106, h3110, reducedSource438] using sourceEq523 B hB

theorem rowSound438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row438 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck438, numericCheck438, reducedZero438 B hB hF, mul_zero]

theorem reducedZero439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource439 (mixedVector B) = 0 := by
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3498 : mixedVector B (Sum.inr 3498) = Sparse.eval nodeValue3498 (mixedVector B) := by
    change mixedMoment B node3498 node3498Labels = _
    exact sound3498 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm525, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2879, h3494, h3498, h3548, h3580, h4084, reducedSource439] using sourceEq525 B hB

theorem rowSound439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row439 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck439, numericCheck439, reducedZero439 B hB hF, mul_zero]

theorem reducedZero440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource440 (mixedVector B) = 0 := by
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm526, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2104, h2106, h2108, h2262, h3580, h4084, reducedSource440] using sourceEq526 B hB

theorem rowSound440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row440 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck440, numericCheck440, reducedZero440 B hB hF, mul_zero]

theorem reducedZero441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource441 (mixedVector B) = 0 := by
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2877 : mixedVector B (Sum.inr 2877) = Sparse.eval nodeValue2877 (mixedVector B) := by
    change mixedMoment B node2877 node2877Labels = _
    exact sound2877 B hB hF
  have h3576 : mixedVector B (Sum.inr 3576) = Sparse.eval nodeValue3576 (mixedVector B) := by
    change mixedMoment B node3576 node3576Labels = _
    exact sound3576 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm527, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2104, h2877, h3576, h3580, h4084, reducedSource441] using sourceEq527 B hB

theorem rowSound441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row441 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck441, numericCheck441, reducedZero441 B hB hF, mul_zero]

theorem reducedZero442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource442 (mixedVector B) = 0 := by
  have h2877 : mixedVector B (Sum.inr 2877) = Sparse.eval nodeValue2877 (mixedVector B) := by
    change mixedMoment B node2877 node2877Labels = _
    exact sound2877 B hB hF
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h2883 : mixedVector B (Sum.inr 2883) = Sparse.eval nodeValue2883 (mixedVector B) := by
    change mixedMoment B node2883 node2883Labels = _
    exact sound2883 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm528, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2877, h2879, h2883, h3050, h3580, h4084, reducedSource442] using sourceEq528 B hB

theorem rowSound442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row442 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck442, numericCheck442, reducedZero442 B hB hF, mul_zero]

theorem reducedZero443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource443 (mixedVector B) = 0 := by
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm529, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2106, h3050, h3502, h3580, h3582, h4084, reducedSource443] using sourceEq529 B hB

theorem rowSound443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row443 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck443, numericCheck443, reducedZero443 B hB hF, mul_zero]

theorem reducedZero444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource444 (mixedVector B) = 0 := by
  have h4581 : mixedVector B (Sum.inr 4581) = Sparse.eval nodeValue4581 (mixedVector B) := by
    change mixedMoment B node4581 node4581Labels = _
    exact sound4581 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4586 : mixedVector B (Sum.inr 4586) = Sparse.eval nodeValue4586 (mixedVector B) := by
    change mixedMoment B node4586 node4586Labels = _
    exact sound4586 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4729 : mixedVector B (Sum.inr 4729) = Sparse.eval nodeValue4729 (mixedVector B) := by
    change mixedMoment B node4729 node4729Labels = _
    exact sound4729 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h5142 : mixedVector B (Sum.inr 5142) = Sparse.eval nodeValue5142 (mixedVector B) := by
    change mixedMoment B node5142 node5142Labels = _
    exact sound5142 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5192 : mixedVector B (Sum.inr 5192) = Sparse.eval nodeValue5192 (mixedVector B) := by
    change mixedMoment B node5192 node5192Labels = _
    exact sound5192 B hB hF
  have h5193 : mixedVector B (Sum.inr 5193) = Sparse.eval nodeValue5193 (mixedVector B) := by
    change mixedMoment B node5193 node5193Labels = _
    exact sound5193 B hB hF
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
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  simpa only [sourceForm530, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4581, h4583, h4586, h4602, h4729, h4742, h4890, h5142, h5149, h5192, h5193, h5204, h5283, h5284, h5292, h5294, h5406, h5411, h5452, h5453, reducedSource444] using sourceEq530 B hB

theorem rowSound444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row444 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck444, numericCheck444, reducedZero444 B hB hF, mul_zero]

theorem reducedZero445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource445 (mixedVector B) = 0 := by
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1898 : mixedVector B (Sum.inr 1898) = Sparse.eval nodeValue1898 (mixedVector B) := by
    change mixedMoment B node1898 node1898Labels = _
    exact sound1898 B hB hF
  have h1915 : mixedVector B (Sum.inr 1915) = Sparse.eval nodeValue1915 (mixedVector B) := by
    change mixedMoment B node1915 node1915Labels = _
    exact sound1915 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2853 : mixedVector B (Sum.inr 2853) = Sparse.eval nodeValue2853 (mixedVector B) := by
    change mixedMoment B node2853 node2853Labels = _
    exact sound2853 B hB hF
  have h2856 : mixedVector B (Sum.inr 2856) = Sparse.eval nodeValue2856 (mixedVector B) := by
    change mixedMoment B node2856 node2856Labels = _
    exact sound2856 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2913 : mixedVector B (Sum.inr 2913) = Sparse.eval nodeValue2913 (mixedVector B) := by
    change mixedMoment B node2913 node2913Labels = _
    exact sound2913 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
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
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3912 : mixedVector B (Sum.inr 3912) = Sparse.eval nodeValue3912 (mixedVector B) := by
    change mixedMoment B node3912 node3912Labels = _
    exact sound3912 B hB hF
  have h4039 : mixedVector B (Sum.inr 4039) = Sparse.eval nodeValue4039 (mixedVector B) := by
    change mixedMoment B node4039 node4039Labels = _
    exact sound4039 B hB hF
  simpa only [sourceForm531, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1200, h1202, h1205, h1236, h1898, h1915, h2247, h2853, h2856, h2881, h2913, h2924, h3076, h3077, h3100, h3101, h3801, h3809, h3912, h4039, reducedSource445] using sourceEq531 B hB

theorem rowSound445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row445 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck445, numericCheck445, reducedZero445 B hB hF, mul_zero]

theorem reducedZero446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource446 (mixedVector B) = 0 := by
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h5065 : mixedVector B (Sum.inr 5065) = Sparse.eval nodeValue5065 (mixedVector B) := by
    change mixedMoment B node5065 node5065Labels = _
    exact sound5065 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  simpa only [sourceForm532, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4439, h4440, h4444, h4459, h5065, h5067, h5074, h5078, h5149, h5152, h5170, h5251, h5252, h5260, h5281, h5282, h5289, h5405, h5410, h5439, h5485, reducedSource446] using sourceEq532 B hB

theorem rowSound446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row446 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck446, numericCheck446, reducedZero446 B hB hF, mul_zero]

theorem reducedZero447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource447 (mixedVector B) = 0 := by
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1026 : mixedVector B (Sum.inr 1026) = Sparse.eval nodeValue1026 (mixedVector B) := by
    change mixedMoment B node1026 node1026Labels = _
    exact sound1026 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2570 : mixedVector B (Sum.inr 2570) = Sparse.eval nodeValue2570 (mixedVector B) := by
    change mixedMoment B node2570 node2570Labels = _
    exact sound2570 B hB hF
  have h2572 : mixedVector B (Sum.inr 2572) = Sparse.eval nodeValue2572 (mixedVector B) := by
    change mixedMoment B node2572 node2572Labels = _
    exact sound2572 B hB hF
  have h2576 : mixedVector B (Sum.inr 2576) = Sparse.eval nodeValue2576 (mixedVector B) := by
    change mixedMoment B node2576 node2576Labels = _
    exact sound2576 B hB hF
  have h2596 : mixedVector B (Sum.inr 2596) = Sparse.eval nodeValue2596 (mixedVector B) := by
    change mixedMoment B node2596 node2596Labels = _
    exact sound2596 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977 B hB hF
  have h3996 : mixedVector B (Sum.inr 3996) = Sparse.eval nodeValue3996 (mixedVector B) := by
    change mixedMoment B node3996 node3996Labels = _
    exact sound3996 B hB hF
  have h3998 : mixedVector B (Sum.inr 3998) = Sparse.eval nodeValue3998 (mixedVector B) := by
    change mixedMoment B node3998 node3998Labels = _
    exact sound3998 B hB hF
  have h4012 : mixedVector B (Sum.inr 4012) = Sparse.eval nodeValue4012 (mixedVector B) := by
    change mixedMoment B node4012 node4012Labels = _
    exact sound4012 B hB hF
  simpa only [sourceForm533, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1021, h1022, h1026, h1042, h2470, h2473, h2481, h2570, h2572, h2576, h2596, h2710, h2712, h2724, h2750, h2751, h2763, h3977, h3996, h3998, h4012, reducedSource447] using sourceEq533 B hB

theorem rowSound447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row447 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck447, numericCheck447, reducedZero447 B hB hF, mul_zero]

theorem sourceRowsAt432 : MixedData.sourceRows (432 : Fin 2425) =
    MixedData.row432 := by decide +kernel

theorem sourceRowsAt433 : MixedData.sourceRows (433 : Fin 2425) =
    MixedData.row433 := by decide +kernel

theorem sourceRowsAt434 : MixedData.sourceRows (434 : Fin 2425) =
    MixedData.row434 := by decide +kernel

theorem sourceRowsAt435 : MixedData.sourceRows (435 : Fin 2425) =
    MixedData.row435 := by decide +kernel

theorem sourceRowsAt436 : MixedData.sourceRows (436 : Fin 2425) =
    MixedData.row436 := by decide +kernel

theorem sourceRowsAt437 : MixedData.sourceRows (437 : Fin 2425) =
    MixedData.row437 := by decide +kernel

theorem sourceRowsAt438 : MixedData.sourceRows (438 : Fin 2425) =
    MixedData.row438 := by decide +kernel

theorem sourceRowsAt439 : MixedData.sourceRows (439 : Fin 2425) =
    MixedData.row439 := by decide +kernel

theorem sourceRowsAt440 : MixedData.sourceRows (440 : Fin 2425) =
    MixedData.row440 := by decide +kernel

theorem sourceRowsAt441 : MixedData.sourceRows (441 : Fin 2425) =
    MixedData.row441 := by decide +kernel

theorem sourceRowsAt442 : MixedData.sourceRows (442 : Fin 2425) =
    MixedData.row442 := by decide +kernel

theorem sourceRowsAt443 : MixedData.sourceRows (443 : Fin 2425) =
    MixedData.row443 := by decide +kernel

theorem sourceRowsAt444 : MixedData.sourceRows (444 : Fin 2425) =
    MixedData.row444 := by decide +kernel

theorem sourceRowsAt445 : MixedData.sourceRows (445 : Fin 2425) =
    MixedData.row445 := by decide +kernel

theorem sourceRowsAt446 : MixedData.sourceRows (446 : Fin 2425) =
    MixedData.row446 := by decide +kernel

theorem sourceRowsAt447 : MixedData.sourceRows (447 : Fin 2425) =
    MixedData.row447 := by decide +kernel

theorem chunkSound27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 27) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 432 ∨ k.val = 433 ∨ k.val = 434 ∨ k.val = 435 ∨ k.val = 436 ∨ k.val = 437 ∨ k.val = 438 ∨ k.val = 439 ∨ k.val = 440 ∨ k.val = 441 ∨ k.val = 442 ∨ k.val = 443 ∨ k.val = 444 ∨ k.val = 445 ∨ k.val = 446 ∨ k.val = 447 := by omega
  rcases heq with h432 | h433 | h434 | h435 | h436 | h437 | h438 | h439 | h440 | h441 | h442 | h443 | h444 | h445 | h446 | h447
  · have he : k = (432 : Fin 2425) := Fin.ext h432
    subst k
    rw [sourceRowsAt432]
    exact rowSound432 B hB hF
  · have he : k = (433 : Fin 2425) := Fin.ext h433
    subst k
    rw [sourceRowsAt433]
    exact rowSound433 B hB hF
  · have he : k = (434 : Fin 2425) := Fin.ext h434
    subst k
    rw [sourceRowsAt434]
    exact rowSound434 B hB hF
  · have he : k = (435 : Fin 2425) := Fin.ext h435
    subst k
    rw [sourceRowsAt435]
    exact rowSound435 B hB hF
  · have he : k = (436 : Fin 2425) := Fin.ext h436
    subst k
    rw [sourceRowsAt436]
    exact rowSound436 B hB hF
  · have he : k = (437 : Fin 2425) := Fin.ext h437
    subst k
    rw [sourceRowsAt437]
    exact rowSound437 B hB hF
  · have he : k = (438 : Fin 2425) := Fin.ext h438
    subst k
    rw [sourceRowsAt438]
    exact rowSound438 B hB hF
  · have he : k = (439 : Fin 2425) := Fin.ext h439
    subst k
    rw [sourceRowsAt439]
    exact rowSound439 B hB hF
  · have he : k = (440 : Fin 2425) := Fin.ext h440
    subst k
    rw [sourceRowsAt440]
    exact rowSound440 B hB hF
  · have he : k = (441 : Fin 2425) := Fin.ext h441
    subst k
    rw [sourceRowsAt441]
    exact rowSound441 B hB hF
  · have he : k = (442 : Fin 2425) := Fin.ext h442
    subst k
    rw [sourceRowsAt442]
    exact rowSound442 B hB hF
  · have he : k = (443 : Fin 2425) := Fin.ext h443
    subst k
    rw [sourceRowsAt443]
    exact rowSound443 B hB hF
  · have he : k = (444 : Fin 2425) := Fin.ext h444
    subst k
    rw [sourceRowsAt444]
    exact rowSound444 B hB hF
  · have he : k = (445 : Fin 2425) := Fin.ext h445
    subst k
    rw [sourceRowsAt445]
    exact rowSound445 B hB hF
  · have he : k = (446 : Fin 2425) := Fin.ext h446
    subst k
    rw [sourceRowsAt446]
    exact rowSound446 B hB hF
  · have he : k = (447 : Fin 2425) := Fin.ext h447
    subst k
    rw [sourceRowsAt447]
    exact rowSound447 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
