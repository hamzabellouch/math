import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources67

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1776 (mixedVector B) = 0 := by
  have h1152 : mixedVector B (Sum.inr 1152) = Sparse.eval nodeValue1152 (mixedVector B) := by
    change mixedMoment B node1152 node1152Labels = _
    exact sound1152 B hB hF
  have h2351 : mixedVector B (Sum.inr 2351) = Sparse.eval nodeValue2351 (mixedVector B) := by
    change mixedMoment B node2351 node2351Labels = _
    exact sound2351 B hB hF
  have h2432 : mixedVector B (Sum.inr 2432) = Sparse.eval nodeValue2432 (mixedVector B) := by
    change mixedMoment B node2432 node2432Labels = _
    exact sound2432 B hB hF
  have h2546 : mixedVector B (Sum.inr 2546) = Sparse.eval nodeValue2546 (mixedVector B) := by
    change mixedMoment B node2546 node2546Labels = _
    exact sound2546 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2130, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1152, h2351, h2432, h2546, h2556, h4091, reducedSource1776] using sourceEq2130 B hB

theorem rowSound1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1776 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1776, numericCheck1776, reducedZero1776 B hB hF, mul_zero]

theorem reducedZero1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1777 (mixedVector B) = 0 := by
  have h1997 : mixedVector B (Sum.inr 1997) = Sparse.eval nodeValue1997 (mixedVector B) := by
    change mixedMoment B node1997 node1997Labels = _
    exact sound1997 B hB hF
  have h2002 : mixedVector B (Sum.inr 2002) = Sparse.eval nodeValue2002 (mixedVector B) := by
    change mixedMoment B node2002 node2002Labels = _
    exact sound2002 B hB hF
  have h2044 : mixedVector B (Sum.inr 2044) = Sparse.eval nodeValue2044 (mixedVector B) := by
    change mixedMoment B node2044 node2044Labels = _
    exact sound2044 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2132, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1997, h2002, h2044, h2225, h3520, h4082, reducedSource1777] using sourceEq2132 B hB

theorem rowSound1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1777 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1777, numericCheck1777, reducedZero1777 B hB hF, mul_zero]

theorem reducedZero1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1778 (mixedVector B) = 0 := by
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3616 : mixedVector B (Sum.inr 3616) = Sparse.eval nodeValue3616 (mixedVector B) := by
    change mixedMoment B node3616 node3616Labels = _
    exact sound3616 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2133, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3482, h3520, h3522, h3542, h3616, h4082, reducedSource1778] using sourceEq2133 B hB

theorem rowSound1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1778 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1778, numericCheck1778, reducedZero1778 B hB hF, mul_zero]

theorem reducedZero1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1779 (mixedVector B) = 0 := by
  have h2905 : mixedVector B (Sum.inr 2905) = Sparse.eval nodeValue2905 (mixedVector B) := by
    change mixedMoment B node2905 node2905Labels = _
    exact sound2905 B hB hF
  have h3680 : mixedVector B (Sum.inr 3680) = Sparse.eval nodeValue3680 (mixedVector B) := by
    change mixedMoment B node3680 node3680Labels = _
    exact sound3680 B hB hF
  have h3683 : mixedVector B (Sum.inr 3683) = Sparse.eval nodeValue3683 (mixedVector B) := by
    change mixedMoment B node3683 node3683Labels = _
    exact sound3683 B hB hF
  have h3696 : mixedVector B (Sum.inr 3696) = Sparse.eval nodeValue3696 (mixedVector B) := by
    change mixedMoment B node3696 node3696Labels = _
    exact sound3696 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm2134, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2905, h3680, h3683, h3696, h3796, h3873, h4090, reducedSource1779] using sourceEq2134 B hB

theorem rowSound1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1779 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1779, numericCheck1779, reducedZero1779 B hB hF, mul_zero]

theorem reducedZero1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1780 (mixedVector B) = 0 := by
  have h4553 : mixedVector B (Sum.inr 4553) = Sparse.eval nodeValue4553 (mixedVector B) := by
    change mixedMoment B node4553 node4553Labels = _
    exact sound4553 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  have h4686 : mixedVector B (Sum.inr 4686) = Sparse.eval nodeValue4686 (mixedVector B) := by
    change mixedMoment B node4686 node4686Labels = _
    exact sound4686 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h4979 : mixedVector B (Sum.inr 4979) = Sparse.eval nodeValue4979 (mixedVector B) := by
    change mixedMoment B node4979 node4979Labels = _
    exact sound4979 B hB hF
  have h5114 : mixedVector B (Sum.inr 5114) = Sparse.eval nodeValue5114 (mixedVector B) := by
    change mixedMoment B node5114 node5114Labels = _
    exact sound5114 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5389 : mixedVector B (Sum.inr 5389) = Sparse.eval nodeValue5389 (mixedVector B) := by
    change mixedMoment B node5389 node5389Labels = _
    exact sound5389 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  simpa only [sourceForm2135, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4553, h4557, h4559, h4627, h4686, h4693, h4871, h4970, h4973, h4979, h5114, h5168, h5170, h5171, h5176, h5308, h5310, h5387, h5389, h5441, h5443, reducedSource1780] using sourceEq2135 B hB

theorem rowSound1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1780 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1780, numericCheck1780, reducedZero1780 B hB hF, mul_zero]

theorem reducedZero1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1781 (mixedVector B) = 0 := by
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1311 : mixedVector B (Sum.inr 1311) = Sparse.eval nodeValue1311 (mixedVector B) := by
    change mixedMoment B node1311 node1311Labels = _
    exact sound1311 B hB hF
  have h1812 : mixedVector B (Sum.inr 1812) = Sparse.eval nodeValue1812 (mixedVector B) := by
    change mixedMoment B node1812 node1812Labels = _
    exact sound1812 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2815 : mixedVector B (Sum.inr 2815) = Sparse.eval nodeValue2815 (mixedVector B) := by
    change mixedMoment B node2815 node2815Labels = _
    exact sound2815 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2820 : mixedVector B (Sum.inr 2820) = Sparse.eval nodeValue2820 (mixedVector B) := by
    change mixedMoment B node2820 node2820Labels = _
    exact sound2820 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2963 : mixedVector B (Sum.inr 2963) = Sparse.eval nodeValue2963 (mixedVector B) := by
    change mixedMoment B node2963 node2963Labels = _
    exact sound2963 B hB hF
  have h2965 : mixedVector B (Sum.inr 2965) = Sparse.eval nodeValue2965 (mixedVector B) := by
    change mixedMoment B node2965 node2965Labels = _
    exact sound2965 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  have h3739 : mixedVector B (Sum.inr 3739) = Sparse.eval nodeValue3739 (mixedVector B) := by
    change mixedMoment B node3739 node3739Labels = _
    exact sound3739 B hB hF
  have h3740 : mixedVector B (Sum.inr 3740) = Sparse.eval nodeValue3740 (mixedVector B) := by
    change mixedMoment B node3740 node3740Labels = _
    exact sound3740 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  have h4037 : mixedVector B (Sum.inr 4037) = Sparse.eval nodeValue4037 (mixedVector B) := by
    change mixedMoment B node4037 node4037Labels = _
    exact sound4037 B hB hF
  simpa only [sourceForm2136, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1138, h1143, h1145, h1311, h1812, h1819, h2112, h2815, h2817, h2820, h2896, h2954, h2963, h2965, h2968, h3121, h3124, h3739, h3740, h3889, h4037, reducedSource1781] using sourceEq2136 B hB

theorem rowSound1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1781 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1781, numericCheck1781, reducedZero1781 B hB hF, mul_zero]

theorem reducedZero1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1782 (mixedVector B) = 0 := by
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h5038 : mixedVector B (Sum.inr 5038) = Sparse.eval nodeValue5038 (mixedVector B) := by
    change mixedMoment B node5038 node5038Labels = _
    exact sound5038 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388 B hB hF
  have h5390 : mixedVector B (Sum.inr 5390) = Sparse.eval nodeValue5390 (mixedVector B) := by
    change mixedMoment B node5390 node5390Labels = _
    exact sound5390 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  simpa only [sourceForm2137, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4354, h4359, h4361, h4466, h4681, h4692, h4868, h4949, h4953, h4972, h5038, h5080, h5163, h5172, h5174, h5291, h5294, h5388, h5390, h5442, h5451, reducedSource1782] using sourceEq2137 B hB

theorem rowSound1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1782 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1782, numericCheck1782, reducedZero1782 B hB hF, mul_zero]

theorem reducedZero1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1783 (mixedVector B) = 0 := by
  have h932 : mixedVector B (Sum.inr 932) = Sparse.eval nodeValue932 (mixedVector B) := by
    change mixedMoment B node932 node932Labels = _
    exact sound932 B hB hF
  have h937 : mixedVector B (Sum.inr 937) = Sparse.eval nodeValue937 (mixedVector B) := by
    change mixedMoment B node937 node937Labels = _
    exact sound937 B hB hF
  have h939 : mixedVector B (Sum.inr 939) = Sparse.eval nodeValue939 (mixedVector B) := by
    change mixedMoment B node939 node939Labels = _
    exact sound939 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1807 : mixedVector B (Sum.inr 1807) = Sparse.eval nodeValue1807 (mixedVector B) := by
    change mixedMoment B node1807 node1807Labels = _
    exact sound1807 B hB hF
  have h1818 : mixedVector B (Sum.inr 1818) = Sparse.eval nodeValue1818 (mixedVector B) := by
    change mixedMoment B node1818 node1818Labels = _
    exact sound1818 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2341 : mixedVector B (Sum.inr 2341) = Sparse.eval nodeValue2341 (mixedVector B) := by
    change mixedMoment B node2341 node2341Labels = _
    exact sound2341 B hB hF
  have h2345 : mixedVector B (Sum.inr 2345) = Sparse.eval nodeValue2345 (mixedVector B) := by
    change mixedMoment B node2345 node2345Labels = _
    exact sound2345 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2434 : mixedVector B (Sum.inr 2434) = Sparse.eval nodeValue2434 (mixedVector B) := by
    change mixedMoment B node2434 node2434Labels = _
    exact sound2434 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2599 : mixedVector B (Sum.inr 2599) = Sparse.eval nodeValue2599 (mixedVector B) := by
    change mixedMoment B node2599 node2599Labels = _
    exact sound2599 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h3737 : mixedVector B (Sum.inr 3737) = Sparse.eval nodeValue3737 (mixedVector B) := by
    change mixedMoment B node3737 node3737Labels = _
    exact sound3737 B hB hF
  have h3741 : mixedVector B (Sum.inr 3741) = Sparse.eval nodeValue3741 (mixedVector B) := by
    change mixedMoment B node3741 node3741Labels = _
    exact sound3741 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  simpa only [sourceForm2138, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h932, h937, h939, h1049, h1807, h1818, h2109, h2341, h2345, h2431, h2434, h2488, h2590, h2599, h2601, h2765, h2768, h3737, h3741, h3888, h4001, reducedSource1783] using sourceEq2138 B hB

theorem rowSound1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1783 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1783, numericCheck1783, reducedZero1783 B hB hF, mul_zero]

theorem reducedZero1784 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1784 (mixedVector B) = 0 := by
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5175 : mixedVector B (Sum.inr 5175) = Sparse.eval nodeValue5175 (mixedVector B) := by
    change mixedMoment B node5175 node5175Labels = _
    exact sound5175 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5206 : mixedVector B (Sum.inr 5206) = Sparse.eval nodeValue5206 (mixedVector B) := by
    change mixedMoment B node5206 node5206Labels = _
    exact sound5206 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  simpa only [sourceForm2139, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4810, h4845, h4846, h4874, h5080, h5110, h5111, h5129, h5140, h5141, h5151, h5152, h5175, h5176, h5177, h5188, h5206, h5207, reducedSource1784] using sourceEq2139 B hB

theorem rowSound1784 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1784 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1784, numericCheck1784, reducedZero1784 B hB hF, mul_zero]

theorem reducedZero1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1785 (mixedVector B) = 0 := by
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2523 : mixedVector B (Sum.inr 2523) = Sparse.eval nodeValue2523 (mixedVector B) := by
    change mixedMoment B node2523 node2523Labels = _
    exact sound2523 B hB hF
  have h2604 : mixedVector B (Sum.inr 2604) = Sparse.eval nodeValue2604 (mixedVector B) := by
    change mixedMoment B node2604 node2604Labels = _
    exact sound2604 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2943 : mixedVector B (Sum.inr 2943) = Sparse.eval nodeValue2943 (mixedVector B) := by
    change mixedMoment B node2943 node2943Labels = _
    exact sound2943 B hB hF
  have h2967 : mixedVector B (Sum.inr 2967) = Sparse.eval nodeValue2967 (mixedVector B) := by
    change mixedMoment B node2967 node2967Labels = _
    exact sound2967 B hB hF
  have h2969 : mixedVector B (Sum.inr 2969) = Sparse.eval nodeValue2969 (mixedVector B) := by
    change mixedMoment B node2969 node2969Labels = _
    exact sound2969 B hB hF
  have h2990 : mixedVector B (Sum.inr 2990) = Sparse.eval nodeValue2990 (mixedVector B) := by
    change mixedMoment B node2990 node2990Labels = _
    exact sound2990 B hB hF
  have h3005 : mixedVector B (Sum.inr 3005) = Sparse.eval nodeValue3005 (mixedVector B) := by
    change mixedMoment B node3005 node3005Labels = _
    exact sound3005 B hB hF
  have h3006 : mixedVector B (Sum.inr 3006) = Sparse.eval nodeValue3006 (mixedVector B) := by
    change mixedMoment B node3006 node3006Labels = _
    exact sound3006 B hB hF
  have h3095 : mixedVector B (Sum.inr 3095) = Sparse.eval nodeValue3095 (mixedVector B) := by
    change mixedMoment B node3095 node3095Labels = _
    exact sound3095 B hB hF
  have h3187 : mixedVector B (Sum.inr 3187) = Sparse.eval nodeValue3187 (mixedVector B) := by
    change mixedMoment B node3187 node3187Labels = _
    exact sound3187 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3216 : mixedVector B (Sum.inr 3216) = Sparse.eval nodeValue3216 (mixedVector B) := by
    change mixedMoment B node3216 node3216Labels = _
    exact sound3216 B hB hF
  simpa only [sourceForm2140, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2488, h2522, h2523, h2604, h2867, h2888, h2889, h2916, h2930, h2931, h2942, h2943, h2967, h2969, h2990, h3005, h3006, h3095, h3187, h3206, h3216, reducedSource1785] using sourceEq2140 B hB

theorem rowSound1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1785 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1785, numericCheck1785, reducedZero1785 B hB hF, mul_zero]

theorem reducedZero1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1786 (mixedVector B) = 0 := by
  have h4554 : mixedVector B (Sum.inr 4554) = Sparse.eval nodeValue4554 (mixedVector B) := by
    change mixedMoment B node4554 node4554Labels = _
    exact sound4554 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4974 : mixedVector B (Sum.inr 4974) = Sparse.eval nodeValue4974 (mixedVector B) := by
    change mixedMoment B node4974 node4974Labels = _
    exact sound4974 B hB hF
  have h5115 : mixedVector B (Sum.inr 5115) = Sparse.eval nodeValue5115 (mixedVector B) := by
    change mixedMoment B node5115 node5115Labels = _
    exact sound5115 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  have h5390 : mixedVector B (Sum.inr 5390) = Sparse.eval nodeValue5390 (mixedVector B) := by
    change mixedMoment B node5390 node5390Labels = _
    exact sound5390 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  simpa only [sourceForm2141, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4554, h4558, h4628, h4948, h4953, h4974, h5115, h5169, h5174, h5177, h5309, h5390, h5418, h5442, reducedSource1786] using sourceEq2141 B hB

theorem rowSound1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1786 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1786, numericCheck1786, reducedZero1786 B hB hF, mul_zero]

theorem reducedZero1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1787 (mixedVector B) = 0 := by
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1144 : mixedVector B (Sum.inr 1144) = Sparse.eval nodeValue1144 (mixedVector B) := by
    change mixedMoment B node1144 node1144Labels = _
    exact sound1144 B hB hF
  have h1312 : mixedVector B (Sum.inr 1312) = Sparse.eval nodeValue1312 (mixedVector B) := by
    change mixedMoment B node1312 node1312Labels = _
    exact sound1312 B hB hF
  have h2339 : mixedVector B (Sum.inr 2339) = Sparse.eval nodeValue2339 (mixedVector B) := by
    change mixedMoment B node2339 node2339Labels = _
    exact sound2339 B hB hF
  have h2345 : mixedVector B (Sum.inr 2345) = Sparse.eval nodeValue2345 (mixedVector B) := by
    change mixedMoment B node2345 node2345Labels = _
    exact sound2345 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2818 : mixedVector B (Sum.inr 2818) = Sparse.eval nodeValue2818 (mixedVector B) := by
    change mixedMoment B node2818 node2818Labels = _
    exact sound2818 B hB hF
  have h2897 : mixedVector B (Sum.inr 2897) = Sparse.eval nodeValue2897 (mixedVector B) := by
    change mixedMoment B node2897 node2897Labels = _
    exact sound2897 B hB hF
  have h2960 : mixedVector B (Sum.inr 2960) = Sparse.eval nodeValue2960 (mixedVector B) := by
    change mixedMoment B node2960 node2960Labels = _
    exact sound2960 B hB hF
  have h2969 : mixedVector B (Sum.inr 2969) = Sparse.eval nodeValue2969 (mixedVector B) := by
    change mixedMoment B node2969 node2969Labels = _
    exact sound2969 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  have h3741 : mixedVector B (Sum.inr 3741) = Sparse.eval nodeValue3741 (mixedVector B) := by
    change mixedMoment B node3741 node3741Labels = _
    exact sound3741 B hB hF
  have h3933 : mixedVector B (Sum.inr 3933) = Sparse.eval nodeValue3933 (mixedVector B) := by
    change mixedMoment B node3933 node3933Labels = _
    exact sound3933 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  simpa only [sourceForm2142, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1139, h1144, h1312, h2339, h2345, h2601, h2818, h2897, h2960, h2969, h3123, h3741, h3933, h4001, reducedSource1787] using sourceEq2142 B hB

theorem rowSound1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1787 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1787, numericCheck1787, reducedZero1787 B hB hF, mul_zero]

theorem reducedZero1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1788 (mixedVector B) = 0 := by
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4950 : mixedVector B (Sum.inr 4950) = Sparse.eval nodeValue4950 (mixedVector B) := by
    change mixedMoment B node4950 node4950Labels = _
    exact sound4950 B hB hF
  have h4952 : mixedVector B (Sum.inr 4952) = Sparse.eval nodeValue4952 (mixedVector B) := by
    change mixedMoment B node4952 node4952Labels = _
    exact sound4952 B hB hF
  have h5039 : mixedVector B (Sum.inr 5039) = Sparse.eval nodeValue5039 (mixedVector B) := by
    change mixedMoment B node5039 node5039Labels = _
    exact sound5039 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465 B hB hF
  have h5466 : mixedVector B (Sum.inr 5466) = Sparse.eval nodeValue5466 (mixedVector B) := by
    change mixedMoment B node5466 node5466Labels = _
    exact sound5466 B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  simpa only [sourceForm2143, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4355, h4360, h4467, h4943, h4950, h4952, h5039, h5081, h5169, h5171, h5293, h5465, h5466, h5487, reducedSource1788] using sourceEq2143 B hB

theorem rowSound1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1788 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1788, numericCheck1788, reducedZero1788 B hB hF, mul_zero]

theorem reducedZero1789 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1789 (mixedVector B) = 0 := by
  have h933 : mixedVector B (Sum.inr 933) = Sparse.eval nodeValue933 (mixedVector B) := by
    change mixedMoment B node933 node933Labels = _
    exact sound933 B hB hF
  have h938 : mixedVector B (Sum.inr 938) = Sparse.eval nodeValue938 (mixedVector B) := by
    change mixedMoment B node938 node938Labels = _
    exact sound938 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h2334 : mixedVector B (Sum.inr 2334) = Sparse.eval nodeValue2334 (mixedVector B) := by
    change mixedMoment B node2334 node2334Labels = _
    exact sound2334 B hB hF
  have h2342 : mixedVector B (Sum.inr 2342) = Sparse.eval nodeValue2342 (mixedVector B) := by
    change mixedMoment B node2342 node2342Labels = _
    exact sound2342 B hB hF
  have h2344 : mixedVector B (Sum.inr 2344) = Sparse.eval nodeValue2344 (mixedVector B) := by
    change mixedMoment B node2344 node2344Labels = _
    exact sound2344 B hB hF
  have h2432 : mixedVector B (Sum.inr 2432) = Sparse.eval nodeValue2432 (mixedVector B) := by
    change mixedMoment B node2432 node2432Labels = _
    exact sound2432 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h2595 : mixedVector B (Sum.inr 2595) = Sparse.eval nodeValue2595 (mixedVector B) := by
    change mixedMoment B node2595 node2595Labels = _
    exact sound2595 B hB hF
  have h2598 : mixedVector B (Sum.inr 2598) = Sparse.eval nodeValue2598 (mixedVector B) := by
    change mixedMoment B node2598 node2598Labels = _
    exact sound2598 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h3931 : mixedVector B (Sum.inr 3931) = Sparse.eval nodeValue3931 (mixedVector B) := by
    change mixedMoment B node3931 node3931Labels = _
    exact sound3931 B hB hF
  have h3934 : mixedVector B (Sum.inr 3934) = Sparse.eval nodeValue3934 (mixedVector B) := by
    change mixedMoment B node3934 node3934Labels = _
    exact sound3934 B hB hF
  have h4000 : mixedVector B (Sum.inr 4000) = Sparse.eval nodeValue4000 (mixedVector B) := by
    change mixedMoment B node4000 node4000Labels = _
    exact sound4000 B hB hF
  simpa only [sourceForm2144, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h933, h938, h1050, h2334, h2342, h2344, h2432, h2489, h2595, h2598, h2767, h3931, h3934, h4000, reducedSource1789] using sourceEq2144 B hB

theorem rowSound1789 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1789 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1789, numericCheck1789, reducedZero1789 B hB hF, mul_zero]

theorem reducedZero1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1790 (mixedVector B) = 0 := by
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5130 : mixedVector B (Sum.inr 5130) = Sparse.eval nodeValue5130 (mixedVector B) := by
    change mixedMoment B node5130 node5130Labels = _
    exact sound5130 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5189 : mixedVector B (Sum.inr 5189) = Sparse.eval nodeValue5189 (mixedVector B) := by
    change mixedMoment B node5189 node5189Labels = _
    exact sound5189 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  simpa only [sourceForm2145, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4811, h4846, h4875, h5081, h5111, h5130, h5141, h5152, h5176, h5177, h5189, h5207, reducedSource1790] using sourceEq2145 B hB

theorem rowSound1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1790 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1790, numericCheck1790, reducedZero1790 B hB hF, mul_zero]

theorem reducedZero1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1791 (mixedVector B) = 0 := by
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3616 : mixedVector B (Sum.inr 3616) = Sparse.eval nodeValue3616 (mixedVector B) := by
    change mixedMoment B node3616 node3616Labels = _
    exact sound3616 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2146, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3482, h3485, h3616, h4082, reducedSource1791] using sourceEq2146 B hB

theorem rowSound1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1791 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1791, numericCheck1791, reducedZero1791 B hB hF, mul_zero]

theorem sourceRowsAt1776 : MixedData.sourceRows (1776 : Fin 2425) =
    MixedData.row1776 := by decide +kernel

theorem sourceRowsAt1777 : MixedData.sourceRows (1777 : Fin 2425) =
    MixedData.row1777 := by decide +kernel

theorem sourceRowsAt1778 : MixedData.sourceRows (1778 : Fin 2425) =
    MixedData.row1778 := by decide +kernel

theorem sourceRowsAt1779 : MixedData.sourceRows (1779 : Fin 2425) =
    MixedData.row1779 := by decide +kernel

theorem sourceRowsAt1780 : MixedData.sourceRows (1780 : Fin 2425) =
    MixedData.row1780 := by decide +kernel

theorem sourceRowsAt1781 : MixedData.sourceRows (1781 : Fin 2425) =
    MixedData.row1781 := by decide +kernel

theorem sourceRowsAt1782 : MixedData.sourceRows (1782 : Fin 2425) =
    MixedData.row1782 := by decide +kernel

theorem sourceRowsAt1783 : MixedData.sourceRows (1783 : Fin 2425) =
    MixedData.row1783 := by decide +kernel

theorem sourceRowsAt1784 : MixedData.sourceRows (1784 : Fin 2425) =
    MixedData.row1784 := by decide +kernel

theorem sourceRowsAt1785 : MixedData.sourceRows (1785 : Fin 2425) =
    MixedData.row1785 := by decide +kernel

theorem sourceRowsAt1786 : MixedData.sourceRows (1786 : Fin 2425) =
    MixedData.row1786 := by decide +kernel

theorem sourceRowsAt1787 : MixedData.sourceRows (1787 : Fin 2425) =
    MixedData.row1787 := by decide +kernel

theorem sourceRowsAt1788 : MixedData.sourceRows (1788 : Fin 2425) =
    MixedData.row1788 := by decide +kernel

theorem sourceRowsAt1789 : MixedData.sourceRows (1789 : Fin 2425) =
    MixedData.row1789 := by decide +kernel

theorem sourceRowsAt1790 : MixedData.sourceRows (1790 : Fin 2425) =
    MixedData.row1790 := by decide +kernel

theorem sourceRowsAt1791 : MixedData.sourceRows (1791 : Fin 2425) =
    MixedData.row1791 := by decide +kernel

theorem chunkSound111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 111) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1776 ∨ k.val = 1777 ∨ k.val = 1778 ∨ k.val = 1779 ∨ k.val = 1780 ∨ k.val = 1781 ∨ k.val = 1782 ∨ k.val = 1783 ∨ k.val = 1784 ∨ k.val = 1785 ∨ k.val = 1786 ∨ k.val = 1787 ∨ k.val = 1788 ∨ k.val = 1789 ∨ k.val = 1790 ∨ k.val = 1791 := by omega
  rcases heq with h1776 | h1777 | h1778 | h1779 | h1780 | h1781 | h1782 | h1783 | h1784 | h1785 | h1786 | h1787 | h1788 | h1789 | h1790 | h1791
  · have he : k = (1776 : Fin 2425) := Fin.ext h1776
    subst k
    rw [sourceRowsAt1776]
    exact rowSound1776 B hB hF
  · have he : k = (1777 : Fin 2425) := Fin.ext h1777
    subst k
    rw [sourceRowsAt1777]
    exact rowSound1777 B hB hF
  · have he : k = (1778 : Fin 2425) := Fin.ext h1778
    subst k
    rw [sourceRowsAt1778]
    exact rowSound1778 B hB hF
  · have he : k = (1779 : Fin 2425) := Fin.ext h1779
    subst k
    rw [sourceRowsAt1779]
    exact rowSound1779 B hB hF
  · have he : k = (1780 : Fin 2425) := Fin.ext h1780
    subst k
    rw [sourceRowsAt1780]
    exact rowSound1780 B hB hF
  · have he : k = (1781 : Fin 2425) := Fin.ext h1781
    subst k
    rw [sourceRowsAt1781]
    exact rowSound1781 B hB hF
  · have he : k = (1782 : Fin 2425) := Fin.ext h1782
    subst k
    rw [sourceRowsAt1782]
    exact rowSound1782 B hB hF
  · have he : k = (1783 : Fin 2425) := Fin.ext h1783
    subst k
    rw [sourceRowsAt1783]
    exact rowSound1783 B hB hF
  · have he : k = (1784 : Fin 2425) := Fin.ext h1784
    subst k
    rw [sourceRowsAt1784]
    exact rowSound1784 B hB hF
  · have he : k = (1785 : Fin 2425) := Fin.ext h1785
    subst k
    rw [sourceRowsAt1785]
    exact rowSound1785 B hB hF
  · have he : k = (1786 : Fin 2425) := Fin.ext h1786
    subst k
    rw [sourceRowsAt1786]
    exact rowSound1786 B hB hF
  · have he : k = (1787 : Fin 2425) := Fin.ext h1787
    subst k
    rw [sourceRowsAt1787]
    exact rowSound1787 B hB hF
  · have he : k = (1788 : Fin 2425) := Fin.ext h1788
    subst k
    rw [sourceRowsAt1788]
    exact rowSound1788 B hB hF
  · have he : k = (1789 : Fin 2425) := Fin.ext h1789
    subst k
    rw [sourceRowsAt1789]
    exact rowSound1789 B hB hF
  · have he : k = (1790 : Fin 2425) := Fin.ext h1790
    subst k
    rw [sourceRowsAt1790]
    exact rowSound1790 B hB hF
  · have he : k = (1791 : Fin 2425) := Fin.ext h1791
    subst k
    rw [sourceRowsAt1791]
    exact rowSound1791 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
