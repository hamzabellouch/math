import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources65

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1744 (mixedVector B) = 0 := by
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  have h4076 : mixedVector B (Sum.inr 4076) = Sparse.eval nodeValue4076 (mixedVector B) := by
    change mixedMoment B node4076 node4076Labels = _
    exact sound4076 B hB hF
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2089, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4064, h4066, h4067, h4070, h4074, h4076, h4077, h4080, h4081, h4082, h4084, h4085, h4092, reducedSource1744] using sourceEq2089 B hB

theorem rowSound1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1744 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1744, numericCheck1744, reducedZero1744 B hB hF, mul_zero]

theorem reducedZero1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1745 (mixedVector B) = 0 := by
  have h2340 : mixedVector B (Sum.inr 2340) = Sparse.eval nodeValue2340 (mixedVector B) := by
    change mixedMoment B node2340 node2340Labels = _
    exact sound2340 B hB hF
  have h2816 : mixedVector B (Sum.inr 2816) = Sparse.eval nodeValue2816 (mixedVector B) := by
    change mixedMoment B node2816 node2816Labels = _
    exact sound2816 B hB hF
  have h3162 : mixedVector B (Sum.inr 3162) = Sparse.eval nodeValue3162 (mixedVector B) := by
    change mixedMoment B node3162 node3162Labels = _
    exact sound3162 B hB hF
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2091, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2340, h2816, h3162, h3174, h3198, h3706, h4092, reducedSource1745] using sourceEq2091 B hB

theorem rowSound1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1745 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1745, numericCheck1745, reducedZero1745 B hB hF, mul_zero]

theorem reducedZero1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1746 (mixedVector B) = 0 := by
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2092, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2213, h2215, h2217, h2225, h2274, h3612, h4082, reducedSource1746] using sourceEq2092 B hB

theorem rowSound1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1746 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1746, numericCheck1746, reducedZero1746 B hB hF, mul_zero]

theorem reducedZero1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1747 (mixedVector B) = 0 := by
  have h910 : mixedVector B (Sum.inr 910) = Sparse.eval nodeValue910 (mixedVector B) := by
    change mixedMoment B node910 node910Labels = _
    exact sound910 B hB hF
  have h1794 : mixedVector B (Sum.inr 1794) = Sparse.eval nodeValue1794 (mixedVector B) := by
    change mixedMoment B node1794 node1794Labels = _
    exact sound1794 B hB hF
  have h1977 : mixedVector B (Sum.inr 1977) = Sparse.eval nodeValue1977 (mixedVector B) := by
    change mixedMoment B node1977 node1977Labels = _
    exact sound1977 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2093, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h910, h1794, h1977, h2012, h2020, h2023, h4083, reducedSource1747] using sourceEq2093 B hB

theorem rowSound1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1747 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1747, numericCheck1747, reducedZero1747 B hB hF, mul_zero]

theorem reducedZero1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1748 (mixedVector B) = 0 := by
  have h2323 : mixedVector B (Sum.inr 2323) = Sparse.eval nodeValue2323 (mixedVector B) := by
    change mixedMoment B node2323 node2323Labels = _
    exact sound2323 B hB hF
  have h2800 : mixedVector B (Sum.inr 2800) = Sparse.eval nodeValue2800 (mixedVector B) := by
    change mixedMoment B node2800 node2800Labels = _
    exact sound2800 B hB hF
  have h3189 : mixedVector B (Sum.inr 3189) = Sparse.eval nodeValue3189 (mixedVector B) := by
    change mixedMoment B node3189 node3189Labels = _
    exact sound3189 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2094, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2323, h2800, h3189, h3199, h3692, h4091, reducedSource1748] using sourceEq2094 B hB

theorem rowSound1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1748 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1748, numericCheck1748, reducedZero1748 B hB hF, mul_zero]

theorem reducedZero1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1749 (mixedVector B) = 0 := by
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2396 : mixedVector B (Sum.inr 2396) = Sparse.eval nodeValue2396 (mixedVector B) := by
    change mixedMoment B node2396 node2396Labels = _
    exact sound2396 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3610 : mixedVector B (Sum.inr 3610) = Sparse.eval nodeValue3610 (mixedVector B) := by
    change mixedMoment B node3610 node3610Labels = _
    exact sound3610 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2095, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2213, h2396, h3476, h3610, h3612, h4082, reducedSource1749] using sourceEq2095 B hB

theorem rowSound1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1749 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1749, numericCheck1749, reducedZero1749 B hB hF, mul_zero]

theorem reducedZero1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1750 (mixedVector B) = 0 := by
  have h3193 : mixedVector B (Sum.inr 3193) = Sparse.eval nodeValue3193 (mixedVector B) := by
    change mixedMoment B node3193 node3193Labels = _
    exact sound3193 B hB hF
  have h3648 : mixedVector B (Sum.inr 3648) = Sparse.eval nodeValue3648 (mixedVector B) := by
    change mixedMoment B node3648 node3648Labels = _
    exact sound3648 B hB hF
  have h3653 : mixedVector B (Sum.inr 3653) = Sparse.eval nodeValue3653 (mixedVector B) := by
    change mixedMoment B node3653 node3653Labels = _
    exact sound3653 B hB hF
  have h3659 : mixedVector B (Sum.inr 3659) = Sparse.eval nodeValue3659 (mixedVector B) := by
    change mixedMoment B node3659 node3659Labels = _
    exact sound3659 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2097, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3193, h3648, h3653, h3659, h3762, h4088, reducedSource1750] using sourceEq2097 B hB

theorem rowSound1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1750 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1750, numericCheck1750, reducedZero1750 B hB hF, mul_zero]

theorem reducedZero1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1751 (mixedVector B) = 0 := by
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1829 : mixedVector B (Sum.inr 1829) = Sparse.eval nodeValue1829 (mixedVector B) := by
    change mixedMoment B node1829 node1829Labels = _
    exact sound1829 B hB hF
  have h1977 : mixedVector B (Sum.inr 1977) = Sparse.eval nodeValue1977 (mixedVector B) := by
    change mixedMoment B node1977 node1977Labels = _
    exact sound1977 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2098, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h950, h1829, h1977, h2094, h2107, h2110, h4083, reducedSource1751] using sourceEq2098 B hB

theorem rowSound1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1751 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1751, numericCheck1751, reducedZero1751 B hB hF, mul_zero]

theorem reducedZero1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1752 (mixedVector B) = 0 := by
  have h2327 : mixedVector B (Sum.inr 2327) = Sparse.eval nodeValue2327 (mixedVector B) := by
    change mixedMoment B node2327 node2327Labels = _
    exact sound2327 B hB hF
  have h2803 : mixedVector B (Sum.inr 2803) = Sparse.eval nodeValue2803 (mixedVector B) := by
    change mixedMoment B node2803 node2803Labels = _
    exact sound2803 B hB hF
  have h3133 : mixedVector B (Sum.inr 3133) = Sparse.eval nodeValue3133 (mixedVector B) := by
    change mixedMoment B node3133 node3133Labels = _
    exact sound3133 B hB hF
  have h3138 : mixedVector B (Sum.inr 3138) = Sparse.eval nodeValue3138 (mixedVector B) := by
    change mixedMoment B node3138 node3138Labels = _
    exact sound3138 B hB hF
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2099, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2327, h2803, h3133, h3138, h3174, h3693, h4092, reducedSource1752] using sourceEq2099 B hB

theorem rowSound1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1752 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1752, numericCheck1752, reducedZero1752 B hB hF, mul_zero]

theorem reducedZero1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1753 (mixedVector B) = 0 := by
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2401 : mixedVector B (Sum.inr 2401) = Sparse.eval nodeValue2401 (mixedVector B) := by
    change mixedMoment B node2401 node2401Labels = _
    exact sound2401 B hB hF
  have h3536 : mixedVector B (Sum.inr 3536) = Sparse.eval nodeValue3536 (mixedVector B) := by
    change mixedMoment B node3536 node3536Labels = _
    exact sound3536 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3630 : mixedVector B (Sum.inr 3630) = Sparse.eval nodeValue3630 (mixedVector B) := by
    change mixedMoment B node3630 node3630Labels = _
    exact sound3630 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2100, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2274, h2401, h3536, h3612, h3630, h3631, h4082, reducedSource1753] using sourceEq2100 B hB

theorem rowSound1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1753 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1753, numericCheck1753, reducedZero1753 B hB hF, mul_zero]

theorem reducedZero1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1754 (mixedVector B) = 0 := by
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2101, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2274, h2276, h2280, h2288, h3631, h4082, reducedSource1754] using sourceEq2101 B hB

theorem rowSound1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1754 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1754, numericCheck1754, reducedZero1754 B hB hF, mul_zero]

theorem reducedZero1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1755 (mixedVector B) = 0 := by
  have h3166 : mixedVector B (Sum.inr 3166) = Sparse.eval nodeValue3166 (mixedVector B) := by
    change mixedMoment B node3166 node3166Labels = _
    exact sound3166 B hB hF
  have h3658 : mixedVector B (Sum.inr 3658) = Sparse.eval nodeValue3658 (mixedVector B) := by
    change mixedMoment B node3658 node3658Labels = _
    exact sound3658 B hB hF
  have h3660 : mixedVector B (Sum.inr 3660) = Sparse.eval nodeValue3660 (mixedVector B) := by
    change mixedMoment B node3660 node3660Labels = _
    exact sound3660 B hB hF
  have h3666 : mixedVector B (Sum.inr 3666) = Sparse.eval nodeValue3666 (mixedVector B) := by
    change mixedMoment B node3666 node3666Labels = _
    exact sound3666 B hB hF
  have h3772 : mixedVector B (Sum.inr 3772) = Sparse.eval nodeValue3772 (mixedVector B) := by
    change mixedMoment B node3772 node3772Labels = _
    exact sound3772 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm2102, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3166, h3658, h3660, h3666, h3772, h4089, reducedSource1755] using sourceEq2102 B hB

theorem rowSound1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1755 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1755, numericCheck1755, reducedZero1755 B hB hF, mul_zero]

theorem reducedZero1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1756 (mixedVector B) = 0 := by
  have h2346 : mixedVector B (Sum.inr 2346) = Sparse.eval nodeValue2346 (mixedVector B) := by
    change mixedMoment B node2346 node2346Labels = _
    exact sound2346 B hB hF
  have h2821 : mixedVector B (Sum.inr 2821) = Sparse.eval nodeValue2821 (mixedVector B) := by
    change mixedMoment B node2821 node2821Labels = _
    exact sound2821 B hB hF
  have h3129 : mixedVector B (Sum.inr 3129) = Sparse.eval nodeValue3129 (mixedVector B) := by
    change mixedMoment B node3129 node3129Labels = _
    exact sound3129 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3397 : mixedVector B (Sum.inr 3397) = Sparse.eval nodeValue3397 (mixedVector B) := by
    change mixedMoment B node3397 node3397Labels = _
    exact sound3397 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2103, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2346, h2821, h3129, h3161, h3397, h4084, reducedSource1756] using sourceEq2103 B hB

theorem rowSound1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1756 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1756, numericCheck1756, reducedZero1756 B hB hF, mul_zero]

theorem reducedZero1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1757 (mixedVector B) = 0 := by
  have h3147 : mixedVector B (Sum.inr 3147) = Sparse.eval nodeValue3147 (mixedVector B) := by
    change mixedMoment B node3147 node3147Labels = _
    exact sound3147 B hB hF
  have h3372 : mixedVector B (Sum.inr 3372) = Sparse.eval nodeValue3372 (mixedVector B) := by
    change mixedMoment B node3372 node3372Labels = _
    exact sound3372 B hB hF
  have h3473 : mixedVector B (Sum.inr 3473) = Sparse.eval nodeValue3473 (mixedVector B) := by
    change mixedMoment B node3473 node3473Labels = _
    exact sound3473 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3611 : mixedVector B (Sum.inr 3611) = Sparse.eval nodeValue3611 (mixedVector B) := by
    change mixedMoment B node3611 node3611Labels = _
    exact sound3611 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2104, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3147, h3372, h3473, h3480, h3611, h4082, reducedSource1757] using sourceEq2104 B hB

theorem rowSound1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1757 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1757, numericCheck1757, reducedZero1757 B hB hF, mul_zero]

theorem reducedZero1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1758 (mixedVector B) = 0 := by
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h2343 : mixedVector B (Sum.inr 2343) = Sparse.eval nodeValue2343 (mixedVector B) := by
    change mixedMoment B node2343 node2343Labels = _
    exact sound2343 B hB hF
  have h2433 : mixedVector B (Sum.inr 2433) = Sparse.eval nodeValue2433 (mixedVector B) := by
    change mixedMoment B node2433 node2433Labels = _
    exact sound2433 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2105, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1141, h2343, h2433, h2499, h2512, h2515, h4092, reducedSource1758] using sourceEq2105 B hB

theorem rowSound1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1758 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1758, numericCheck1758, reducedZero1758 B hB hF, mul_zero]

theorem reducedZero1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1759 (mixedVector B) = 0 := by
  have h2335 : mixedVector B (Sum.inr 2335) = Sparse.eval nodeValue2335 (mixedVector B) := by
    change mixedMoment B node2335 node2335Labels = _
    exact sound2335 B hB hF
  have h2811 : mixedVector B (Sum.inr 2811) = Sparse.eval nodeValue2811 (mixedVector B) := by
    change mixedMoment B node2811 node2811Labels = _
    exact sound2811 B hB hF
  have h2846 : mixedVector B (Sum.inr 2846) = Sparse.eval nodeValue2846 (mixedVector B) := by
    change mixedMoment B node2846 node2846Labels = _
    exact sound2846 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h3705 : mixedVector B (Sum.inr 3705) = Sparse.eval nodeValue3705 (mixedVector B) := by
    change mixedMoment B node3705 node3705Labels = _
    exact sound3705 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2106, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2335, h2811, h2846, h2889, h2979, h3705, h4092, reducedSource1759] using sourceEq2106 B hB

theorem rowSound1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1759 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1759, numericCheck1759, reducedZero1759 B hB hF, mul_zero]

theorem sourceRowsAt1744 : MixedData.sourceRows (1744 : Fin 2425) =
    MixedData.row1744 := by decide +kernel

theorem sourceRowsAt1745 : MixedData.sourceRows (1745 : Fin 2425) =
    MixedData.row1745 := by decide +kernel

theorem sourceRowsAt1746 : MixedData.sourceRows (1746 : Fin 2425) =
    MixedData.row1746 := by decide +kernel

theorem sourceRowsAt1747 : MixedData.sourceRows (1747 : Fin 2425) =
    MixedData.row1747 := by decide +kernel

theorem sourceRowsAt1748 : MixedData.sourceRows (1748 : Fin 2425) =
    MixedData.row1748 := by decide +kernel

theorem sourceRowsAt1749 : MixedData.sourceRows (1749 : Fin 2425) =
    MixedData.row1749 := by decide +kernel

theorem sourceRowsAt1750 : MixedData.sourceRows (1750 : Fin 2425) =
    MixedData.row1750 := by decide +kernel

theorem sourceRowsAt1751 : MixedData.sourceRows (1751 : Fin 2425) =
    MixedData.row1751 := by decide +kernel

theorem sourceRowsAt1752 : MixedData.sourceRows (1752 : Fin 2425) =
    MixedData.row1752 := by decide +kernel

theorem sourceRowsAt1753 : MixedData.sourceRows (1753 : Fin 2425) =
    MixedData.row1753 := by decide +kernel

theorem sourceRowsAt1754 : MixedData.sourceRows (1754 : Fin 2425) =
    MixedData.row1754 := by decide +kernel

theorem sourceRowsAt1755 : MixedData.sourceRows (1755 : Fin 2425) =
    MixedData.row1755 := by decide +kernel

theorem sourceRowsAt1756 : MixedData.sourceRows (1756 : Fin 2425) =
    MixedData.row1756 := by decide +kernel

theorem sourceRowsAt1757 : MixedData.sourceRows (1757 : Fin 2425) =
    MixedData.row1757 := by decide +kernel

theorem sourceRowsAt1758 : MixedData.sourceRows (1758 : Fin 2425) =
    MixedData.row1758 := by decide +kernel

theorem sourceRowsAt1759 : MixedData.sourceRows (1759 : Fin 2425) =
    MixedData.row1759 := by decide +kernel

theorem chunkSound109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 109) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1744 ∨ k.val = 1745 ∨ k.val = 1746 ∨ k.val = 1747 ∨ k.val = 1748 ∨ k.val = 1749 ∨ k.val = 1750 ∨ k.val = 1751 ∨ k.val = 1752 ∨ k.val = 1753 ∨ k.val = 1754 ∨ k.val = 1755 ∨ k.val = 1756 ∨ k.val = 1757 ∨ k.val = 1758 ∨ k.val = 1759 := by omega
  rcases heq with h1744 | h1745 | h1746 | h1747 | h1748 | h1749 | h1750 | h1751 | h1752 | h1753 | h1754 | h1755 | h1756 | h1757 | h1758 | h1759
  · have he : k = (1744 : Fin 2425) := Fin.ext h1744
    subst k
    rw [sourceRowsAt1744]
    exact rowSound1744 B hB hF
  · have he : k = (1745 : Fin 2425) := Fin.ext h1745
    subst k
    rw [sourceRowsAt1745]
    exact rowSound1745 B hB hF
  · have he : k = (1746 : Fin 2425) := Fin.ext h1746
    subst k
    rw [sourceRowsAt1746]
    exact rowSound1746 B hB hF
  · have he : k = (1747 : Fin 2425) := Fin.ext h1747
    subst k
    rw [sourceRowsAt1747]
    exact rowSound1747 B hB hF
  · have he : k = (1748 : Fin 2425) := Fin.ext h1748
    subst k
    rw [sourceRowsAt1748]
    exact rowSound1748 B hB hF
  · have he : k = (1749 : Fin 2425) := Fin.ext h1749
    subst k
    rw [sourceRowsAt1749]
    exact rowSound1749 B hB hF
  · have he : k = (1750 : Fin 2425) := Fin.ext h1750
    subst k
    rw [sourceRowsAt1750]
    exact rowSound1750 B hB hF
  · have he : k = (1751 : Fin 2425) := Fin.ext h1751
    subst k
    rw [sourceRowsAt1751]
    exact rowSound1751 B hB hF
  · have he : k = (1752 : Fin 2425) := Fin.ext h1752
    subst k
    rw [sourceRowsAt1752]
    exact rowSound1752 B hB hF
  · have he : k = (1753 : Fin 2425) := Fin.ext h1753
    subst k
    rw [sourceRowsAt1753]
    exact rowSound1753 B hB hF
  · have he : k = (1754 : Fin 2425) := Fin.ext h1754
    subst k
    rw [sourceRowsAt1754]
    exact rowSound1754 B hB hF
  · have he : k = (1755 : Fin 2425) := Fin.ext h1755
    subst k
    rw [sourceRowsAt1755]
    exact rowSound1755 B hB hF
  · have he : k = (1756 : Fin 2425) := Fin.ext h1756
    subst k
    rw [sourceRowsAt1756]
    exact rowSound1756 B hB hF
  · have he : k = (1757 : Fin 2425) := Fin.ext h1757
    subst k
    rw [sourceRowsAt1757]
    exact rowSound1757 B hB hF
  · have he : k = (1758 : Fin 2425) := Fin.ext h1758
    subst k
    rw [sourceRowsAt1758]
    exact rowSound1758 B hB hF
  · have he : k = (1759 : Fin 2425) := Fin.ext h1759
    subst k
    rw [sourceRowsAt1759]
    exact rowSound1759 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
