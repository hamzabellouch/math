import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources8

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource224 (mixedVector B) = 0 := by
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm264, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2714, h2716, h2724, h2732, h2758, h3814, h4092, reducedSource224] using sourceEq264 B hB

theorem rowSound224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row224 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck224, numericCheck224, reducedZero224 B hB hF, mul_zero]

theorem reducedZero225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource225 (mixedVector B) = 0 := by
  have h1218 : mixedVector B (Sum.inr 1218) = Sparse.eval nodeValue1218 (mixedVector B) := by
    change mixedMoment B node1218 node1218Labels = _
    exact sound1218 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2544 : mixedVector B (Sum.inr 2544) = Sparse.eval nodeValue2544 (mixedVector B) := by
    change mixedMoment B node2544 node2544Labels = _
    exact sound2544 B hB hF
  have h2619 : mixedVector B (Sum.inr 2619) = Sparse.eval nodeValue2619 (mixedVector B) := by
    change mixedMoment B node2619 node2619Labels = _
    exact sound2619 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm265, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1218, h2486, h2544, h2619, h2716, h2724, h4092, reducedSource225] using sourceEq265 B hB

theorem rowSound225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row225 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck225, numericCheck225, reducedZero225 B hB hF, mul_zero]

theorem reducedZero226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource226 (mixedVector B) = 0 := by
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1608 : mixedVector B (Sum.inr 1608) = Sparse.eval nodeValue1608 (mixedVector B) := by
    change mixedMoment B node1608 node1608Labels = _
    exact sound1608 B hB hF
  have h1612 : mixedVector B (Sum.inr 1612) = Sparse.eval nodeValue1612 (mixedVector B) := by
    change mixedMoment B node1612 node1612Labels = _
    exact sound1612 B hB hF
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h2538 : mixedVector B (Sum.inr 2538) = Sparse.eval nodeValue2538 (mixedVector B) := by
    change mixedMoment B node2538 node2538Labels = _
    exact sound2538 B hB hF
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h3346 : mixedVector B (Sum.inr 3346) = Sparse.eval nodeValue3346 (mixedVector B) := by
    change mixedMoment B node3346 node3346Labels = _
    exact sound3346 B hB hF
  have h3349 : mixedVector B (Sum.inr 3349) = Sparse.eval nodeValue3349 (mixedVector B) := by
    change mixedMoment B node3349 node3349Labels = _
    exact sound3349 B hB hF
  have h3355 : mixedVector B (Sum.inr 3355) = Sparse.eval nodeValue3355 (mixedVector B) := by
    change mixedMoment B node3355 node3355Labels = _
    exact sound3355 B hB hF
  have h3431 : mixedVector B (Sum.inr 3431) = Sparse.eval nodeValue3431 (mixedVector B) := by
    change mixedMoment B node3431 node3431Labels = _
    exact sound3431 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3507 : mixedVector B (Sum.inr 3507) = Sparse.eval nodeValue3507 (mixedVector B) := by
    change mixedMoment B node3507 node3507Labels = _
    exact sound3507 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3997 : mixedVector B (Sum.inr 3997) = Sparse.eval nodeValue3997 (mixedVector B) := by
    change mixedMoment B node3997 node3997Labels = _
    exact sound3997 B hB hF
  simpa only [sourceForm268, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1607, h1608, h1612, h1619, h1714, h2534, h2538, h2588, h2670, h3346, h3349, h3355, h3431, h3434, h3463, h3503, h3507, h3517, h3523, h3539, h3540, h3543, h3572, h3606, h3625, h3848, h3857, h3858, h3884, h3997, reducedSource226] using sourceEq268 B hB

theorem rowSound226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row226 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck226, numericCheck226, reducedZero226 B hB hF, mul_zero]

theorem reducedZero227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource227 (mixedVector B) = 0 := by
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm269, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3086, h3871, h3876, h3881, h3902, h3983, h4091, reducedSource227] using sourceEq269 B hB

theorem rowSound227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row227 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck227, numericCheck227, reducedZero227 B hB hF, mul_zero]

theorem reducedZero228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource228 (mixedVector B) = 0 := by
  have h1392 : mixedVector B (Sum.inr 1392) = Sparse.eval nodeValue1392 (mixedVector B) := by
    change mixedMoment B node1392 node1392Labels = _
    exact sound1392 B hB hF
  have h1394 : mixedVector B (Sum.inr 1394) = Sparse.eval nodeValue1394 (mixedVector B) := by
    change mixedMoment B node1394 node1394Labels = _
    exact sound1394 B hB hF
  have h1400 : mixedVector B (Sum.inr 1400) = Sparse.eval nodeValue1400 (mixedVector B) := by
    change mixedMoment B node1400 node1400Labels = _
    exact sound1400 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h1425 : mixedVector B (Sum.inr 1425) = Sparse.eval nodeValue1425 (mixedVector B) := by
    change mixedMoment B node1425 node1425Labels = _
    exact sound1425 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm270, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1392, h1394, h1400, h1406, h1425, h3086, h4091, reducedSource228] using sourceEq270 B hB

theorem rowSound228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row228 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck228, numericCheck228, reducedZero228 B hB hF, mul_zero]

theorem reducedZero229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource229 (mixedVector B) = 0 := by
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm271, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1406, h2954, h2984, h3077, h3086, h3097, h4091, reducedSource229] using sourceEq271 B hB

theorem rowSound229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row229 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck229, numericCheck229, reducedZero229 B hB hF, mul_zero]

theorem reducedZero230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource230 (mixedVector B) = 0 := by
  have h2624 : mixedVector B (Sum.inr 2624) = Sparse.eval nodeValue2624 (mixedVector B) := by
    change mixedMoment B node2624 node2624Labels = _
    exact sound2624 B hB hF
  have h2949 : mixedVector B (Sum.inr 2949) = Sparse.eval nodeValue2949 (mixedVector B) := by
    change mixedMoment B node2949 node2949Labels = _
    exact sound2949 B hB hF
  have h3013 : mixedVector B (Sum.inr 3013) = Sparse.eval nodeValue3013 (mixedVector B) := by
    change mixedMoment B node3013 node3013Labels = _
    exact sound3013 B hB hF
  have h3014 : mixedVector B (Sum.inr 3014) = Sparse.eval nodeValue3014 (mixedVector B) := by
    change mixedMoment B node3014 node3014Labels = _
    exact sound3014 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm272, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2624, h2949, h3013, h3014, h3086, h3881, h4091, reducedSource230] using sourceEq272 B hB

theorem rowSound230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row230 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck230, numericCheck230, reducedZero230 B hB hF, mul_zero]

theorem reducedZero231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource231 (mixedVector B) = 0 := by
  have h1392 : mixedVector B (Sum.inr 1392) = Sparse.eval nodeValue1392 (mixedVector B) := by
    change mixedMoment B node1392 node1392Labels = _
    exact sound1392 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h3013 : mixedVector B (Sum.inr 3013) = Sparse.eval nodeValue3013 (mixedVector B) := by
    change mixedMoment B node3013 node3013Labels = _
    exact sound3013 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3084 : mixedVector B (Sum.inr 3084) = Sparse.eval nodeValue3084 (mixedVector B) := by
    change mixedMoment B node3084 node3084Labels = _
    exact sound3084 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm273, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1392, h2933, h3013, h3064, h3084, h3086, h4091, reducedSource231] using sourceEq273 B hB

theorem rowSound231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row231 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck231, numericCheck231, reducedZero231 B hB hF, mul_zero]

theorem reducedZero232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource232 (mixedVector B) = 0 := by
  have h2610 : mixedVector B (Sum.inr 2610) = Sparse.eval nodeValue2610 (mixedVector B) := by
    change mixedMoment B node2610 node2610Labels = _
    exact sound2610 B hB hF
  have h2947 : mixedVector B (Sum.inr 2947) = Sparse.eval nodeValue2947 (mixedVector B) := by
    change mixedMoment B node2947 node2947Labels = _
    exact sound2947 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h2992 : mixedVector B (Sum.inr 2992) = Sparse.eval nodeValue2992 (mixedVector B) := by
    change mixedMoment B node2992 node2992Labels = _
    exact sound2992 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm274, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2610, h2947, h2984, h2992, h3086, h3871, h4091, reducedSource232] using sourceEq274 B hB

theorem rowSound232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row232 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck232, numericCheck232, reducedZero232 B hB hF, mul_zero]

theorem reducedZero233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource233 (mixedVector B) = 0 := by
  have h1425 : mixedVector B (Sum.inr 1425) = Sparse.eval nodeValue1425 (mixedVector B) := by
    change mixedMoment B node1425 node1425Labels = _
    exact sound1425 B hB hF
  have h2992 : mixedVector B (Sum.inr 2992) = Sparse.eval nodeValue2992 (mixedVector B) := by
    change mixedMoment B node2992 node2992Labels = _
    exact sound2992 B hB hF
  have h3014 : mixedVector B (Sum.inr 3014) = Sparse.eval nodeValue3014 (mixedVector B) := by
    change mixedMoment B node3014 node3014Labels = _
    exact sound3014 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3108 : mixedVector B (Sum.inr 3108) = Sparse.eval nodeValue3108 (mixedVector B) := by
    change mixedMoment B node3108 node3108Labels = _
    exact sound3108 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm275, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1425, h2992, h3014, h3086, h3108, h4091, reducedSource233] using sourceEq275 B hB

theorem rowSound233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row233 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck233, numericCheck233, reducedZero233 B hB hF, mul_zero]

theorem reducedZero234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource234 (mixedVector B) = 0 := by
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm276, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2618, h2933, h2942, h2954, h3086, h3876, h4091, reducedSource234] using sourceEq276 B hB

theorem rowSound234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row234 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck234, numericCheck234, reducedZero234 B hB hF, mul_zero]

theorem reducedZero235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource235 (mixedVector B) = 0 := by
  have h1400 : mixedVector B (Sum.inr 1400) = Sparse.eval nodeValue1400 (mixedVector B) := by
    change mixedMoment B node1400 node1400Labels = _
    exact sound1400 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2947 : mixedVector B (Sum.inr 2947) = Sparse.eval nodeValue2947 (mixedVector B) := by
    change mixedMoment B node2947 node2947Labels = _
    exact sound2947 B hB hF
  have h2949 : mixedVector B (Sum.inr 2949) = Sparse.eval nodeValue2949 (mixedVector B) := by
    change mixedMoment B node2949 node2949Labels = _
    exact sound2949 B hB hF
  have h2964 : mixedVector B (Sum.inr 2964) = Sparse.eval nodeValue2964 (mixedVector B) := by
    change mixedMoment B node2964 node2964Labels = _
    exact sound2964 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm277, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1400, h2942, h2947, h2949, h2964, h3086, h4091, reducedSource235] using sourceEq277 B hB

theorem rowSound235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row235 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck235, numericCheck235, reducedZero235 B hB hF, mul_zero]

theorem reducedZero236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource236 (mixedVector B) = 0 := by
  have h2496 : mixedVector B (Sum.inr 2496) = Sparse.eval nodeValue2496 (mixedVector B) := by
    change mixedMoment B node2496 node2496Labels = _
    exact sound2496 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2498 : mixedVector B (Sum.inr 2498) = Sparse.eval nodeValue2498 (mixedVector B) := by
    change mixedMoment B node2498 node2498Labels = _
    exact sound2498 B hB hF
  have h2516 : mixedVector B (Sum.inr 2516) = Sparse.eval nodeValue2516 (mixedVector B) := by
    change mixedMoment B node2516 node2516Labels = _
    exact sound2516 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h3028 : mixedVector B (Sum.inr 3028) = Sparse.eval nodeValue3028 (mixedVector B) := by
    change mixedMoment B node3028 node3028Labels = _
    exact sound3028 B hB hF
  have h3035 : mixedVector B (Sum.inr 3035) = Sparse.eval nodeValue3035 (mixedVector B) := by
    change mixedMoment B node3035 node3035Labels = _
    exact sound3035 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3042 : mixedVector B (Sum.inr 3042) = Sparse.eval nodeValue3042 (mixedVector B) := by
    change mixedMoment B node3042 node3042Labels = _
    exact sound3042 B hB hF
  have h3063 : mixedVector B (Sum.inr 3063) = Sparse.eval nodeValue3063 (mixedVector B) := by
    change mixedMoment B node3063 node3063Labels = _
    exact sound3063 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3067 : mixedVector B (Sum.inr 3067) = Sparse.eval nodeValue3067 (mixedVector B) := by
    change mixedMoment B node3067 node3067Labels = _
    exact sound3067 B hB hF
  have h3080 : mixedVector B (Sum.inr 3080) = Sparse.eval nodeValue3080 (mixedVector B) := by
    change mixedMoment B node3080 node3080Labels = _
    exact sound3080 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3211 : mixedVector B (Sum.inr 3211) = Sparse.eval nodeValue3211 (mixedVector B) := by
    change mixedMoment B node3211 node3211Labels = _
    exact sound3211 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  simpa only [sourceForm280, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2496, h2497, h2498, h2516, h2708, h2719, h2722, h2729, h2765, h2777, h3028, h3035, h3038, h3042, h3063, h3064, h3067, h3080, h3086, h3088, h3092, h3098, h3101, h3110, h3121, h3197, h3198, h3211, h3225, reducedSource236] using sourceEq280 B hB

theorem rowSound236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row236 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck236, numericCheck236, reducedZero236 B hB hF, mul_zero]

theorem reducedZero237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource237 (mixedVector B) = 0 := by
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm281, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2588, h3502, h3506, h3533, h3540, h3582, h4084, reducedSource237] using sourceEq281 B hB

theorem rowSound237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row237 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck237, numericCheck237, reducedZero237 B hB hF, mul_zero]

theorem reducedZero238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource238 (mixedVector B) = 0 := by
  have h2033 : mixedVector B (Sum.inr 2033) = Sparse.eval nodeValue2033 (mixedVector B) := by
    change mixedMoment B node2033 node2033Labels = _
    exact sound2033 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm282, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2033, h2035, h2039, h2054, h2278, h3540, h4084, reducedSource238] using sourceEq282 B hB

theorem rowSound238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row238 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck238, numericCheck238, reducedZero238 B hB hF, mul_zero]

theorem reducedZero239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource239 (mixedVector B) = 0 := by
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm283, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2278, h2781, h3540, h3632, h3633, h4084, reducedSource239] using sourceEq283 B hB

theorem rowSound239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row239 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck239, numericCheck239, reducedZero239 B hB hF, mul_zero]

theorem sourceRowsAt224 : MixedData.sourceRows (224 : Fin 2425) =
    MixedData.row224 := by decide +kernel

theorem sourceRowsAt225 : MixedData.sourceRows (225 : Fin 2425) =
    MixedData.row225 := by decide +kernel

theorem sourceRowsAt226 : MixedData.sourceRows (226 : Fin 2425) =
    MixedData.row226 := by decide +kernel

theorem sourceRowsAt227 : MixedData.sourceRows (227 : Fin 2425) =
    MixedData.row227 := by decide +kernel

theorem sourceRowsAt228 : MixedData.sourceRows (228 : Fin 2425) =
    MixedData.row228 := by decide +kernel

theorem sourceRowsAt229 : MixedData.sourceRows (229 : Fin 2425) =
    MixedData.row229 := by decide +kernel

theorem sourceRowsAt230 : MixedData.sourceRows (230 : Fin 2425) =
    MixedData.row230 := by decide +kernel

theorem sourceRowsAt231 : MixedData.sourceRows (231 : Fin 2425) =
    MixedData.row231 := by decide +kernel

theorem sourceRowsAt232 : MixedData.sourceRows (232 : Fin 2425) =
    MixedData.row232 := by decide +kernel

theorem sourceRowsAt233 : MixedData.sourceRows (233 : Fin 2425) =
    MixedData.row233 := by decide +kernel

theorem sourceRowsAt234 : MixedData.sourceRows (234 : Fin 2425) =
    MixedData.row234 := by decide +kernel

theorem sourceRowsAt235 : MixedData.sourceRows (235 : Fin 2425) =
    MixedData.row235 := by decide +kernel

theorem sourceRowsAt236 : MixedData.sourceRows (236 : Fin 2425) =
    MixedData.row236 := by decide +kernel

theorem sourceRowsAt237 : MixedData.sourceRows (237 : Fin 2425) =
    MixedData.row237 := by decide +kernel

theorem sourceRowsAt238 : MixedData.sourceRows (238 : Fin 2425) =
    MixedData.row238 := by decide +kernel

theorem sourceRowsAt239 : MixedData.sourceRows (239 : Fin 2425) =
    MixedData.row239 := by decide +kernel

theorem chunkSound14 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 14) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 224 ∨ k.val = 225 ∨ k.val = 226 ∨ k.val = 227 ∨ k.val = 228 ∨ k.val = 229 ∨ k.val = 230 ∨ k.val = 231 ∨ k.val = 232 ∨ k.val = 233 ∨ k.val = 234 ∨ k.val = 235 ∨ k.val = 236 ∨ k.val = 237 ∨ k.val = 238 ∨ k.val = 239 := by omega
  rcases heq with h224 | h225 | h226 | h227 | h228 | h229 | h230 | h231 | h232 | h233 | h234 | h235 | h236 | h237 | h238 | h239
  · have he : k = (224 : Fin 2425) := Fin.ext h224
    subst k
    rw [sourceRowsAt224]
    exact rowSound224 B hB hF
  · have he : k = (225 : Fin 2425) := Fin.ext h225
    subst k
    rw [sourceRowsAt225]
    exact rowSound225 B hB hF
  · have he : k = (226 : Fin 2425) := Fin.ext h226
    subst k
    rw [sourceRowsAt226]
    exact rowSound226 B hB hF
  · have he : k = (227 : Fin 2425) := Fin.ext h227
    subst k
    rw [sourceRowsAt227]
    exact rowSound227 B hB hF
  · have he : k = (228 : Fin 2425) := Fin.ext h228
    subst k
    rw [sourceRowsAt228]
    exact rowSound228 B hB hF
  · have he : k = (229 : Fin 2425) := Fin.ext h229
    subst k
    rw [sourceRowsAt229]
    exact rowSound229 B hB hF
  · have he : k = (230 : Fin 2425) := Fin.ext h230
    subst k
    rw [sourceRowsAt230]
    exact rowSound230 B hB hF
  · have he : k = (231 : Fin 2425) := Fin.ext h231
    subst k
    rw [sourceRowsAt231]
    exact rowSound231 B hB hF
  · have he : k = (232 : Fin 2425) := Fin.ext h232
    subst k
    rw [sourceRowsAt232]
    exact rowSound232 B hB hF
  · have he : k = (233 : Fin 2425) := Fin.ext h233
    subst k
    rw [sourceRowsAt233]
    exact rowSound233 B hB hF
  · have he : k = (234 : Fin 2425) := Fin.ext h234
    subst k
    rw [sourceRowsAt234]
    exact rowSound234 B hB hF
  · have he : k = (235 : Fin 2425) := Fin.ext h235
    subst k
    rw [sourceRowsAt235]
    exact rowSound235 B hB hF
  · have he : k = (236 : Fin 2425) := Fin.ext h236
    subst k
    rw [sourceRowsAt236]
    exact rowSound236 B hB hF
  · have he : k = (237 : Fin 2425) := Fin.ext h237
    subst k
    rw [sourceRowsAt237]
    exact rowSound237 B hB hF
  · have he : k = (238 : Fin 2425) := Fin.ext h238
    subst k
    rw [sourceRowsAt238]
    exact rowSound238 B hB hF
  · have he : k = (239 : Fin 2425) := Fin.ext h239
    subst k
    rw [sourceRowsAt239]
    exact rowSound239 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
