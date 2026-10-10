import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources17

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource464 (mixedVector B) = 0 := by
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm552, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3075, h3525, h3534, h3581, h3623, h4083, reducedSource464] using sourceEq552 B hB

theorem rowSound464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row464 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck464, numericCheck464, reducedZero464 B hB hF, mul_zero]

theorem reducedZero465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource465 (mixedVector B) = 0 := by
  have h1382 : mixedVector B (Sum.inr 1382) = Sparse.eval nodeValue1382 (mixedVector B) := by
    change mixedMoment B node1382 node1382Labels = _
    exact sound1382 B hB hF
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h1390 : mixedVector B (Sum.inr 1390) = Sparse.eval nodeValue1390 (mixedVector B) := by
    change mixedMoment B node1390 node1390Labels = _
    exact sound1390 B hB hF
  have h1404 : mixedVector B (Sum.inr 1404) = Sparse.eval nodeValue1404 (mixedVector B) := by
    change mixedMoment B node1404 node1404Labels = _
    exact sound1404 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm553, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1382, h1385, h1390, h1404, h3075, h4083, reducedSource465] using sourceEq553 B hB

theorem rowSound465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row465 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck465, numericCheck465, reducedZero465 B hB hF, mul_zero]

theorem reducedZero466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource466 (mixedVector B) = 0 := by
  have h1382 : mixedVector B (Sum.inr 1382) = Sparse.eval nodeValue1382 (mixedVector B) := by
    change mixedMoment B node1382 node1382Labels = _
    exact sound1382 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h3073 : mixedVector B (Sum.inr 3073) = Sparse.eval nodeValue3073 (mixedVector B) := by
    change mixedMoment B node3073 node3073Labels = _
    exact sound3073 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm554, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1382, h2923, h3073, h3075, h4083, reducedSource466] using sourceEq554 B hB

theorem rowSound466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row466 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck466, numericCheck466, reducedZero466 B hB hF, mul_zero]

theorem reducedZero467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource467 (mixedVector B) = 0 := by
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2980 : mixedVector B (Sum.inr 2980) = Sparse.eval nodeValue2980 (mixedVector B) := by
    change mixedMoment B node2980 node2980Labels = _
    exact sound2980 B hB hF
  have h2983 : mixedVector B (Sum.inr 2983) = Sparse.eval nodeValue2983 (mixedVector B) := by
    change mixedMoment B node2983 node2983Labels = _
    exact sound2983 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm555, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2009, h2980, h2983, h3075, h3525, h4083, reducedSource467] using sourceEq555 B hB

theorem rowSound467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row467 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck467, numericCheck467, reducedZero467 B hB hF, mul_zero]

theorem reducedZero468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource468 (mixedVector B) = 0 := by
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm556, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2025, h2923, h2930, h2952, h3075, h3534, h4083, reducedSource468] using sourceEq556 B hB

theorem rowSound468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row468 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck468, numericCheck468, reducedZero468 B hB hF, mul_zero]

theorem reducedZero469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource469 (mixedVector B) = 0 := by
  have h1390 : mixedVector B (Sum.inr 1390) = Sparse.eval nodeValue1390 (mixedVector B) := by
    change mixedMoment B node1390 node1390Labels = _
    exact sound1390 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2980 : mixedVector B (Sum.inr 2980) = Sparse.eval nodeValue2980 (mixedVector B) := by
    change mixedMoment B node2980 node2980Labels = _
    exact sound2980 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm557, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1390, h2930, h2980, h3075, h3079, h4083, reducedSource469] using sourceEq557 B hB

theorem rowSound469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row469 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck469, numericCheck469, reducedZero469 B hB hF, mul_zero]

theorem reducedZero470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource470 (mixedVector B) = 0 := by
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h3015 : mixedVector B (Sum.inr 3015) = Sparse.eval nodeValue3015 (mixedVector B) := by
    change mixedMoment B node3015 node3015Labels = _
    exact sound3015 B hB hF
  have h3022 : mixedVector B (Sum.inr 3022) = Sparse.eval nodeValue3022 (mixedVector B) := by
    change mixedMoment B node3022 node3022Labels = _
    exact sound3022 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3057 : mixedVector B (Sum.inr 3057) = Sparse.eval nodeValue3057 (mixedVector B) := by
    change mixedMoment B node3057 node3057Labels = _
    exact sound3057 B hB hF
  have h3058 : mixedVector B (Sum.inr 3058) = Sparse.eval nodeValue3058 (mixedVector B) := by
    change mixedMoment B node3058 node3058Labels = _
    exact sound3058 B hB hF
  have h3063 : mixedVector B (Sum.inr 3063) = Sparse.eval nodeValue3063 (mixedVector B) := by
    change mixedMoment B node3063 node3063Labels = _
    exact sound3063 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3072 : mixedVector B (Sum.inr 3072) = Sparse.eval nodeValue3072 (mixedVector B) := by
    change mixedMoment B node3072 node3072Labels = _
    exact sound3072 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223 B hB hF
  simpa only [sourceForm560, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2693, h2702, h2704, h2740, h3015, h3022, h3024, h3052, h3057, h3058, h3063, h3064, h3072, h3075, h3077, h3098, h3101, h3155, h3156, h3158, h3223, reducedSource470] using sourceEq560 B hB

theorem rowSound470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row470 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck470, numericCheck470, reducedZero470 B hB hF, mul_zero]

theorem reducedZero471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource471 (mixedVector B) = 0 := by
  have h1234 : mixedVector B (Sum.inr 1234) = Sparse.eval nodeValue1234 (mixedVector B) := by
    change mixedMoment B node1234 node1234Labels = _
    exact sound1234 B hB hF
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm561, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1234, h2509, h2552, h2738, h2740, h4084, reducedSource471] using sourceEq561 B hB

theorem rowSound471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row471 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck471, numericCheck471, reducedZero471 B hB hF, mul_zero]

theorem reducedZero472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource472 (mixedVector B) = 0 := by
  have h2131 : mixedVector B (Sum.inr 2131) = Sparse.eval nodeValue2131 (mixedVector B) := by
    change mixedMoment B node2131 node2131Labels = _
    exact sound2131 B hB hF
  have h2132 : mixedVector B (Sum.inr 2132) = Sparse.eval nodeValue2132 (mixedVector B) := by
    change mixedMoment B node2132 node2132Labels = _
    exact sound2132 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm562, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2131, h2132, h2133, h2277, h2738, h4084, reducedSource472] using sourceEq562 B hB

theorem rowSound472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row472 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck472, numericCheck472, reducedZero472 B hB hF, mul_zero]

theorem reducedZero473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource473 (mixedVector B) = 0 := by
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5201 : mixedVector B (Sum.inr 5201) = Sparse.eval nodeValue5201 (mixedVector B) := by
    change mixedMoment B node5201 node5201Labels = _
    exact sound5201 B hB hF
  have h5206 : mixedVector B (Sum.inr 5206) = Sparse.eval nodeValue5206 (mixedVector B) := by
    change mixedMoment B node5206 node5206Labels = _
    exact sound5206 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  have h5449 : mixedVector B (Sum.inr 5449) = Sparse.eval nodeValue5449 (mixedVector B) := by
    change mixedMoment B node5449 node5449Labels = _
    exact sound5449 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  simpa only [sourceForm564, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4607, h4609, h4611, h4619, h5144, h5147, h5151, h5163, h5198, h5201, h5206, h5258, h5261, h5274, h5289, h5295, h5304, h5432, h5441, h5449, h5451, reducedSource473] using sourceEq564 B hB

theorem rowSound473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row473 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck473, numericCheck473, reducedZero473 B hB hF, mul_zero]

theorem reducedZero474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource474 (mixedVector B) = 0 := by
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h1302 : mixedVector B (Sum.inr 1302) = Sparse.eval nodeValue1302 (mixedVector B) := by
    change mixedMoment B node1302 node1302Labels = _
    exact sound1302 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h2886 : mixedVector B (Sum.inr 2886) = Sparse.eval nodeValue2886 (mixedVector B) := by
    change mixedMoment B node2886 node2886Labels = _
    exact sound2886 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2961 : mixedVector B (Sum.inr 2961) = Sparse.eval nodeValue2961 (mixedVector B) := by
    change mixedMoment B node2961 node2961Labels = _
    exact sound2961 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3090 : mixedVector B (Sum.inr 3090) = Sparse.eval nodeValue3090 (mixedVector B) := by
    change mixedMoment B node3090 node3090Labels = _
    exact sound3090 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  have h3987 : mixedVector B (Sum.inr 3987) = Sparse.eval nodeValue3987 (mixedVector B) := by
    change mixedMoment B node3987 node3987Labels = _
    exact sound3987 B hB hF
  have h4027 : mixedVector B (Sum.inr 4027) = Sparse.eval nodeValue4027 (mixedVector B) := by
    change mixedMoment B node4027 node4027Labels = _
    exact sound4027 B hB hF
  have h4030 : mixedVector B (Sum.inr 4030) = Sparse.eval nodeValue4030 (mixedVector B) := by
    change mixedMoment B node4030 node4030Labels = _
    exact sound4030 B hB hF
  have h4037 : mixedVector B (Sum.inr 4037) = Sparse.eval nodeValue4037 (mixedVector B) := by
    change mixedMoment B node4037 node4037Labels = _
    exact sound4037 B hB hF
  simpa only [sourceForm565, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1241, h1243, h1245, h1302, h2865, h2885, h2886, h2888, h2928, h2930, h2961, h3089, h3090, h3097, h3098, h3112, h3119, h3987, h4027, h4030, h4037, reducedSource474] using sourceEq565 B hB

theorem rowSound474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row474 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck474, numericCheck474, reducedZero474 B hB hF, mul_zero]

theorem reducedZero475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource475 (mixedVector B) = 0 := by
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3579 : mixedVector B (Sum.inr 3579) = Sparse.eval nodeValue3579 (mixedVector B) := by
    change mixedMoment B node3579 node3579Labels = _
    exact sound3579 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3860 : mixedVector B (Sum.inr 3860) = Sparse.eval nodeValue3860 (mixedVector B) := by
    change mixedMoment B node3860 node3860Labels = _
    exact sound3860 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  simpa only [sourceForm566, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2681, h2683, h2687, h2781, h3296, h3302, h3305, h3530, h3533, h3545, h3547, h3557, h3564, h3570, h3572, h3579, h3583, h3850, h3860, h3886, h3888, reducedSource475] using sourceEq566 B hB

theorem rowSound475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row475 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck475, numericCheck475, reducedZero475 B hB hF, mul_zero]

theorem reducedZero476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource476 (mixedVector B) = 0 := by
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3905 : mixedVector B (Sum.inr 3905) = Sparse.eval nodeValue3905 (mixedVector B) := by
    change mixedMoment B node3905 node3905Labels = _
    exact sound3905 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm567, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2765, h3850, h3886, h3905, h3913, h4092, reducedSource476] using sourceEq567 B hB

theorem rowSound476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row476 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck476, numericCheck476, reducedZero476 B hB hF, mul_zero]

theorem reducedZero477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource477 (mixedVector B) = 0 := by
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm568, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1261, h1264, h1273, h1294, h2765, h4092, reducedSource477] using sourceEq568 B hB

theorem rowSound477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row477 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck477, numericCheck477, reducedZero477 B hB hF, mul_zero]

theorem reducedZero478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource478 (mixedVector B) = 0 := by
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm569, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1294, h2590, h2742, h2765, h2782, h4092, reducedSource478] using sourceEq569 B hB

theorem rowSound478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row478 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck478, numericCheck478, reducedZero478 B hB hF, mul_zero]

theorem reducedZero479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource479 (mixedVector B) = 0 := by
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2635 : mixedVector B (Sum.inr 2635) = Sparse.eval nodeValue2635 (mixedVector B) := by
    change mixedMoment B node2635 node2635Labels = _
    exact sound2635 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm570, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2632, h2635, h2643, h2765, h3886, h4092, reducedSource479] using sourceEq570 B hB

theorem rowSound479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row479 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck479, numericCheck479, reducedZero479 B hB hF, mul_zero]

theorem sourceRowsAt464 : MixedData.sourceRows (464 : Fin 2425) =
    MixedData.row464 := by decide +kernel

theorem sourceRowsAt465 : MixedData.sourceRows (465 : Fin 2425) =
    MixedData.row465 := by decide +kernel

theorem sourceRowsAt466 : MixedData.sourceRows (466 : Fin 2425) =
    MixedData.row466 := by decide +kernel

theorem sourceRowsAt467 : MixedData.sourceRows (467 : Fin 2425) =
    MixedData.row467 := by decide +kernel

theorem sourceRowsAt468 : MixedData.sourceRows (468 : Fin 2425) =
    MixedData.row468 := by decide +kernel

theorem sourceRowsAt469 : MixedData.sourceRows (469 : Fin 2425) =
    MixedData.row469 := by decide +kernel

theorem sourceRowsAt470 : MixedData.sourceRows (470 : Fin 2425) =
    MixedData.row470 := by decide +kernel

theorem sourceRowsAt471 : MixedData.sourceRows (471 : Fin 2425) =
    MixedData.row471 := by decide +kernel

theorem sourceRowsAt472 : MixedData.sourceRows (472 : Fin 2425) =
    MixedData.row472 := by decide +kernel

theorem sourceRowsAt473 : MixedData.sourceRows (473 : Fin 2425) =
    MixedData.row473 := by decide +kernel

theorem sourceRowsAt474 : MixedData.sourceRows (474 : Fin 2425) =
    MixedData.row474 := by decide +kernel

theorem sourceRowsAt475 : MixedData.sourceRows (475 : Fin 2425) =
    MixedData.row475 := by decide +kernel

theorem sourceRowsAt476 : MixedData.sourceRows (476 : Fin 2425) =
    MixedData.row476 := by decide +kernel

theorem sourceRowsAt477 : MixedData.sourceRows (477 : Fin 2425) =
    MixedData.row477 := by decide +kernel

theorem sourceRowsAt478 : MixedData.sourceRows (478 : Fin 2425) =
    MixedData.row478 := by decide +kernel

theorem sourceRowsAt479 : MixedData.sourceRows (479 : Fin 2425) =
    MixedData.row479 := by decide +kernel

theorem chunkSound29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 29) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 464 ∨ k.val = 465 ∨ k.val = 466 ∨ k.val = 467 ∨ k.val = 468 ∨ k.val = 469 ∨ k.val = 470 ∨ k.val = 471 ∨ k.val = 472 ∨ k.val = 473 ∨ k.val = 474 ∨ k.val = 475 ∨ k.val = 476 ∨ k.val = 477 ∨ k.val = 478 ∨ k.val = 479 := by omega
  rcases heq with h464 | h465 | h466 | h467 | h468 | h469 | h470 | h471 | h472 | h473 | h474 | h475 | h476 | h477 | h478 | h479
  · have he : k = (464 : Fin 2425) := Fin.ext h464
    subst k
    rw [sourceRowsAt464]
    exact rowSound464 B hB hF
  · have he : k = (465 : Fin 2425) := Fin.ext h465
    subst k
    rw [sourceRowsAt465]
    exact rowSound465 B hB hF
  · have he : k = (466 : Fin 2425) := Fin.ext h466
    subst k
    rw [sourceRowsAt466]
    exact rowSound466 B hB hF
  · have he : k = (467 : Fin 2425) := Fin.ext h467
    subst k
    rw [sourceRowsAt467]
    exact rowSound467 B hB hF
  · have he : k = (468 : Fin 2425) := Fin.ext h468
    subst k
    rw [sourceRowsAt468]
    exact rowSound468 B hB hF
  · have he : k = (469 : Fin 2425) := Fin.ext h469
    subst k
    rw [sourceRowsAt469]
    exact rowSound469 B hB hF
  · have he : k = (470 : Fin 2425) := Fin.ext h470
    subst k
    rw [sourceRowsAt470]
    exact rowSound470 B hB hF
  · have he : k = (471 : Fin 2425) := Fin.ext h471
    subst k
    rw [sourceRowsAt471]
    exact rowSound471 B hB hF
  · have he : k = (472 : Fin 2425) := Fin.ext h472
    subst k
    rw [sourceRowsAt472]
    exact rowSound472 B hB hF
  · have he : k = (473 : Fin 2425) := Fin.ext h473
    subst k
    rw [sourceRowsAt473]
    exact rowSound473 B hB hF
  · have he : k = (474 : Fin 2425) := Fin.ext h474
    subst k
    rw [sourceRowsAt474]
    exact rowSound474 B hB hF
  · have he : k = (475 : Fin 2425) := Fin.ext h475
    subst k
    rw [sourceRowsAt475]
    exact rowSound475 B hB hF
  · have he : k = (476 : Fin 2425) := Fin.ext h476
    subst k
    rw [sourceRowsAt476]
    exact rowSound476 B hB hF
  · have he : k = (477 : Fin 2425) := Fin.ext h477
    subst k
    rw [sourceRowsAt477]
    exact rowSound477 B hB hF
  · have he : k = (478 : Fin 2425) := Fin.ext h478
    subst k
    rw [sourceRowsAt478]
    exact rowSound478 B hB hF
  · have he : k = (479 : Fin 2425) := Fin.ext h479
    subst k
    rw [sourceRowsAt479]
    exact rowSound479 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
