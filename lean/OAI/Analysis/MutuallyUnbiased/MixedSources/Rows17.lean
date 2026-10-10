import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources10

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource272 (mixedVector B) = 0 := by
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm321, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2266, h3535, h3584, h3626, h3627, h4084, reducedSource272] using sourceEq321 B hB

theorem rowSound272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row272 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck272, numericCheck272, reducedZero272 B hB hF, mul_zero]

theorem reducedZero273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource273 (mixedVector B) = 0 := by
  have h3159 : mixedVector B (Sum.inr 3159) = Sparse.eval nodeValue3159 (mixedVector B) := by
    change mixedMoment B node3159 node3159Labels = _
    exact sound3159 B hB hF
  have h3377 : mixedVector B (Sum.inr 3377) = Sparse.eval nodeValue3377 (mixedVector B) := by
    change mixedMoment B node3377 node3377Labels = _
    exact sound3377 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm322, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3159, h3377, h3379, h3395, h3535, h4084, reducedSource273] using sourceEq322 B hB

theorem rowSound273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row273 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck273, numericCheck273, reducedZero273 B hB hF, mul_zero]

theorem reducedZero274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource274 (mixedVector B) = 0 := by
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h3377 : mixedVector B (Sum.inr 3377) = Sparse.eval nodeValue3377 (mixedVector B) := by
    change mixedMoment B node3377 node3377Labels = _
    exact sound3377 B hB hF
  have h3504 : mixedVector B (Sum.inr 3504) = Sparse.eval nodeValue3504 (mixedVector B) := by
    change mixedMoment B node3504 node3504Labels = _
    exact sound3504 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm323, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2021, h3377, h3504, h3528, h3531, h3535, h4084, reducedSource274] using sourceEq323 B hB

theorem rowSound274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row274 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck274, numericCheck274, reducedZero274 B hB hF, mul_zero]

theorem reducedZero275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource275 (mixedVector B) = 0 := by
  have h3153 : mixedVector B (Sum.inr 3153) = Sparse.eval nodeValue3153 (mixedVector B) := by
    change mixedMoment B node3153 node3153Labels = _
    exact sound3153 B hB hF
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3497 : mixedVector B (Sum.inr 3497) = Sparse.eval nodeValue3497 (mixedVector B) := by
    change mixedMoment B node3497 node3497Labels = _
    exact sound3497 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm324, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3153, h3388, h3488, h3497, h3535, h4084, reducedSource275] using sourceEq324 B hB

theorem rowSound275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row275 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck275, numericCheck275, reducedZero275 B hB hF, mul_zero]

theorem reducedZero276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource276 (mixedVector B) = 0 := by
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h3153 : mixedVector B (Sum.inr 3153) = Sparse.eval nodeValue3153 (mixedVector B) := by
    change mixedMoment B node3153 node3153Labels = _
    exact sound3153 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3157 : mixedVector B (Sum.inr 3157) = Sparse.eval nodeValue3157 (mixedVector B) := by
    change mixedMoment B node3157 node3157Labels = _
    exact sound3157 B hB hF
  have h3159 : mixedVector B (Sum.inr 3159) = Sparse.eval nodeValue3159 (mixedVector B) := by
    change mixedMoment B node3159 node3159Labels = _
    exact sound3159 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm325, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2026, h3153, h3156, h3157, h3159, h3535, h4084, reducedSource276] using sourceEq325 B hB

theorem rowSound276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row276 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck276, numericCheck276, reducedZero276 B hB hF, mul_zero]

theorem reducedZero277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource277 (mixedVector B) = 0 := by
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm326, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3531, h3533, h3535, h3544, h3627, h4084, reducedSource277] using sourceEq326 B hB

theorem rowSound277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row277 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck277, numericCheck277, reducedZero277 B hB hF, mul_zero]

theorem reducedZero278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource278 (mixedVector B) = 0 := by
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3497 : mixedVector B (Sum.inr 3497) = Sparse.eval nodeValue3497 (mixedVector B) := by
    change mixedMoment B node3497 node3497Labels = _
    exact sound3497 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm327, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2058, h3395, h3497, h3535, h3541, h3544, h4084, reducedSource278] using sourceEq327 B hB

theorem rowSound278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row278 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck278, numericCheck278, reducedZero278 B hB hF, mul_zero]

theorem reducedZero279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource279 (mixedVector B) = 0 := by
  have h3157 : mixedVector B (Sum.inr 3157) = Sparse.eval nodeValue3157 (mixedVector B) := by
    change mixedMoment B node3157 node3157Labels = _
    exact sound3157 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3504 : mixedVector B (Sum.inr 3504) = Sparse.eval nodeValue3504 (mixedVector B) := by
    change mixedMoment B node3504 node3504Labels = _
    exact sound3504 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm328, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3157, h3392, h3504, h3506, h3535, h3584, h4084, reducedSource279] using sourceEq328 B hB

theorem rowSound279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row279 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck279, numericCheck279, reducedZero279 B hB hF, mul_zero]

theorem reducedZero280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource280 (mixedVector B) = 0 := by
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm329, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2028, h3379, h3488, h3506, h3533, h3535, h4084, reducedSource280] using sourceEq329 B hB

theorem rowSound280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row280 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck280, numericCheck280, reducedZero280 B hB hF, mul_zero]

theorem reducedZero281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource281 (mixedVector B) = 0 := by
  have h1178 : mixedVector B (Sum.inr 1178) = Sparse.eval nodeValue1178 (mixedVector B) := by
    change mixedMoment B node1178 node1178Labels = _
    exact sound1178 B hB hF
  have h1179 : mixedVector B (Sum.inr 1179) = Sparse.eval nodeValue1179 (mixedVector B) := by
    change mixedMoment B node1179 node1179Labels = _
    exact sound1179 B hB hF
  have h1182 : mixedVector B (Sum.inr 1182) = Sparse.eval nodeValue1182 (mixedVector B) := by
    change mixedMoment B node1182 node1182Labels = _
    exact sound1182 B hB hF
  have h1185 : mixedVector B (Sum.inr 1185) = Sparse.eval nodeValue1185 (mixedVector B) := by
    change mixedMoment B node1185 node1185Labels = _
    exact sound1185 B hB hF
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h1992 : mixedVector B (Sum.inr 1992) = Sparse.eval nodeValue1992 (mixedVector B) := by
    change mixedMoment B node1992 node1992Labels = _
    exact sound1992 B hB hF
  have h2004 : mixedVector B (Sum.inr 2004) = Sparse.eval nodeValue2004 (mixedVector B) := by
    change mixedMoment B node2004 node2004Labels = _
    exact sound2004 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2833 : mixedVector B (Sum.inr 2833) = Sparse.eval nodeValue2833 (mixedVector B) := by
    change mixedMoment B node2833 node2833Labels = _
    exact sound2833 B hB hF
  have h2835 : mixedVector B (Sum.inr 2835) = Sparse.eval nodeValue2835 (mixedVector B) := by
    change mixedMoment B node2835 node2835Labels = _
    exact sound2835 B hB hF
  have h2838 : mixedVector B (Sum.inr 2838) = Sparse.eval nodeValue2838 (mixedVector B) := by
    change mixedMoment B node2838 node2838Labels = _
    exact sound2838 B hB hF
  have h2905 : mixedVector B (Sum.inr 2905) = Sparse.eval nodeValue2905 (mixedVector B) := by
    change mixedMoment B node2905 node2905Labels = _
    exact sound2905 B hB hF
  have h2907 : mixedVector B (Sum.inr 2907) = Sparse.eval nodeValue2907 (mixedVector B) := by
    change mixedMoment B node2907 node2907Labels = _
    exact sound2907 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h2997 : mixedVector B (Sum.inr 2997) = Sparse.eval nodeValue2997 (mixedVector B) := by
    change mixedMoment B node2997 node2997Labels = _
    exact sound2997 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  simpa only [sourceForm331, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1178, h1179, h1182, h1185, h1261, h1992, h2004, h2035, h2197, h2833, h2835, h2838, h2905, h2907, h2933, h2974, h2979, h2997, h3016, h3025, h3037, h3039, h3051, h3086, h3109, h3541, h3814, h3841, h3853, h3856, reducedSource281] using sourceEq331 B hB

theorem rowSound281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row281 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck281, numericCheck281, reducedZero281 B hB hF, mul_zero]

theorem reducedZero282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource282 (mixedVector B) = 0 := by
  have h2001 : mixedVector B (Sum.inr 2001) = Sparse.eval nodeValue2001 (mixedVector B) := by
    change mixedMoment B node2001 node2001Labels = _
    exact sound2001 B hB hF
  have h2004 : mixedVector B (Sum.inr 2004) = Sparse.eval nodeValue2004 (mixedVector B) := by
    change mixedMoment B node2004 node2004Labels = _
    exact sound2004 B hB hF
  have h2005 : mixedVector B (Sum.inr 2005) = Sparse.eval nodeValue2005 (mixedVector B) := by
    change mixedMoment B node2005 node2005Labels = _
    exact sound2005 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2833 : mixedVector B (Sum.inr 2833) = Sparse.eval nodeValue2833 (mixedVector B) := by
    change mixedMoment B node2833 node2833Labels = _
    exact sound2833 B hB hF
  have h2835 : mixedVector B (Sum.inr 2835) = Sparse.eval nodeValue2835 (mixedVector B) := by
    change mixedMoment B node2835 node2835Labels = _
    exact sound2835 B hB hF
  have h2838 : mixedVector B (Sum.inr 2838) = Sparse.eval nodeValue2838 (mixedVector B) := by
    change mixedMoment B node2838 node2838Labels = _
    exact sound2838 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3238 : mixedVector B (Sum.inr 3238) = Sparse.eval nodeValue3238 (mixedVector B) := by
    change mixedMoment B node3238 node3238Labels = _
    exact sound3238 B hB hF
  have h3240 : mixedVector B (Sum.inr 3240) = Sparse.eval nodeValue3240 (mixedVector B) := by
    change mixedMoment B node3240 node3240Labels = _
    exact sound3240 B hB hF
  have h3243 : mixedVector B (Sum.inr 3243) = Sparse.eval nodeValue3243 (mixedVector B) := by
    change mixedMoment B node3243 node3243Labels = _
    exact sound3243 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3518 : mixedVector B (Sum.inr 3518) = Sparse.eval nodeValue3518 (mixedVector B) := by
    change mixedMoment B node3518 node3518Labels = _
    exact sound3518 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3561 : mixedVector B (Sum.inr 3561) = Sparse.eval nodeValue3561 (mixedVector B) := by
    change mixedMoment B node3561 node3561Labels = _
    exact sound3561 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  simpa only [sourceForm332, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2001, h2004, h2005, h2055, h2207, h2833, h2835, h2838, h3038, h3238, h3240, h3243, h3296, h3464, h3479, h3480, h3517, h3518, h3526, h3528, h3534, h3535, h3540, h3561, h3573, h3577, h3814, h3841, h3853, h3856, reducedSource282] using sourceEq332 B hB

theorem rowSound282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row282 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck282, numericCheck282, reducedZero282 B hB hF, mul_zero]

theorem reducedZero283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource283 (mixedVector B) = 0 := by
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3906 : mixedVector B (Sum.inr 3906) = Sparse.eval nodeValue3906 (mixedVector B) := by
    change mixedMoment B node3906 node3906Labels = _
    exact sound3906 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm333, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2732, h3814, h3841, h3906, h4092, reducedSource283] using sourceEq333 B hB

theorem rowSound283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row283 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck283, numericCheck283, reducedZero283 B hB hF, mul_zero]

theorem reducedZero284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource284 (mixedVector B) = 0 := by
  have h1278 : mixedVector B (Sum.inr 1278) = Sparse.eval nodeValue1278 (mixedVector B) := by
    change mixedMoment B node1278 node1278Labels = _
    exact sound1278 B hB hF
  have h2578 : mixedVector B (Sum.inr 2578) = Sparse.eval nodeValue2578 (mixedVector B) := by
    change mixedMoment B node2578 node2578Labels = _
    exact sound2578 B hB hF
  have h2649 : mixedVector B (Sum.inr 2649) = Sparse.eval nodeValue2649 (mixedVector B) := by
    change mixedMoment B node2649 node2649Labels = _
    exact sound2649 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm335, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1278, h2578, h2649, h2732, h2758, h2773, h4092, reducedSource284] using sourceEq335 B hB

theorem rowSound284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row284 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck284, numericCheck284, reducedZero284 B hB hF, mul_zero]

theorem reducedZero285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource285 (mixedVector B) = 0 := by
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm336, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2494, h2497, h2499, h2515, h2732, h3814, h4092, reducedSource285] using sourceEq336 B hB

theorem rowSound285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row285 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck285, numericCheck285, reducedZero285 B hB hF, mul_zero]

theorem reducedZero286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource286 (mixedVector B) = 0 := by
  have h990 : mixedVector B (Sum.inr 990) = Sparse.eval nodeValue990 (mixedVector B) := by
    change mixedMoment B node990 node990Labels = _
    exact sound990 B hB hF
  have h991 : mixedVector B (Sum.inr 991) = Sparse.eval nodeValue991 (mixedVector B) := by
    change mixedMoment B node991 node991Labels = _
    exact sound991 B hB hF
  have h992 : mixedVector B (Sum.inr 992) = Sparse.eval nodeValue992 (mixedVector B) := by
    change mixedMoment B node992 node992Labels = _
    exact sound992 B hB hF
  have h1006 : mixedVector B (Sum.inr 1006) = Sparse.eval nodeValue1006 (mixedVector B) := by
    change mixedMoment B node1006 node1006Labels = _
    exact sound1006 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h2392 : mixedVector B (Sum.inr 2392) = Sparse.eval nodeValue2392 (mixedVector B) := by
    change mixedMoment B node2392 node2392Labels = _
    exact sound2392 B hB hF
  have h2393 : mixedVector B (Sum.inr 2393) = Sparse.eval nodeValue2393 (mixedVector B) := by
    change mixedMoment B node2393 node2393Labels = _
    exact sound2393 B hB hF
  have h2394 : mixedVector B (Sum.inr 2394) = Sparse.eval nodeValue2394 (mixedVector B) := by
    change mixedMoment B node2394 node2394Labels = _
    exact sound2394 B hB hF
  have h2405 : mixedVector B (Sum.inr 2405) = Sparse.eval nodeValue2405 (mixedVector B) := by
    change mixedMoment B node2405 node2405Labels = _
    exact sound2405 B hB hF
  have h2454 : mixedVector B (Sum.inr 2454) = Sparse.eval nodeValue2454 (mixedVector B) := by
    change mixedMoment B node2454 node2454Labels = _
    exact sound2454 B hB hF
  have h2455 : mixedVector B (Sum.inr 2455) = Sparse.eval nodeValue2455 (mixedVector B) := by
    change mixedMoment B node2455 node2455Labels = _
    exact sound2455 B hB hF
  have h2463 : mixedVector B (Sum.inr 2463) = Sparse.eval nodeValue2463 (mixedVector B) := by
    change mixedMoment B node2463 node2463Labels = _
    exact sound2463 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h2638 : mixedVector B (Sum.inr 2638) = Sparse.eval nodeValue2638 (mixedVector B) := by
    change mixedMoment B node2638 node2638Labels = _
    exact sound2638 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  have h4003 : mixedVector B (Sum.inr 4003) = Sparse.eval nodeValue4003 (mixedVector B) := by
    change mixedMoment B node4003 node4003Labels = _
    exact sound4003 B hB hF
  simpa only [sourceForm341, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h990, h991, h992, h1006, h1058, h2392, h2393, h2394, h2405, h2454, h2455, h2463, h2494, h2617, h2618, h2620, h2638, h2728, h2729, h2732, h2734, h2735, h2744, h2773, h2776, h3872, h3876, h3877, h3889, h4003, reducedSource286] using sourceEq341 B hB

theorem rowSound286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row286 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck286, numericCheck286, reducedZero286 B hB hF, mul_zero]

theorem reducedZero287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource287 (mixedVector B) = 0 := by
  have h1609 : mixedVector B (Sum.inr 1609) = Sparse.eval nodeValue1609 (mixedVector B) := by
    change mixedMoment B node1609 node1609Labels = _
    exact sound1609 B hB hF
  have h1610 : mixedVector B (Sum.inr 1610) = Sparse.eval nodeValue1610 (mixedVector B) := by
    change mixedMoment B node1610 node1610Labels = _
    exact sound1610 B hB hF
  have h1611 : mixedVector B (Sum.inr 1611) = Sparse.eval nodeValue1611 (mixedVector B) := by
    change mixedMoment B node1611 node1611Labels = _
    exact sound1611 B hB hF
  have h1624 : mixedVector B (Sum.inr 1624) = Sparse.eval nodeValue1624 (mixedVector B) := by
    change mixedMoment B node1624 node1624Labels = _
    exact sound1624 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h2906 : mixedVector B (Sum.inr 2906) = Sparse.eval nodeValue2906 (mixedVector B) := by
    change mixedMoment B node2906 node2906Labels = _
    exact sound2906 B hB hF
  have h2910 : mixedVector B (Sum.inr 2910) = Sparse.eval nodeValue2910 (mixedVector B) := by
    change mixedMoment B node2910 node2910Labels = _
    exact sound2910 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3347 : mixedVector B (Sum.inr 3347) = Sparse.eval nodeValue3347 (mixedVector B) := by
    change mixedMoment B node3347 node3347Labels = _
    exact sound3347 B hB hF
  have h3348 : mixedVector B (Sum.inr 3348) = Sparse.eval nodeValue3348 (mixedVector B) := by
    change mixedMoment B node3348 node3348Labels = _
    exact sound3348 B hB hF
  have h3358 : mixedVector B (Sum.inr 3358) = Sparse.eval nodeValue3358 (mixedVector B) := by
    change mixedMoment B node3358 node3358Labels = _
    exact sound3358 B hB hF
  have h3430 : mixedVector B (Sum.inr 3430) = Sparse.eval nodeValue3430 (mixedVector B) := by
    change mixedMoment B node3430 node3430Labels = _
    exact sound3430 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3993 : mixedVector B (Sum.inr 3993) = Sparse.eval nodeValue3993 (mixedVector B) := by
    change mixedMoment B node3993 node3993Labels = _
    exact sound3993 B hB hF
  simpa only [sourceForm342, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1609, h1610, h1611, h1624, h1715, h2906, h2910, h2952, h3052, h3347, h3348, h3358, h3430, h3437, h3464, h3505, h3506, h3523, h3537, h3538, h3541, h3549, h3573, h3624, h3626, h3839, h3845, h3862, h3877, h3993, reducedSource287] using sourceEq342 B hB

theorem rowSound287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row287 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck287, numericCheck287, reducedZero287 B hB hF, mul_zero]

theorem sourceRowsAt272 : MixedData.sourceRows (272 : Fin 2425) =
    MixedData.row272 := by decide +kernel

theorem sourceRowsAt273 : MixedData.sourceRows (273 : Fin 2425) =
    MixedData.row273 := by decide +kernel

theorem sourceRowsAt274 : MixedData.sourceRows (274 : Fin 2425) =
    MixedData.row274 := by decide +kernel

theorem sourceRowsAt275 : MixedData.sourceRows (275 : Fin 2425) =
    MixedData.row275 := by decide +kernel

theorem sourceRowsAt276 : MixedData.sourceRows (276 : Fin 2425) =
    MixedData.row276 := by decide +kernel

theorem sourceRowsAt277 : MixedData.sourceRows (277 : Fin 2425) =
    MixedData.row277 := by decide +kernel

theorem sourceRowsAt278 : MixedData.sourceRows (278 : Fin 2425) =
    MixedData.row278 := by decide +kernel

theorem sourceRowsAt279 : MixedData.sourceRows (279 : Fin 2425) =
    MixedData.row279 := by decide +kernel

theorem sourceRowsAt280 : MixedData.sourceRows (280 : Fin 2425) =
    MixedData.row280 := by decide +kernel

theorem sourceRowsAt281 : MixedData.sourceRows (281 : Fin 2425) =
    MixedData.row281 := by decide +kernel

theorem sourceRowsAt282 : MixedData.sourceRows (282 : Fin 2425) =
    MixedData.row282 := by decide +kernel

theorem sourceRowsAt283 : MixedData.sourceRows (283 : Fin 2425) =
    MixedData.row283 := by decide +kernel

theorem sourceRowsAt284 : MixedData.sourceRows (284 : Fin 2425) =
    MixedData.row284 := by decide +kernel

theorem sourceRowsAt285 : MixedData.sourceRows (285 : Fin 2425) =
    MixedData.row285 := by decide +kernel

theorem sourceRowsAt286 : MixedData.sourceRows (286 : Fin 2425) =
    MixedData.row286 := by decide +kernel

theorem sourceRowsAt287 : MixedData.sourceRows (287 : Fin 2425) =
    MixedData.row287 := by decide +kernel

theorem chunkSound17 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 17) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 272 ∨ k.val = 273 ∨ k.val = 274 ∨ k.val = 275 ∨ k.val = 276 ∨ k.val = 277 ∨ k.val = 278 ∨ k.val = 279 ∨ k.val = 280 ∨ k.val = 281 ∨ k.val = 282 ∨ k.val = 283 ∨ k.val = 284 ∨ k.val = 285 ∨ k.val = 286 ∨ k.val = 287 := by omega
  rcases heq with h272 | h273 | h274 | h275 | h276 | h277 | h278 | h279 | h280 | h281 | h282 | h283 | h284 | h285 | h286 | h287
  · have he : k = (272 : Fin 2425) := Fin.ext h272
    subst k
    rw [sourceRowsAt272]
    exact rowSound272 B hB hF
  · have he : k = (273 : Fin 2425) := Fin.ext h273
    subst k
    rw [sourceRowsAt273]
    exact rowSound273 B hB hF
  · have he : k = (274 : Fin 2425) := Fin.ext h274
    subst k
    rw [sourceRowsAt274]
    exact rowSound274 B hB hF
  · have he : k = (275 : Fin 2425) := Fin.ext h275
    subst k
    rw [sourceRowsAt275]
    exact rowSound275 B hB hF
  · have he : k = (276 : Fin 2425) := Fin.ext h276
    subst k
    rw [sourceRowsAt276]
    exact rowSound276 B hB hF
  · have he : k = (277 : Fin 2425) := Fin.ext h277
    subst k
    rw [sourceRowsAt277]
    exact rowSound277 B hB hF
  · have he : k = (278 : Fin 2425) := Fin.ext h278
    subst k
    rw [sourceRowsAt278]
    exact rowSound278 B hB hF
  · have he : k = (279 : Fin 2425) := Fin.ext h279
    subst k
    rw [sourceRowsAt279]
    exact rowSound279 B hB hF
  · have he : k = (280 : Fin 2425) := Fin.ext h280
    subst k
    rw [sourceRowsAt280]
    exact rowSound280 B hB hF
  · have he : k = (281 : Fin 2425) := Fin.ext h281
    subst k
    rw [sourceRowsAt281]
    exact rowSound281 B hB hF
  · have he : k = (282 : Fin 2425) := Fin.ext h282
    subst k
    rw [sourceRowsAt282]
    exact rowSound282 B hB hF
  · have he : k = (283 : Fin 2425) := Fin.ext h283
    subst k
    rw [sourceRowsAt283]
    exact rowSound283 B hB hF
  · have he : k = (284 : Fin 2425) := Fin.ext h284
    subst k
    rw [sourceRowsAt284]
    exact rowSound284 B hB hF
  · have he : k = (285 : Fin 2425) := Fin.ext h285
    subst k
    rw [sourceRowsAt285]
    exact rowSound285 B hB hF
  · have he : k = (286 : Fin 2425) := Fin.ext h286
    subst k
    rw [sourceRowsAt286]
    exact rowSound286 B hB hF
  · have he : k = (287 : Fin 2425) := Fin.ext h287
    subst k
    rw [sourceRowsAt287]
    exact rowSound287 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
