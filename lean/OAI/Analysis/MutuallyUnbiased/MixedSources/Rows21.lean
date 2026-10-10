import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources13

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource336 (mixedVector B) = 0 := by
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3493 : mixedVector B (Sum.inr 3493) = Sparse.eval nodeValue3493 (mixedVector B) := by
    change mixedMoment B node3493 node3493Labels = _
    exact sound3493 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm401, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2552, h3488, h3493, h3533, h3539, h4084, reducedSource336] using sourceEq401 B hB

theorem rowSound336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row336 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck336, numericCheck336, reducedZero336 B hB hF, mul_zero]

theorem reducedZero337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource337 (mixedVector B) = 0 := by
  have h2033 : mixedVector B (Sum.inr 2033) = Sparse.eval nodeValue2033 (mixedVector B) := by
    change mixedMoment B node2033 node2033Labels = _
    exact sound2033 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm402, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2033, h2034, h2051, h2277, h3539, h4084, reducedSource337] using sourceEq402 B hB

theorem rowSound337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row337 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck337, numericCheck337, reducedZero337 B hB hF, mul_zero]

theorem reducedZero338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource338 (mixedVector B) = 0 := by
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm403, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2277, h2738, h3539, h3625, h3632, h4084, reducedSource338] using sourceEq403 B hB

theorem rowSound338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row338 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck338, numericCheck338, reducedZero338 B hB hF, mul_zero]

theorem reducedZero339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource339 (mixedVector B) = 0 := by
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  simpa only [sourceForm405, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4619, h4621, h4627, h4871, h4899, h5170, h5176, h5302, h5306, h5308, h5443, h5455, h5456, reducedSource339] using sourceEq405 B hB

theorem rowSound339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row339 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck339, numericCheck339, reducedZero339 B hB hF, mul_zero]

theorem reducedZero340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource340 (mixedVector B) = 0 := by
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h1311 : mixedVector B (Sum.inr 1311) = Sparse.eval nodeValue1311 (mixedVector B) := by
    change mixedMoment B node1311 node1311Labels = _
    exact sound1311 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  have h3916 : mixedVector B (Sum.inr 3916) = Sparse.eval nodeValue3916 (mixedVector B) := by
    change mixedMoment B node3916 node3916Labels = _
    exact sound3916 B hB hF
  have h4019 : mixedVector B (Sum.inr 4019) = Sparse.eval nodeValue4019 (mixedVector B) := by
    change mixedMoment B node4019 node4019Labels = _
    exact sound4019 B hB hF
  simpa only [sourceForm406, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1294, h1297, h1311, h2112, h2281, h2954, h2968, h3054, h3120, h3124, h3889, h3916, h4019, reducedSource340] using sourceEq406 B hB

theorem rowSound340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row340 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck340, numericCheck340, reducedZero340 B hB hF, mul_zero]

theorem reducedZero341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource341 (mixedVector B) = 0 := by
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5455 : mixedVector B (Sum.inr 5455) = Sparse.eval nodeValue5455 (mixedVector B) := by
    change mixedMoment B node5455 node5455Labels = _
    exact sound5455 B hB hF
  have h5494 : mixedVector B (Sum.inr 5494) = Sparse.eval nodeValue5494 (mixedVector B) := by
    change mixedMoment B node5494 node5494Labels = _
    exact sound5494 B hB hF
  simpa only [sourceForm407, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4503, h4507, h4510, h5105, h5109, h5110, h5294, h5296, h5304, h5305, h5451, h5455, h5494, reducedSource341] using sourceEq407 B hB

theorem rowSound341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row341 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck341, numericCheck341, reducedZero341 B hB hF, mul_zero]

theorem reducedZero342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource342 (mixedVector B) = 0 := by
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h3987 : mixedVector B (Sum.inr 3987) = Sparse.eval nodeValue3987 (mixedVector B) := by
    change mixedMoment B node3987 node3987Labels = _
    exact sound3987 B hB hF
  have h4019 : mixedVector B (Sum.inr 4019) = Sparse.eval nodeValue4019 (mixedVector B) := by
    change mixedMoment B node4019 node4019Labels = _
    exact sound4019 B hB hF
  have h4020 : mixedVector B (Sum.inr 4020) = Sparse.eval nodeValue4020 (mixedVector B) := by
    change mixedMoment B node4020 node4020Labels = _
    exact sound4020 B hB hF
  simpa only [sourceForm408, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1087, h1091, h1094, h2515, h2519, h2522, h2768, h2770, h2782, h2783, h3987, h4019, h4020, reducedSource342] using sourceEq408 B hB

theorem rowSound342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row342 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck342, numericCheck342, reducedZero342 B hB hF, mul_zero]

theorem reducedZero343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource343 (mixedVector B) = 0 := by
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  have h5311 : mixedVector B (Sum.inr 5311) = Sparse.eval nodeValue5311 (mixedVector B) := by
    change mixedMoment B node5311 node5311Labels = _
    exact sound5311 B hB hF
  simpa only [sourceForm409, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4896, h4899, h4901, h5260, h5275, h5276, h5291, h5294, h5295, h5305, h5308, h5309, h5311, reducedSource343] using sourceEq409 B hB

theorem rowSound343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row343 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck343, numericCheck343, reducedZero343 B hB hF, mul_zero]

theorem reducedZero344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource344 (mixedVector B) = 0 := by
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h2787 : mixedVector B (Sum.inr 2787) = Sparse.eval nodeValue2787 (mixedVector B) := by
    change mixedMoment B node2787 node2787Labels = _
    exact sound2787 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h3103 : mixedVector B (Sum.inr 3103) = Sparse.eval nodeValue3103 (mixedVector B) := by
    change mixedMoment B node3103 node3103Labels = _
    exact sound3103 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  have h3125 : mixedVector B (Sum.inr 3125) = Sparse.eval nodeValue3125 (mixedVector B) := by
    change mixedMoment B node3125 node3125Labels = _
    exact sound3125 B hB hF
  simpa only [sourceForm410, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2266, h2293, h2294, h2724, h2743, h2744, h2768, h2769, h2787, h2789, h3103, h3124, h3125, reducedSource344] using sourceEq410 B hB

theorem rowSound344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row344 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck344, numericCheck344, reducedZero344 B hB hF, mul_zero]

theorem reducedZero345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource345 (mixedVector B) = 0 := by
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h2786 : mixedVector B (Sum.inr 2786) = Sparse.eval nodeValue2786 (mixedVector B) := by
    change mixedMoment B node2786 node2786Labels = _
    exact sound2786 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  have h3231 : mixedVector B (Sum.inr 3231) = Sparse.eval nodeValue3231 (mixedVector B) := by
    change mixedMoment B node3231 node3231Labels = _
    exact sound3231 B hB hF
  simpa only [sourceForm411, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2765, h2777, h2778, h2783, h2786, h2789, h3086, h3098, h3101, h3110, h3123, h3225, h3231, reducedSource345] using sourceEq411 B hB

theorem rowSound345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row345 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck345, numericCheck345, reducedZero345 B hB hF, mul_zero]

theorem reducedZero346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource346 (mixedVector B) = 0 := by
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3629 : mixedVector B (Sum.inr 3629) = Sparse.eval nodeValue3629 (mixedVector B) := by
    change mixedMoment B node3629 node3629Labels = _
    exact sound3629 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm412, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2783, h3582, h3629, h3633, h4084, reducedSource346] using sourceEq412 B hB

theorem rowSound346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row346 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck346, numericCheck346, reducedZero346 B hB hF, mul_zero]

theorem reducedZero347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource347 (mixedVector B) = 0 := by
  have h3629 : mixedVector B (Sum.inr 3629) = Sparse.eval nodeValue3629 (mixedVector B) := by
    change mixedMoment B node3629 node3629Labels = _
    exact sound3629 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h3635 : mixedVector B (Sum.inr 3635) = Sparse.eval nodeValue3635 (mixedVector B) := by
    change mixedMoment B node3635 node3635Labels = _
    exact sound3635 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm413, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3629, h3632, h3633, h3635, h4084, reducedSource347] using sourceEq413 B hB

theorem rowSound347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row347 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck347, numericCheck347, reducedZero347 B hB hF, mul_zero]

theorem reducedZero348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource348 (mixedVector B) = 0 := by
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h3635 : mixedVector B (Sum.inr 3635) = Sparse.eval nodeValue3635 (mixedVector B) := by
    change mixedMoment B node3635 node3635Labels = _
    exact sound3635 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm414, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2293, h3548, h3633, h3635, h4084, reducedSource348] using sourceEq414 B hB

theorem rowSound348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row348 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck348, numericCheck348, reducedZero348 B hB hF, mul_zero]

theorem reducedZero349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource349 (mixedVector B) = 0 := by
  have h1088 : mixedVector B (Sum.inr 1088) = Sparse.eval nodeValue1088 (mixedVector B) := by
    change mixedMoment B node1088 node1088Labels = _
    exact sound1088 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h1093 : mixedVector B (Sum.inr 1093) = Sparse.eval nodeValue1093 (mixedVector B) := by
    change mixedMoment B node1093 node1093Labels = _
    exact sound1093 B hB hF
  have h2516 : mixedVector B (Sum.inr 2516) = Sparse.eval nodeValue2516 (mixedVector B) := by
    change mixedMoment B node2516 node2516Labels = _
    exact sound2516 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2521 : mixedVector B (Sum.inr 2521) = Sparse.eval nodeValue2521 (mixedVector B) := by
    change mixedMoment B node2521 node2521Labels = _
    exact sound2521 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  simpa only [sourceForm417, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1088, h1092, h1093, h2516, h2520, h2521, h2761, h2777, h2778, h2780, h2783, h3098, h3121, reducedSource349] using sourceEq417 B hB

theorem rowSound349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row349 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck349, numericCheck349, reducedZero349 B hB hF, mul_zero]

theorem reducedZero350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource350 (mixedVector B) = 0 := by
  have h1303 : mixedVector B (Sum.inr 1303) = Sparse.eval nodeValue1303 (mixedVector B) := by
    change mixedMoment B node1303 node1303Labels = _
    exact sound1303 B hB hF
  have h1309 : mixedVector B (Sum.inr 1309) = Sparse.eval nodeValue1309 (mixedVector B) := by
    change mixedMoment B node1309 node1309Labels = _
    exact sound1309 B hB hF
  have h1310 : mixedVector B (Sum.inr 1310) = Sparse.eval nodeValue1310 (mixedVector B) := by
    change mixedMoment B node1310 node1310Labels = _
    exact sound1310 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm418, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1303, h1309, h1310, h2789, h4084, reducedSource350] using sourceEq418 B hB

theorem rowSound350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row350 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck350, numericCheck350, reducedZero350 B hB hF, mul_zero]

theorem reducedZero351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource351 (mixedVector B) = 0 := by
  have h1303 : mixedVector B (Sum.inr 1303) = Sparse.eval nodeValue1303 (mixedVector B) := by
    change mixedMoment B node1303 node1303Labels = _
    exact sound1303 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2597 : mixedVector B (Sum.inr 2597) = Sparse.eval nodeValue2597 (mixedVector B) := by
    change mixedMoment B node2597 node2597Labels = _
    exact sound2597 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm419, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1303, h2134, h2597, h2781, h2789, h4084, reducedSource351] using sourceEq419 B hB

theorem rowSound351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row351 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck351, numericCheck351, reducedZero351 B hB hF, mul_zero]

theorem sourceRowsAt336 : MixedData.sourceRows (336 : Fin 2425) =
    MixedData.row336 := by decide +kernel

theorem sourceRowsAt337 : MixedData.sourceRows (337 : Fin 2425) =
    MixedData.row337 := by decide +kernel

theorem sourceRowsAt338 : MixedData.sourceRows (338 : Fin 2425) =
    MixedData.row338 := by decide +kernel

theorem sourceRowsAt339 : MixedData.sourceRows (339 : Fin 2425) =
    MixedData.row339 := by decide +kernel

theorem sourceRowsAt340 : MixedData.sourceRows (340 : Fin 2425) =
    MixedData.row340 := by decide +kernel

theorem sourceRowsAt341 : MixedData.sourceRows (341 : Fin 2425) =
    MixedData.row341 := by decide +kernel

theorem sourceRowsAt342 : MixedData.sourceRows (342 : Fin 2425) =
    MixedData.row342 := by decide +kernel

theorem sourceRowsAt343 : MixedData.sourceRows (343 : Fin 2425) =
    MixedData.row343 := by decide +kernel

theorem sourceRowsAt344 : MixedData.sourceRows (344 : Fin 2425) =
    MixedData.row344 := by decide +kernel

theorem sourceRowsAt345 : MixedData.sourceRows (345 : Fin 2425) =
    MixedData.row345 := by decide +kernel

theorem sourceRowsAt346 : MixedData.sourceRows (346 : Fin 2425) =
    MixedData.row346 := by decide +kernel

theorem sourceRowsAt347 : MixedData.sourceRows (347 : Fin 2425) =
    MixedData.row347 := by decide +kernel

theorem sourceRowsAt348 : MixedData.sourceRows (348 : Fin 2425) =
    MixedData.row348 := by decide +kernel

theorem sourceRowsAt349 : MixedData.sourceRows (349 : Fin 2425) =
    MixedData.row349 := by decide +kernel

theorem sourceRowsAt350 : MixedData.sourceRows (350 : Fin 2425) =
    MixedData.row350 := by decide +kernel

theorem sourceRowsAt351 : MixedData.sourceRows (351 : Fin 2425) =
    MixedData.row351 := by decide +kernel

theorem chunkSound21 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 21) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 336 ∨ k.val = 337 ∨ k.val = 338 ∨ k.val = 339 ∨ k.val = 340 ∨ k.val = 341 ∨ k.val = 342 ∨ k.val = 343 ∨ k.val = 344 ∨ k.val = 345 ∨ k.val = 346 ∨ k.val = 347 ∨ k.val = 348 ∨ k.val = 349 ∨ k.val = 350 ∨ k.val = 351 := by omega
  rcases heq with h336 | h337 | h338 | h339 | h340 | h341 | h342 | h343 | h344 | h345 | h346 | h347 | h348 | h349 | h350 | h351
  · have he : k = (336 : Fin 2425) := Fin.ext h336
    subst k
    rw [sourceRowsAt336]
    exact rowSound336 B hB hF
  · have he : k = (337 : Fin 2425) := Fin.ext h337
    subst k
    rw [sourceRowsAt337]
    exact rowSound337 B hB hF
  · have he : k = (338 : Fin 2425) := Fin.ext h338
    subst k
    rw [sourceRowsAt338]
    exact rowSound338 B hB hF
  · have he : k = (339 : Fin 2425) := Fin.ext h339
    subst k
    rw [sourceRowsAt339]
    exact rowSound339 B hB hF
  · have he : k = (340 : Fin 2425) := Fin.ext h340
    subst k
    rw [sourceRowsAt340]
    exact rowSound340 B hB hF
  · have he : k = (341 : Fin 2425) := Fin.ext h341
    subst k
    rw [sourceRowsAt341]
    exact rowSound341 B hB hF
  · have he : k = (342 : Fin 2425) := Fin.ext h342
    subst k
    rw [sourceRowsAt342]
    exact rowSound342 B hB hF
  · have he : k = (343 : Fin 2425) := Fin.ext h343
    subst k
    rw [sourceRowsAt343]
    exact rowSound343 B hB hF
  · have he : k = (344 : Fin 2425) := Fin.ext h344
    subst k
    rw [sourceRowsAt344]
    exact rowSound344 B hB hF
  · have he : k = (345 : Fin 2425) := Fin.ext h345
    subst k
    rw [sourceRowsAt345]
    exact rowSound345 B hB hF
  · have he : k = (346 : Fin 2425) := Fin.ext h346
    subst k
    rw [sourceRowsAt346]
    exact rowSound346 B hB hF
  · have he : k = (347 : Fin 2425) := Fin.ext h347
    subst k
    rw [sourceRowsAt347]
    exact rowSound347 B hB hF
  · have he : k = (348 : Fin 2425) := Fin.ext h348
    subst k
    rw [sourceRowsAt348]
    exact rowSound348 B hB hF
  · have he : k = (349 : Fin 2425) := Fin.ext h349
    subst k
    rw [sourceRowsAt349]
    exact rowSound349 B hB hF
  · have he : k = (350 : Fin 2425) := Fin.ext h350
    subst k
    rw [sourceRowsAt350]
    exact rowSound350 B hB hF
  · have he : k = (351 : Fin 2425) := Fin.ext h351
    subst k
    rw [sourceRowsAt351]
    exact rowSound351 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
