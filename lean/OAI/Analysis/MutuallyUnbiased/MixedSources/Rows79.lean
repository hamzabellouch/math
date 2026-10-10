import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources46

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1264 (mixedVector B) = 0 := by
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h1095 : mixedVector B (Sum.inr 1095) = Sparse.eval nodeValue1095 (mixedVector B) := by
    change mixedMoment B node1095 node1095Labels = _
    exact sound1095 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1274 : mixedVector B (Sum.inr 1274) = Sparse.eval nodeValue1274 (mixedVector B) := by
    change mixedMoment B node1274 node1274Labels = _
    exact sound1274 B hB hF
  have h1310 : mixedVector B (Sum.inr 1310) = Sparse.eval nodeValue1310 (mixedVector B) := by
    change mixedMoment B node1310 node1310Labels = _
    exact sound1310 B hB hF
  have h1312 : mixedVector B (Sum.inr 1312) = Sparse.eval nodeValue1312 (mixedVector B) := by
    change mixedMoment B node1312 node1312Labels = _
    exact sound1312 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1454 : mixedVector B (Sum.inr 1454) = Sparse.eval nodeValue1454 (mixedVector B) := by
    change mixedMoment B node1454 node1454Labels = _
    exact sound1454 B hB hF
  have h1455 : mixedVector B (Sum.inr 1455) = Sparse.eval nodeValue1455 (mixedVector B) := by
    change mixedMoment B node1455 node1455Labels = _
    exact sound1455 B hB hF
  simpa only [sourceForm1476, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1049, h1094, h1095, h1219, h1245, h1246, h1273, h1274, h1310, h1312, h1419, h1454, h1455, reducedSource1264] using sourceEq1476 B hB

theorem rowSound1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1264 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1264, numericCheck1264, reducedZero1264 B hB hF, mul_zero]

theorem reducedZero1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1265 (mixedVector B) = 0 := by
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3311 : mixedVector B (Sum.inr 3311) = Sparse.eval nodeValue3311 (mixedVector B) := by
    change mixedMoment B node3311 node3311Labels = _
    exact sound3311 B hB hF
  have h3312 : mixedVector B (Sum.inr 3312) = Sparse.eval nodeValue3312 (mixedVector B) := by
    change mixedMoment B node3312 node3312Labels = _
    exact sound3312 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1477, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1755, h3301, h3311, h3312, h4071, reducedSource1265] using sourceEq1477 B hB

theorem rowSound1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1265 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1265, numericCheck1265, reducedZero1265 B hB hF, mul_zero]

theorem reducedZero1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1266 (mixedVector B) = 0 := by
  have h4186 : mixedVector B (Sum.inr 4186) = Sparse.eval nodeValue4186 (mixedVector B) := by
    change mixedMoment B node4186 node4186Labels = _
    exact sound4186 B hB hF
  have h4191 : mixedVector B (Sum.inr 4191) = Sparse.eval nodeValue4191 (mixedVector B) := by
    change mixedMoment B node4191 node4191Labels = _
    exact sound4191 B hB hF
  have h4554 : mixedVector B (Sum.inr 4554) = Sparse.eval nodeValue4554 (mixedVector B) := by
    change mixedMoment B node4554 node4554Labels = _
    exact sound4554 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  simpa only [sourceForm1478, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4186, h4191, h4554, h4558, h4624, h4625, h5177, h5309, reducedSource1266] using sourceEq1478 B hB

theorem rowSound1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1266 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1266, numericCheck1266, reducedZero1266 B hB hF, mul_zero]

theorem reducedZero1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1267 (mixedVector B) = 0 := by
  have h614 : mixedVector B (Sum.inr 614) = Sparse.eval nodeValue614 (mixedVector B) := by
    change mixedMoment B node614 node614Labels = _
    exact sound614 B hB hF
  have h619 : mixedVector B (Sum.inr 619) = Sparse.eval nodeValue619 (mixedVector B) := by
    change mixedMoment B node619 node619Labels = _
    exact sound619 B hB hF
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1144 : mixedVector B (Sum.inr 1144) = Sparse.eval nodeValue1144 (mixedVector B) := by
    change mixedMoment B node1144 node1144Labels = _
    exact sound1144 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h1304 : mixedVector B (Sum.inr 1304) = Sparse.eval nodeValue1304 (mixedVector B) := by
    change mixedMoment B node1304 node1304Labels = _
    exact sound1304 B hB hF
  have h2969 : mixedVector B (Sum.inr 2969) = Sparse.eval nodeValue2969 (mixedVector B) := by
    change mixedMoment B node2969 node2969Labels = _
    exact sound2969 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  simpa only [sourceForm1479, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h614, h619, h1139, h1144, h1301, h1304, h2969, h3123, reducedSource1267] using sourceEq1479 B hB

theorem rowSound1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1267 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1267, numericCheck1267, reducedZero1267 B hB hF, mul_zero]

theorem reducedZero1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1268 (mixedVector B) = 0 := by
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4593 : mixedVector B (Sum.inr 4593) = Sparse.eval nodeValue4593 (mixedVector B) := by
    change mixedMoment B node4593 node4593Labels = _
    exact sound4593 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  simpa only [sourceForm1480, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4467, h4511, h4593, h4612, h4627, reducedSource1268] using sourceEq1480 B hB

theorem rowSound1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1268 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1268, numericCheck1268, reducedZero1268 B hB hF, mul_zero]

theorem reducedZero1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1269 (mixedVector B) = 0 := by
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h1095 : mixedVector B (Sum.inr 1095) = Sparse.eval nodeValue1095 (mixedVector B) := by
    change mixedMoment B node1095 node1095Labels = _
    exact sound1095 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1274 : mixedVector B (Sum.inr 1274) = Sparse.eval nodeValue1274 (mixedVector B) := by
    change mixedMoment B node1274 node1274Labels = _
    exact sound1274 B hB hF
  have h1311 : mixedVector B (Sum.inr 1311) = Sparse.eval nodeValue1311 (mixedVector B) := by
    change mixedMoment B node1311 node1311Labels = _
    exact sound1311 B hB hF
  have h1420 : mixedVector B (Sum.inr 1420) = Sparse.eval nodeValue1420 (mixedVector B) := by
    change mixedMoment B node1420 node1420Labels = _
    exact sound1420 B hB hF
  have h1455 : mixedVector B (Sum.inr 1455) = Sparse.eval nodeValue1455 (mixedVector B) := by
    change mixedMoment B node1455 node1455Labels = _
    exact sound1455 B hB hF
  simpa only [sourceForm1481, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1050, h1095, h1220, h1246, h1274, h1311, h1420, h1455, reducedSource1269] using sourceEq1481 B hB

theorem rowSound1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1269 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1269, numericCheck1269, reducedZero1269 B hB hF, mul_zero]

theorem reducedZero1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1270 (mixedVector B) = 0 := by
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h3312 : mixedVector B (Sum.inr 3312) = Sparse.eval nodeValue3312 (mixedVector B) := by
    change mixedMoment B node3312 node3312Labels = _
    exact sound3312 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1482, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1751, h1755, h3312, h4071, reducedSource1270] using sourceEq1482 B hB

theorem rowSound1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1270 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1270, numericCheck1270, reducedZero1270 B hB hF, mul_zero]

theorem reducedZero1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1271 (mixedVector B) = 0 := by
  have h4158 : mixedVector B (Sum.inr 4158) = Sparse.eval nodeValue4158 (mixedVector B) := by
    change mixedMoment B node4158 node4158Labels = _
    exact sound4158 B hB hF
  have h4160 : mixedVector B (Sum.inr 4160) = Sparse.eval nodeValue4160 (mixedVector B) := by
    change mixedMoment B node4160 node4160Labels = _
    exact sound4160 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4188 : mixedVector B (Sum.inr 4188) = Sparse.eval nodeValue4188 (mixedVector B) := by
    change mixedMoment B node4188 node4188Labels = _
    exact sound4188 B hB hF
  have h4533 : mixedVector B (Sum.inr 4533) = Sparse.eval nodeValue4533 (mixedVector B) := by
    change mixedMoment B node4533 node4533Labels = _
    exact sound4533 B hB hF
  have h4534 : mixedVector B (Sum.inr 4534) = Sparse.eval nodeValue4534 (mixedVector B) := by
    change mixedMoment B node4534 node4534Labels = _
    exact sound4534 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4556 : mixedVector B (Sum.inr 4556) = Sparse.eval nodeValue4556 (mixedVector B) := by
    change mixedMoment B node4556 node4556Labels = _
    exact sound4556 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4603 : mixedVector B (Sum.inr 4603) = Sparse.eval nodeValue4603 (mixedVector B) := by
    change mixedMoment B node4603 node4603Labels = _
    exact sound4603 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4620 : mixedVector B (Sum.inr 4620) = Sparse.eval nodeValue4620 (mixedVector B) := by
    change mixedMoment B node4620 node4620Labels = _
    exact sound4620 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  simpa only [sourceForm1483, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4158, h4160, h4161, h4188, h4533, h4534, h4535, h4549, h4556, h4558, h4559, h4602, h4603, h4608, h4609, h4619, h4620, h5111, h5141, h5274, h5275, reducedSource1271] using sourceEq1483 B hB

theorem rowSound1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1271 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1271, numericCheck1271, reducedZero1271 B hB hF, mul_zero]

theorem reducedZero1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1272 (mixedVector B) = 0 := by
  have h586 : mixedVector B (Sum.inr 586) = Sparse.eval nodeValue586 (mixedVector B) := by
    change mixedMoment B node586 node586Labels = _
    exact sound586 B hB hF
  have h588 : mixedVector B (Sum.inr 588) = Sparse.eval nodeValue588 (mixedVector B) := by
    change mixedMoment B node588 node588Labels = _
    exact sound588 B hB hF
  have h589 : mixedVector B (Sum.inr 589) = Sparse.eval nodeValue589 (mixedVector B) := by
    change mixedMoment B node589 node589Labels = _
    exact sound589 B hB hF
  have h616 : mixedVector B (Sum.inr 616) = Sparse.eval nodeValue616 (mixedVector B) := by
    change mixedMoment B node616 node616Labels = _
    exact sound616 B hB hF
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h1120 : mixedVector B (Sum.inr 1120) = Sparse.eval nodeValue1120 (mixedVector B) := by
    change mixedMoment B node1120 node1120Labels = _
    exact sound1120 B hB hF
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h1172 : mixedVector B (Sum.inr 1172) = Sparse.eval nodeValue1172 (mixedVector B) := by
    change mixedMoment B node1172 node1172Labels = _
    exact sound1172 B hB hF
  have h1175 : mixedVector B (Sum.inr 1175) = Sparse.eval nodeValue1175 (mixedVector B) := by
    change mixedMoment B node1175 node1175Labels = _
    exact sound1175 B hB hF
  have h1176 : mixedVector B (Sum.inr 1176) = Sparse.eval nodeValue1176 (mixedVector B) := by
    change mixedMoment B node1176 node1176Labels = _
    exact sound1176 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h1267 : mixedVector B (Sum.inr 1267) = Sparse.eval nodeValue1267 (mixedVector B) := by
    change mixedMoment B node1267 node1267Labels = _
    exact sound1267 B hB hF
  have h1269 : mixedVector B (Sum.inr 1269) = Sparse.eval nodeValue1269 (mixedVector B) := by
    change mixedMoment B node1269 node1269Labels = _
    exact sound1269 B hB hF
  have h1295 : mixedVector B (Sum.inr 1295) = Sparse.eval nodeValue1295 (mixedVector B) := by
    change mixedMoment B node1295 node1295Labels = _
    exact sound1295 B hB hF
  have h1302 : mixedVector B (Sum.inr 1302) = Sparse.eval nodeValue1302 (mixedVector B) := by
    change mixedMoment B node1302 node1302Labels = _
    exact sound1302 B hB hF
  have h2943 : mixedVector B (Sum.inr 2943) = Sparse.eval nodeValue2943 (mixedVector B) := by
    change mixedMoment B node2943 node2943Labels = _
    exact sound2943 B hB hF
  have h3006 : mixedVector B (Sum.inr 3006) = Sparse.eval nodeValue3006 (mixedVector B) := by
    change mixedMoment B node3006 node3006Labels = _
    exact sound3006 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  simpa only [sourceForm1484, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h586, h588, h589, h616, h1117, h1119, h1120, h1141, h1172, h1175, h1176, h1262, h1264, h1267, h1269, h1295, h1302, h2943, h3006, h3110, h3112, reducedSource1272] using sourceEq1484 B hB

theorem rowSound1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1272 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1272, numericCheck1272, reducedZero1272 B hB hF, mul_zero]

theorem reducedZero1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1273 (mixedVector B) = 0 := by
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3271 : mixedVector B (Sum.inr 3271) = Sparse.eval nodeValue3271 (mixedVector B) := by
    change mixedMoment B node3271 node3271Labels = _
    exact sound3271 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  simpa only [sourceForm1485, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1522, h1523, h1526, h1533, h3265, h3267, h3268, h3271, h3272, h3276, h3277, h3293, h3294, h3300, h3302, h3305, h3306, h3485, h3522, h3547, h3548, reducedSource1273] using sourceEq1485 B hB

theorem rowSound1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1273 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1273, numericCheck1273, reducedZero1273 B hB hF, mul_zero]

theorem reducedZero1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1274 (mixedVector B) = 0 := by
  have h627 : mixedVector B (Sum.inr 627) = Sparse.eval nodeValue627 (mixedVector B) := by
    change mixedMoment B node627 node627Labels = _
    exact sound627 B hB hF
  have h635 : mixedVector B (Sum.inr 635) = Sparse.eval nodeValue635 (mixedVector B) := by
    change mixedMoment B node635 node635Labels = _
    exact sound635 B hB hF
  have h636 : mixedVector B (Sum.inr 636) = Sparse.eval nodeValue636 (mixedVector B) := by
    change mixedMoment B node636 node636Labels = _
    exact sound636 B hB hF
  have h642 : mixedVector B (Sum.inr 642) = Sparse.eval nodeValue642 (mixedVector B) := by
    change mixedMoment B node642 node642Labels = _
    exact sound642 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1486, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h627, h635, h636, h642, h1246, h4092, reducedSource1274] using sourceEq1486 B hB

theorem rowSound1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1274 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1274, numericCheck1274, reducedZero1274 B hB hF, mul_zero]

theorem reducedZero1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1275 (mixedVector B) = 0 := by
  have h627 : mixedVector B (Sum.inr 627) = Sparse.eval nodeValue627 (mixedVector B) := by
    change mixedMoment B node627 node627Labels = _
    exact sound627 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1487, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h627, h1134, h1149, h1236, h1237, h1246, h4092, reducedSource1275] using sourceEq1487 B hB

theorem rowSound1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1275 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1275, numericCheck1275, reducedZero1275 B hB hF, mul_zero]

theorem reducedZero1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1276 (mixedVector B) = 0 := by
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h1154 : mixedVector B (Sum.inr 1154) = Sparse.eval nodeValue1154 (mixedVector B) := by
    change mixedMoment B node1154 node1154Labels = _
    exact sound1154 B hB hF
  have h1155 : mixedVector B (Sum.inr 1155) = Sparse.eval nodeValue1155 (mixedVector B) := by
    change mixedMoment B node1155 node1155Labels = _
    exact sound1155 B hB hF
  have h1160 : mixedVector B (Sum.inr 1160) = Sparse.eval nodeValue1160 (mixedVector B) := by
    change mixedMoment B node1160 node1160Labels = _
    exact sound1160 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1488, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1149, h1154, h1155, h1160, h1246, h2561, h4092, reducedSource1276] using sourceEq1488 B hB

theorem rowSound1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1276 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1276, numericCheck1276, reducedZero1276 B hB hF, mul_zero]

theorem reducedZero1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1277 (mixedVector B) = 0 := by
  have h642 : mixedVector B (Sum.inr 642) = Sparse.eval nodeValue642 (mixedVector B) := by
    change mixedMoment B node642 node642Labels = _
    exact sound642 B hB hF
  have h1160 : mixedVector B (Sum.inr 1160) = Sparse.eval nodeValue1160 (mixedVector B) := by
    change mixedMoment B node1160 node1160Labels = _
    exact sound1160 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1295 : mixedVector B (Sum.inr 1295) = Sparse.eval nodeValue1295 (mixedVector B) := by
    change mixedMoment B node1295 node1295Labels = _
    exact sound1295 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1489, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h642, h1160, h1246, h1294, h1295, h4092, reducedSource1277] using sourceEq1489 B hB

theorem rowSound1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1277 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1277, numericCheck1277, reducedZero1277 B hB hF, mul_zero]

theorem reducedZero1278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1278 (mixedVector B) = 0 := by
  have h4145 : mixedVector B (Sum.inr 4145) = Sparse.eval nodeValue4145 (mixedVector B) := by
    change mixedMoment B node4145 node4145Labels = _
    exact sound4145 B hB hF
  have h4147 : mixedVector B (Sum.inr 4147) = Sparse.eval nodeValue4147 (mixedVector B) := by
    change mixedMoment B node4147 node4147Labels = _
    exact sound4147 B hB hF
  have h4148 : mixedVector B (Sum.inr 4148) = Sparse.eval nodeValue4148 (mixedVector B) := by
    change mixedMoment B node4148 node4148Labels = _
    exact sound4148 B hB hF
  have h4180 : mixedVector B (Sum.inr 4180) = Sparse.eval nodeValue4180 (mixedVector B) := by
    change mixedMoment B node4180 node4180Labels = _
    exact sound4180 B hB hF
  have h4518 : mixedVector B (Sum.inr 4518) = Sparse.eval nodeValue4518 (mixedVector B) := by
    change mixedMoment B node4518 node4518Labels = _
    exact sound4518 B hB hF
  have h4519 : mixedVector B (Sum.inr 4519) = Sparse.eval nodeValue4519 (mixedVector B) := by
    change mixedMoment B node4519 node4519Labels = _
    exact sound4519 B hB hF
  have h4520 : mixedVector B (Sum.inr 4520) = Sparse.eval nodeValue4520 (mixedVector B) := by
    change mixedMoment B node4520 node4520Labels = _
    exact sound4520 B hB hF
  have h4524 : mixedVector B (Sum.inr 4524) = Sparse.eval nodeValue4524 (mixedVector B) := by
    change mixedMoment B node4524 node4524Labels = _
    exact sound4524 B hB hF
  have h4525 : mixedVector B (Sum.inr 4525) = Sparse.eval nodeValue4525 (mixedVector B) := by
    change mixedMoment B node4525 node4525Labels = _
    exact sound4525 B hB hF
  have h4526 : mixedVector B (Sum.inr 4526) = Sparse.eval nodeValue4526 (mixedVector B) := by
    change mixedMoment B node4526 node4526Labels = _
    exact sound4526 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1490, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4145, h4147, h4148, h4180, h4518, h4519, h4520, h4524, h4525, h4526, h4549, h4602, h4605, h4606, h4608, h4623, h4624, h5152, h5207, h5293, h5294, reducedSource1278] using sourceEq1490 B hB

theorem rowSound1278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1278 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1278, numericCheck1278, reducedZero1278 B hB hF, mul_zero]

theorem reducedZero1279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1279 (mixedVector B) = 0 := by
  have h573 : mixedVector B (Sum.inr 573) = Sparse.eval nodeValue573 (mixedVector B) := by
    change mixedMoment B node573 node573Labels = _
    exact sound573 B hB hF
  have h575 : mixedVector B (Sum.inr 575) = Sparse.eval nodeValue575 (mixedVector B) := by
    change mixedMoment B node575 node575Labels = _
    exact sound575 B hB hF
  have h576 : mixedVector B (Sum.inr 576) = Sparse.eval nodeValue576 (mixedVector B) := by
    change mixedMoment B node576 node576Labels = _
    exact sound576 B hB hF
  have h608 : mixedVector B (Sum.inr 608) = Sparse.eval nodeValue608 (mixedVector B) := by
    change mixedMoment B node608 node608Labels = _
    exact sound608 B hB hF
  have h1102 : mixedVector B (Sum.inr 1102) = Sparse.eval nodeValue1102 (mixedVector B) := by
    change mixedMoment B node1102 node1102Labels = _
    exact sound1102 B hB hF
  have h1103 : mixedVector B (Sum.inr 1103) = Sparse.eval nodeValue1103 (mixedVector B) := by
    change mixedMoment B node1103 node1103Labels = _
    exact sound1103 B hB hF
  have h1104 : mixedVector B (Sum.inr 1104) = Sparse.eval nodeValue1104 (mixedVector B) := by
    change mixedMoment B node1104 node1104Labels = _
    exact sound1104 B hB hF
  have h1108 : mixedVector B (Sum.inr 1108) = Sparse.eval nodeValue1108 (mixedVector B) := by
    change mixedMoment B node1108 node1108Labels = _
    exact sound1108 B hB hF
  have h1109 : mixedVector B (Sum.inr 1109) = Sparse.eval nodeValue1109 (mixedVector B) := by
    change mixedMoment B node1109 node1109Labels = _
    exact sound1109 B hB hF
  have h1110 : mixedVector B (Sum.inr 1110) = Sparse.eval nodeValue1110 (mixedVector B) := by
    change mixedMoment B node1110 node1110Labels = _
    exact sound1110 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1300 : mixedVector B (Sum.inr 1300) = Sparse.eval nodeValue1300 (mixedVector B) := by
    change mixedMoment B node1300 node1300Labels = _
    exact sound1300 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  simpa only [sourceForm1491, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h573, h575, h576, h608, h1102, h1103, h1104, h1108, h1109, h1110, h1134, h1236, h1239, h1240, h1242, h1300, h1301, h2889, h2931, h3101, h3102, reducedSource1279] using sourceEq1491 B hB

theorem rowSound1279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1279 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1279, numericCheck1279, reducedZero1279 B hB hF, mul_zero]

theorem sourceRowsAt1264 : MixedData.sourceRows (1264 : Fin 2425) =
    MixedData.row1264 := by decide +kernel

theorem sourceRowsAt1265 : MixedData.sourceRows (1265 : Fin 2425) =
    MixedData.row1265 := by decide +kernel

theorem sourceRowsAt1266 : MixedData.sourceRows (1266 : Fin 2425) =
    MixedData.row1266 := by decide +kernel

theorem sourceRowsAt1267 : MixedData.sourceRows (1267 : Fin 2425) =
    MixedData.row1267 := by decide +kernel

theorem sourceRowsAt1268 : MixedData.sourceRows (1268 : Fin 2425) =
    MixedData.row1268 := by decide +kernel

theorem sourceRowsAt1269 : MixedData.sourceRows (1269 : Fin 2425) =
    MixedData.row1269 := by decide +kernel

theorem sourceRowsAt1270 : MixedData.sourceRows (1270 : Fin 2425) =
    MixedData.row1270 := by decide +kernel

theorem sourceRowsAt1271 : MixedData.sourceRows (1271 : Fin 2425) =
    MixedData.row1271 := by decide +kernel

theorem sourceRowsAt1272 : MixedData.sourceRows (1272 : Fin 2425) =
    MixedData.row1272 := by decide +kernel

theorem sourceRowsAt1273 : MixedData.sourceRows (1273 : Fin 2425) =
    MixedData.row1273 := by decide +kernel

theorem sourceRowsAt1274 : MixedData.sourceRows (1274 : Fin 2425) =
    MixedData.row1274 := by decide +kernel

theorem sourceRowsAt1275 : MixedData.sourceRows (1275 : Fin 2425) =
    MixedData.row1275 := by decide +kernel

theorem sourceRowsAt1276 : MixedData.sourceRows (1276 : Fin 2425) =
    MixedData.row1276 := by decide +kernel

theorem sourceRowsAt1277 : MixedData.sourceRows (1277 : Fin 2425) =
    MixedData.row1277 := by decide +kernel

theorem sourceRowsAt1278 : MixedData.sourceRows (1278 : Fin 2425) =
    MixedData.row1278 := by decide +kernel

theorem sourceRowsAt1279 : MixedData.sourceRows (1279 : Fin 2425) =
    MixedData.row1279 := by decide +kernel

theorem chunkSound79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 79) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1264 ∨ k.val = 1265 ∨ k.val = 1266 ∨ k.val = 1267 ∨ k.val = 1268 ∨ k.val = 1269 ∨ k.val = 1270 ∨ k.val = 1271 ∨ k.val = 1272 ∨ k.val = 1273 ∨ k.val = 1274 ∨ k.val = 1275 ∨ k.val = 1276 ∨ k.val = 1277 ∨ k.val = 1278 ∨ k.val = 1279 := by omega
  rcases heq with h1264 | h1265 | h1266 | h1267 | h1268 | h1269 | h1270 | h1271 | h1272 | h1273 | h1274 | h1275 | h1276 | h1277 | h1278 | h1279
  · have he : k = (1264 : Fin 2425) := Fin.ext h1264
    subst k
    rw [sourceRowsAt1264]
    exact rowSound1264 B hB hF
  · have he : k = (1265 : Fin 2425) := Fin.ext h1265
    subst k
    rw [sourceRowsAt1265]
    exact rowSound1265 B hB hF
  · have he : k = (1266 : Fin 2425) := Fin.ext h1266
    subst k
    rw [sourceRowsAt1266]
    exact rowSound1266 B hB hF
  · have he : k = (1267 : Fin 2425) := Fin.ext h1267
    subst k
    rw [sourceRowsAt1267]
    exact rowSound1267 B hB hF
  · have he : k = (1268 : Fin 2425) := Fin.ext h1268
    subst k
    rw [sourceRowsAt1268]
    exact rowSound1268 B hB hF
  · have he : k = (1269 : Fin 2425) := Fin.ext h1269
    subst k
    rw [sourceRowsAt1269]
    exact rowSound1269 B hB hF
  · have he : k = (1270 : Fin 2425) := Fin.ext h1270
    subst k
    rw [sourceRowsAt1270]
    exact rowSound1270 B hB hF
  · have he : k = (1271 : Fin 2425) := Fin.ext h1271
    subst k
    rw [sourceRowsAt1271]
    exact rowSound1271 B hB hF
  · have he : k = (1272 : Fin 2425) := Fin.ext h1272
    subst k
    rw [sourceRowsAt1272]
    exact rowSound1272 B hB hF
  · have he : k = (1273 : Fin 2425) := Fin.ext h1273
    subst k
    rw [sourceRowsAt1273]
    exact rowSound1273 B hB hF
  · have he : k = (1274 : Fin 2425) := Fin.ext h1274
    subst k
    rw [sourceRowsAt1274]
    exact rowSound1274 B hB hF
  · have he : k = (1275 : Fin 2425) := Fin.ext h1275
    subst k
    rw [sourceRowsAt1275]
    exact rowSound1275 B hB hF
  · have he : k = (1276 : Fin 2425) := Fin.ext h1276
    subst k
    rw [sourceRowsAt1276]
    exact rowSound1276 B hB hF
  · have he : k = (1277 : Fin 2425) := Fin.ext h1277
    subst k
    rw [sourceRowsAt1277]
    exact rowSound1277 B hB hF
  · have he : k = (1278 : Fin 2425) := Fin.ext h1278
    subst k
    rw [sourceRowsAt1278]
    exact rowSound1278 B hB hF
  · have he : k = (1279 : Fin 2425) := Fin.ext h1279
    subst k
    rw [sourceRowsAt1279]
    exact rowSound1279 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
