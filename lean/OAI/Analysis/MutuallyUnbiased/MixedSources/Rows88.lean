import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources51

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1408 (mixedVector B) = 0 := by
  have h1288 : mixedVector B (Sum.inr 1288) = Sparse.eval nodeValue1288 (mixedVector B) := by
    change mixedMoment B node1288 node1288Labels = _
    exact sound1288 B hB hF
  have h2585 : mixedVector B (Sum.inr 2585) = Sparse.eval nodeValue2585 (mixedVector B) := by
    change mixedMoment B node2585 node2585Labels = _
    exact sound2585 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h2771 : mixedVector B (Sum.inr 2771) = Sparse.eval nodeValue2771 (mixedVector B) := by
    change mixedMoment B node2771 node2771Labels = _
    exact sound2771 B hB hF
  have h2779 : mixedVector B (Sum.inr 2779) = Sparse.eval nodeValue2779 (mixedVector B) := by
    change mixedMoment B node2779 node2779Labels = _
    exact sound2779 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1647, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1288, h2585, h2686, h2771, h2779, h4089, reducedSource1408] using sourceEq1647 B hB

theorem rowSound1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1408 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1408, numericCheck1408, reducedZero1408 B hB hF, mul_zero]

theorem reducedZero1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1409 (mixedVector B) = 0 := by
  have h4182 : mixedVector B (Sum.inr 4182) = Sparse.eval nodeValue4182 (mixedVector B) := by
    change mixedMoment B node4182 node4182Labels = _
    exact sound4182 B hB hF
  have h4183 : mixedVector B (Sum.inr 4183) = Sparse.eval nodeValue4183 (mixedVector B) := by
    change mixedMoment B node4183 node4183Labels = _
    exact sound4183 B hB hF
  have h4185 : mixedVector B (Sum.inr 4185) = Sparse.eval nodeValue4185 (mixedVector B) := by
    change mixedMoment B node4185 node4185Labels = _
    exact sound4185 B hB hF
  have h4550 : mixedVector B (Sum.inr 4550) = Sparse.eval nodeValue4550 (mixedVector B) := by
    change mixedMoment B node4550 node4550Labels = _
    exact sound4550 B hB hF
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4553 : mixedVector B (Sum.inr 4553) = Sparse.eval nodeValue4553 (mixedVector B) := by
    change mixedMoment B node4553 node4553Labels = _
    exact sound4553 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  simpa only [sourceForm1648, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4182, h4183, h4185, h4550, h4551, h4553, h4618, h4619, h4623, h4625, h4627, h5168, h5306, h5308, reducedSource1409] using sourceEq1648 B hB

theorem rowSound1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1409 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1409, numericCheck1409, reducedZero1409 B hB hF, mul_zero]

theorem reducedZero1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1410 (mixedVector B) = 0 := by
  have h610 : mixedVector B (Sum.inr 610) = Sparse.eval nodeValue610 (mixedVector B) := by
    change mixedMoment B node610 node610Labels = _
    exact sound610 B hB hF
  have h611 : mixedVector B (Sum.inr 611) = Sparse.eval nodeValue611 (mixedVector B) := by
    change mixedMoment B node611 node611Labels = _
    exact sound611 B hB hF
  have h613 : mixedVector B (Sum.inr 613) = Sparse.eval nodeValue613 (mixedVector B) := by
    change mixedMoment B node613 node613Labels = _
    exact sound613 B hB hF
  have h1135 : mixedVector B (Sum.inr 1135) = Sparse.eval nodeValue1135 (mixedVector B) := by
    change mixedMoment B node1135 node1135Labels = _
    exact sound1135 B hB hF
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h1311 : mixedVector B (Sum.inr 1311) = Sparse.eval nodeValue1311 (mixedVector B) := by
    change mixedMoment B node1311 node1311Labels = _
    exact sound1311 B hB hF
  have h2963 : mixedVector B (Sum.inr 2963) = Sparse.eval nodeValue2963 (mixedVector B) := by
    change mixedMoment B node2963 node2963Labels = _
    exact sound2963 B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  simpa only [sourceForm1649, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h610, h611, h613, h1135, h1136, h1138, h1293, h1294, h1305, h1307, h1311, h2963, h3120, h3124, reducedSource1410] using sourceEq1649 B hB

theorem rowSound1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1410 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1410, numericCheck1410, reducedZero1410 B hB hF, mul_zero]

theorem reducedZero1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1411 (mixedVector B) = 0 := by
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4174 : mixedVector B (Sum.inr 4174) = Sparse.eval nodeValue4174 (mixedVector B) := by
    change mixedMoment B node4174 node4174Labels = _
    exact sound4174 B hB hF
  have h4180 : mixedVector B (Sum.inr 4180) = Sparse.eval nodeValue4180 (mixedVector B) := by
    change mixedMoment B node4180 node4180Labels = _
    exact sound4180 B hB hF
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  simpa only [sourceForm1650, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4172, h4174, h4180, h4541, h4543, h4549, h4602, h4605, h4612, h4622, h4624, h5172, h5294, h5307, reducedSource1411] using sourceEq1650 B hB

theorem rowSound1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1411 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1411, numericCheck1411, reducedZero1411 B hB hF, mul_zero]

theorem reducedZero1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1412 (mixedVector B) = 0 := by
  have h600 : mixedVector B (Sum.inr 600) = Sparse.eval nodeValue600 (mixedVector B) := by
    change mixedMoment B node600 node600Labels = _
    exact sound600 B hB hF
  have h602 : mixedVector B (Sum.inr 602) = Sparse.eval nodeValue602 (mixedVector B) := by
    change mixedMoment B node602 node602Labels = _
    exact sound602 B hB hF
  have h608 : mixedVector B (Sum.inr 608) = Sparse.eval nodeValue608 (mixedVector B) := by
    change mixedMoment B node608 node608Labels = _
    exact sound608 B hB hF
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h2959 : mixedVector B (Sum.inr 2959) = Sparse.eval nodeValue2959 (mixedVector B) := by
    change mixedMoment B node2959 node2959Labels = _
    exact sound2959 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3122 : mixedVector B (Sum.inr 3122) = Sparse.eval nodeValue3122 (mixedVector B) := by
    change mixedMoment B node3122 node3122Labels = _
    exact sound3122 B hB hF
  simpa only [sourceForm1651, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h600, h602, h608, h1126, h1128, h1134, h1236, h1239, h1246, h1299, h1301, h2959, h3101, h3122, reducedSource1412] using sourceEq1651 B hB

theorem rowSound1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1412 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1412, numericCheck1412, reducedZero1412 B hB hF, mul_zero]

theorem reducedZero1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1413 (mixedVector B) = 0 := by
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4600 : mixedVector B (Sum.inr 4600) = Sparse.eval nodeValue4600 (mixedVector B) := by
    change mixedMoment B node4600 node4600Labels = _
    exact sound4600 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  simpa only [sourceForm1652, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4457, h4461, h4496, h4498, h4502, h4503, h4589, h4600, h4602, h4606, h4607, h4617, h4619, h4624, reducedSource1413] using sourceEq1652 B hB

theorem rowSound1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1413 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1413, numericCheck1413, reducedZero1413 B hB hF, mul_zero]

theorem reducedZero1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1414 (mixedVector B) = 0 := by
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1267 : mixedVector B (Sum.inr 1267) = Sparse.eval nodeValue1267 (mixedVector B) := by
    change mixedMoment B node1267 node1267Labels = _
    exact sound1267 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h1302 : mixedVector B (Sum.inr 1302) = Sparse.eval nodeValue1302 (mixedVector B) := by
    change mixedMoment B node1302 node1302Labels = _
    exact sound1302 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h1448 : mixedVector B (Sum.inr 1448) = Sparse.eval nodeValue1448 (mixedVector B) := by
    change mixedMoment B node1448 node1448Labels = _
    exact sound1448 B hB hF
  have h1451 : mixedVector B (Sum.inr 1451) = Sparse.eval nodeValue1451 (mixedVector B) := by
    change mixedMoment B node1451 node1451Labels = _
    exact sound1451 B hB hF
  simpa only [sourceForm1653, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1044, h1086, h1087, h1216, h1240, h1241, h1267, h1270, h1301, h1302, h1306, h1414, h1448, h1451, reducedSource1414] using sourceEq1653 B hB

theorem rowSound1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1414 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1414, numericCheck1414, reducedZero1414 B hB hF, mul_zero]

theorem reducedZero1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1415 (mixedVector B) = 0 := by
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1654, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1737, h1739, h1753, h3308, h4069, reducedSource1415] using sourceEq1654 B hB

theorem rowSound1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1415 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1415, numericCheck1415, reducedZero1415 B hB hF, mul_zero]

theorem reducedZero1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1416 (mixedVector B) = 0 := by
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h3309 : mixedVector B (Sum.inr 3309) = Sparse.eval nodeValue3309 (mixedVector B) := by
    change mixedMoment B node3309 node3309Labels = _
    exact sound3309 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1655, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1727, h3293, h3305, h3308, h3309, h4069, reducedSource1416] using sourceEq1655 B hB

theorem rowSound1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1416 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1416, numericCheck1416, reducedZero1416 B hB hF, mul_zero]

theorem reducedZero1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1417 (mixedVector B) = 0 := by
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4180 : mixedVector B (Sum.inr 4180) = Sparse.eval nodeValue4180 (mixedVector B) := by
    change mixedMoment B node4180 node4180Labels = _
    exact sound4180 B hB hF
  have h4186 : mixedVector B (Sum.inr 4186) = Sparse.eval nodeValue4186 (mixedVector B) := by
    change mixedMoment B node4186 node4186Labels = _
    exact sound4186 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4554 : mixedVector B (Sum.inr 4554) = Sparse.eval nodeValue4554 (mixedVector B) := by
    change mixedMoment B node4554 node4554Labels = _
    exact sound4554 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  simpa only [sourceForm1656, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4175, h4177, h4180, h4186, h4544, h4546, h4549, h4554, h4606, h4608, h4612, h4622, h4623, h4624, h4625, h4628, h5169, h5293, h5307, h5309, reducedSource1417] using sourceEq1656 B hB

theorem rowSound1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1417 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1417, numericCheck1417, reducedZero1417 B hB hF, mul_zero]

theorem reducedZero1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1418 (mixedVector B) = 0 := by
  have h603 : mixedVector B (Sum.inr 603) = Sparse.eval nodeValue603 (mixedVector B) := by
    change mixedMoment B node603 node603Labels = _
    exact sound603 B hB hF
  have h605 : mixedVector B (Sum.inr 605) = Sparse.eval nodeValue605 (mixedVector B) := by
    change mixedMoment B node605 node605Labels = _
    exact sound605 B hB hF
  have h608 : mixedVector B (Sum.inr 608) = Sparse.eval nodeValue608 (mixedVector B) := by
    change mixedMoment B node608 node608Labels = _
    exact sound608 B hB hF
  have h614 : mixedVector B (Sum.inr 614) = Sparse.eval nodeValue614 (mixedVector B) := by
    change mixedMoment B node614 node614Labels = _
    exact sound614 B hB hF
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299 B hB hF
  have h1300 : mixedVector B (Sum.inr 1300) = Sparse.eval nodeValue1300 (mixedVector B) := by
    change mixedMoment B node1300 node1300Labels = _
    exact sound1300 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h1304 : mixedVector B (Sum.inr 1304) = Sparse.eval nodeValue1304 (mixedVector B) := by
    change mixedMoment B node1304 node1304Labels = _
    exact sound1304 B hB hF
  have h1312 : mixedVector B (Sum.inr 1312) = Sparse.eval nodeValue1312 (mixedVector B) := by
    change mixedMoment B node1312 node1312Labels = _
    exact sound1312 B hB hF
  have h2960 : mixedVector B (Sum.inr 2960) = Sparse.eval nodeValue2960 (mixedVector B) := by
    change mixedMoment B node2960 node2960Labels = _
    exact sound2960 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  have h3122 : mixedVector B (Sum.inr 3122) = Sparse.eval nodeValue3122 (mixedVector B) := by
    change mixedMoment B node3122 node3122Labels = _
    exact sound3122 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  simpa only [sourceForm1657, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h603, h605, h608, h614, h1129, h1131, h1134, h1139, h1240, h1242, h1246, h1299, h1300, h1301, h1304, h1312, h2960, h3102, h3122, h3123, reducedSource1418] using sourceEq1657 B hB

theorem rowSound1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1418 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1418, numericCheck1418, reducedZero1418 B hB hF, mul_zero]

theorem reducedZero1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1419 (mixedVector B) = 0 := by
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4590 : mixedVector B (Sum.inr 4590) = Sparse.eval nodeValue4590 (mixedVector B) := by
    change mixedMoment B node4590 node4590Labels = _
    exact sound4590 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4603 : mixedVector B (Sum.inr 4603) = Sparse.eval nodeValue4603 (mixedVector B) := by
    change mixedMoment B node4603 node4603Labels = _
    exact sound4603 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4620 : mixedVector B (Sum.inr 4620) = Sparse.eval nodeValue4620 (mixedVector B) := by
    change mixedMoment B node4620 node4620Labels = _
    exact sound4620 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  simpa only [sourceForm1658, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4458, h4498, h4499, h4502, h4590, h4602, h4603, h4606, h4619, h4620, h4623, h4624, reducedSource1419] using sourceEq1658 B hB

theorem rowSound1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1419 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1419, numericCheck1419, reducedZero1419 B hB hF, mul_zero]

theorem reducedZero1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1420 (mixedVector B) = 0 := by
  have h4165 : mixedVector B (Sum.inr 4165) = Sparse.eval nodeValue4165 (mixedVector B) := by
    change mixedMoment B node4165 node4165Labels = _
    exact sound4165 B hB hF
  have h4166 : mixedVector B (Sum.inr 4166) = Sparse.eval nodeValue4166 (mixedVector B) := by
    change mixedMoment B node4166 node4166Labels = _
    exact sound4166 B hB hF
  have h4167 : mixedVector B (Sum.inr 4167) = Sparse.eval nodeValue4167 (mixedVector B) := by
    change mixedMoment B node4167 node4167Labels = _
    exact sound4167 B hB hF
  have h4185 : mixedVector B (Sum.inr 4185) = Sparse.eval nodeValue4185 (mixedVector B) := by
    change mixedMoment B node4185 node4185Labels = _
    exact sound4185 B hB hF
  have h4537 : mixedVector B (Sum.inr 4537) = Sparse.eval nodeValue4537 (mixedVector B) := by
    change mixedMoment B node4537 node4537Labels = _
    exact sound4537 B hB hF
  have h4538 : mixedVector B (Sum.inr 4538) = Sparse.eval nodeValue4538 (mixedVector B) := by
    change mixedMoment B node4538 node4538Labels = _
    exact sound4538 B hB hF
  have h4539 : mixedVector B (Sum.inr 4539) = Sparse.eval nodeValue4539 (mixedVector B) := by
    change mixedMoment B node4539 node4539Labels = _
    exact sound4539 B hB hF
  have h4553 : mixedVector B (Sum.inr 4553) = Sparse.eval nodeValue4553 (mixedVector B) := by
    change mixedMoment B node4553 node4553Labels = _
    exact sound4553 B hB hF
  have h4570 : mixedVector B (Sum.inr 4570) = Sparse.eval nodeValue4570 (mixedVector B) := by
    change mixedMoment B node4570 node4570Labels = _
    exact sound4570 B hB hF
  have h4572 : mixedVector B (Sum.inr 4572) = Sparse.eval nodeValue4572 (mixedVector B) := by
    change mixedMoment B node4572 node4572Labels = _
    exact sound4572 B hB hF
  have h4575 : mixedVector B (Sum.inr 4575) = Sparse.eval nodeValue4575 (mixedVector B) := by
    change mixedMoment B node4575 node4575Labels = _
    exact sound4575 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  simpa only [sourceForm1659, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4165, h4166, h4167, h4185, h4537, h4538, h4539, h4553, h4570, h4572, h4575, h4618, h4619, h4621, h4623, h4627, h5170, h5302, h5306, h5310, reducedSource1420] using sourceEq1659 B hB

theorem rowSound1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1420 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1420, numericCheck1420, reducedZero1420 B hB hF, mul_zero]

theorem reducedZero1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1421 (mixedVector B) = 0 := by
  have h593 : mixedVector B (Sum.inr 593) = Sparse.eval nodeValue593 (mixedVector B) := by
    change mixedMoment B node593 node593Labels = _
    exact sound593 B hB hF
  have h594 : mixedVector B (Sum.inr 594) = Sparse.eval nodeValue594 (mixedVector B) := by
    change mixedMoment B node594 node594Labels = _
    exact sound594 B hB hF
  have h595 : mixedVector B (Sum.inr 595) = Sparse.eval nodeValue595 (mixedVector B) := by
    change mixedMoment B node595 node595Labels = _
    exact sound595 B hB hF
  have h613 : mixedVector B (Sum.inr 613) = Sparse.eval nodeValue613 (mixedVector B) := by
    change mixedMoment B node613 node613Labels = _
    exact sound613 B hB hF
  have h1122 : mixedVector B (Sum.inr 1122) = Sparse.eval nodeValue1122 (mixedVector B) := by
    change mixedMoment B node1122 node1122Labels = _
    exact sound1122 B hB hF
  have h1123 : mixedVector B (Sum.inr 1123) = Sparse.eval nodeValue1123 (mixedVector B) := by
    change mixedMoment B node1123 node1123Labels = _
    exact sound1123 B hB hF
  have h1124 : mixedVector B (Sum.inr 1124) = Sparse.eval nodeValue1124 (mixedVector B) := by
    change mixedMoment B node1124 node1124Labels = _
    exact sound1124 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1193 : mixedVector B (Sum.inr 1193) = Sparse.eval nodeValue1193 (mixedVector B) := by
    change mixedMoment B node1193 node1193Labels = _
    exact sound1193 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h1311 : mixedVector B (Sum.inr 1311) = Sparse.eval nodeValue1311 (mixedVector B) := by
    change mixedMoment B node1311 node1311Labels = _
    exact sound1311 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  simpa only [sourceForm1660, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h593, h594, h595, h613, h1122, h1123, h1124, h1138, h1188, h1190, h1193, h1293, h1294, h1297, h1305, h1311, h2954, h3054, h3120, h3121, reducedSource1421] using sourceEq1660 B hB

theorem rowSound1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1421 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1421, numericCheck1421, reducedZero1421 B hB hF, mul_zero]

theorem reducedZero1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1422 (mixedVector B) = 0 := by
  have h4176 : mixedVector B (Sum.inr 4176) = Sparse.eval nodeValue4176 (mixedVector B) := by
    change mixedMoment B node4176 node4176Labels = _
    exact sound4176 B hB hF
  have h4178 : mixedVector B (Sum.inr 4178) = Sparse.eval nodeValue4178 (mixedVector B) := by
    change mixedMoment B node4178 node4178Labels = _
    exact sound4178 B hB hF
  have h4179 : mixedVector B (Sum.inr 4179) = Sparse.eval nodeValue4179 (mixedVector B) := by
    change mixedMoment B node4179 node4179Labels = _
    exact sound4179 B hB hF
  have h4188 : mixedVector B (Sum.inr 4188) = Sparse.eval nodeValue4188 (mixedVector B) := by
    change mixedMoment B node4188 node4188Labels = _
    exact sound4188 B hB hF
  have h4545 : mixedVector B (Sum.inr 4545) = Sparse.eval nodeValue4545 (mixedVector B) := by
    change mixedMoment B node4545 node4545Labels = _
    exact sound4545 B hB hF
  have h4547 : mixedVector B (Sum.inr 4547) = Sparse.eval nodeValue4547 (mixedVector B) := by
    change mixedMoment B node4547 node4547Labels = _
    exact sound4547 B hB hF
  have h4548 : mixedVector B (Sum.inr 4548) = Sparse.eval nodeValue4548 (mixedVector B) := by
    change mixedMoment B node4548 node4548Labels = _
    exact sound4548 B hB hF
  have h4556 : mixedVector B (Sum.inr 4556) = Sparse.eval nodeValue4556 (mixedVector B) := by
    change mixedMoment B node4556 node4556Labels = _
    exact sound4556 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4616 : mixedVector B (Sum.inr 4616) = Sparse.eval nodeValue4616 (mixedVector B) := by
    change mixedMoment B node4616 node4616Labels = _
    exact sound4616 B hB hF
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4620 : mixedVector B (Sum.inr 4620) = Sparse.eval nodeValue4620 (mixedVector B) := by
    change mixedMoment B node4620 node4620Labels = _
    exact sound4620 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  simpa only [sourceForm1661, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4176, h4178, h4179, h4188, h4545, h4547, h4548, h4556, h4602, h4607, h4608, h4609, h4611, h4612, h4616, h4617, h4620, h5163, h5274, h5291, h5304, reducedSource1422] using sourceEq1661 B hB

theorem rowSound1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1422 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1422, numericCheck1422, reducedZero1422 B hB hF, mul_zero]

theorem reducedZero1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1423 (mixedVector B) = 0 := by
  have h604 : mixedVector B (Sum.inr 604) = Sparse.eval nodeValue604 (mixedVector B) := by
    change mixedMoment B node604 node604Labels = _
    exact sound604 B hB hF
  have h606 : mixedVector B (Sum.inr 606) = Sparse.eval nodeValue606 (mixedVector B) := by
    change mixedMoment B node606 node606Labels = _
    exact sound606 B hB hF
  have h607 : mixedVector B (Sum.inr 607) = Sparse.eval nodeValue607 (mixedVector B) := by
    change mixedMoment B node607 node607Labels = _
    exact sound607 B hB hF
  have h616 : mixedVector B (Sum.inr 616) = Sparse.eval nodeValue616 (mixedVector B) := by
    change mixedMoment B node616 node616Labels = _
    exact sound616 B hB hF
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h1133 : mixedVector B (Sum.inr 1133) = Sparse.eval nodeValue1133 (mixedVector B) := by
    change mixedMoment B node1133 node1133Labels = _
    exact sound1133 B hB hF
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h1267 : mixedVector B (Sum.inr 1267) = Sparse.eval nodeValue1267 (mixedVector B) := by
    change mixedMoment B node1267 node1267Labels = _
    exact sound1267 B hB hF
  have h1269 : mixedVector B (Sum.inr 1269) = Sparse.eval nodeValue1269 (mixedVector B) := by
    change mixedMoment B node1269 node1269Labels = _
    exact sound1269 B hB hF
  have h1274 : mixedVector B (Sum.inr 1274) = Sparse.eval nodeValue1274 (mixedVector B) := by
    change mixedMoment B node1274 node1274Labels = _
    exact sound1274 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h1292 : mixedVector B (Sum.inr 1292) = Sparse.eval nodeValue1292 (mixedVector B) := by
    change mixedMoment B node1292 node1292Labels = _
    exact sound1292 B hB hF
  have h1295 : mixedVector B (Sum.inr 1295) = Sparse.eval nodeValue1295 (mixedVector B) := by
    change mixedMoment B node1295 node1295Labels = _
    exact sound1295 B hB hF
  have h2961 : mixedVector B (Sum.inr 2961) = Sparse.eval nodeValue2961 (mixedVector B) := by
    change mixedMoment B node2961 node2961Labels = _
    exact sound2961 B hB hF
  have h3103 : mixedVector B (Sum.inr 3103) = Sparse.eval nodeValue3103 (mixedVector B) := by
    change mixedMoment B node3103 node3103Labels = _
    exact sound3103 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  simpa only [sourceForm1662, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h604, h606, h607, h616, h1130, h1132, h1133, h1141, h1241, h1243, h1245, h1267, h1269, h1274, h1291, h1292, h1295, h2961, h3103, h3112, h3119, reducedSource1423] using sourceEq1662 B hB

theorem rowSound1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1423 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1423, numericCheck1423, reducedZero1423 B hB hF, mul_zero]

theorem sourceRowsAt1408 : MixedData.sourceRows (1408 : Fin 2425) =
    MixedData.row1408 := by decide +kernel

theorem sourceRowsAt1409 : MixedData.sourceRows (1409 : Fin 2425) =
    MixedData.row1409 := by decide +kernel

theorem sourceRowsAt1410 : MixedData.sourceRows (1410 : Fin 2425) =
    MixedData.row1410 := by decide +kernel

theorem sourceRowsAt1411 : MixedData.sourceRows (1411 : Fin 2425) =
    MixedData.row1411 := by decide +kernel

theorem sourceRowsAt1412 : MixedData.sourceRows (1412 : Fin 2425) =
    MixedData.row1412 := by decide +kernel

theorem sourceRowsAt1413 : MixedData.sourceRows (1413 : Fin 2425) =
    MixedData.row1413 := by decide +kernel

theorem sourceRowsAt1414 : MixedData.sourceRows (1414 : Fin 2425) =
    MixedData.row1414 := by decide +kernel

theorem sourceRowsAt1415 : MixedData.sourceRows (1415 : Fin 2425) =
    MixedData.row1415 := by decide +kernel

theorem sourceRowsAt1416 : MixedData.sourceRows (1416 : Fin 2425) =
    MixedData.row1416 := by decide +kernel

theorem sourceRowsAt1417 : MixedData.sourceRows (1417 : Fin 2425) =
    MixedData.row1417 := by decide +kernel

theorem sourceRowsAt1418 : MixedData.sourceRows (1418 : Fin 2425) =
    MixedData.row1418 := by decide +kernel

theorem sourceRowsAt1419 : MixedData.sourceRows (1419 : Fin 2425) =
    MixedData.row1419 := by decide +kernel

theorem sourceRowsAt1420 : MixedData.sourceRows (1420 : Fin 2425) =
    MixedData.row1420 := by decide +kernel

theorem sourceRowsAt1421 : MixedData.sourceRows (1421 : Fin 2425) =
    MixedData.row1421 := by decide +kernel

theorem sourceRowsAt1422 : MixedData.sourceRows (1422 : Fin 2425) =
    MixedData.row1422 := by decide +kernel

theorem sourceRowsAt1423 : MixedData.sourceRows (1423 : Fin 2425) =
    MixedData.row1423 := by decide +kernel

theorem chunkSound88 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 88) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1408 ∨ k.val = 1409 ∨ k.val = 1410 ∨ k.val = 1411 ∨ k.val = 1412 ∨ k.val = 1413 ∨ k.val = 1414 ∨ k.val = 1415 ∨ k.val = 1416 ∨ k.val = 1417 ∨ k.val = 1418 ∨ k.val = 1419 ∨ k.val = 1420 ∨ k.val = 1421 ∨ k.val = 1422 ∨ k.val = 1423 := by omega
  rcases heq with h1408 | h1409 | h1410 | h1411 | h1412 | h1413 | h1414 | h1415 | h1416 | h1417 | h1418 | h1419 | h1420 | h1421 | h1422 | h1423
  · have he : k = (1408 : Fin 2425) := Fin.ext h1408
    subst k
    rw [sourceRowsAt1408]
    exact rowSound1408 B hB hF
  · have he : k = (1409 : Fin 2425) := Fin.ext h1409
    subst k
    rw [sourceRowsAt1409]
    exact rowSound1409 B hB hF
  · have he : k = (1410 : Fin 2425) := Fin.ext h1410
    subst k
    rw [sourceRowsAt1410]
    exact rowSound1410 B hB hF
  · have he : k = (1411 : Fin 2425) := Fin.ext h1411
    subst k
    rw [sourceRowsAt1411]
    exact rowSound1411 B hB hF
  · have he : k = (1412 : Fin 2425) := Fin.ext h1412
    subst k
    rw [sourceRowsAt1412]
    exact rowSound1412 B hB hF
  · have he : k = (1413 : Fin 2425) := Fin.ext h1413
    subst k
    rw [sourceRowsAt1413]
    exact rowSound1413 B hB hF
  · have he : k = (1414 : Fin 2425) := Fin.ext h1414
    subst k
    rw [sourceRowsAt1414]
    exact rowSound1414 B hB hF
  · have he : k = (1415 : Fin 2425) := Fin.ext h1415
    subst k
    rw [sourceRowsAt1415]
    exact rowSound1415 B hB hF
  · have he : k = (1416 : Fin 2425) := Fin.ext h1416
    subst k
    rw [sourceRowsAt1416]
    exact rowSound1416 B hB hF
  · have he : k = (1417 : Fin 2425) := Fin.ext h1417
    subst k
    rw [sourceRowsAt1417]
    exact rowSound1417 B hB hF
  · have he : k = (1418 : Fin 2425) := Fin.ext h1418
    subst k
    rw [sourceRowsAt1418]
    exact rowSound1418 B hB hF
  · have he : k = (1419 : Fin 2425) := Fin.ext h1419
    subst k
    rw [sourceRowsAt1419]
    exact rowSound1419 B hB hF
  · have he : k = (1420 : Fin 2425) := Fin.ext h1420
    subst k
    rw [sourceRowsAt1420]
    exact rowSound1420 B hB hF
  · have he : k = (1421 : Fin 2425) := Fin.ext h1421
    subst k
    rw [sourceRowsAt1421]
    exact rowSound1421 B hB hF
  · have he : k = (1422 : Fin 2425) := Fin.ext h1422
    subst k
    rw [sourceRowsAt1422]
    exact rowSound1422 B hB hF
  · have he : k = (1423 : Fin 2425) := Fin.ext h1423
    subst k
    rw [sourceRowsAt1423]
    exact rowSound1423 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
