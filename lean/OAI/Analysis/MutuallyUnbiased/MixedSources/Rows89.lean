import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources52

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1424 (mixedVector B) = 0 := by
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1513 : mixedVector B (Sum.inr 1513) = Sparse.eval nodeValue1513 (mixedVector B) := by
    change mixedMoment B node1513 node1513Labels = _
    exact sound1513 B hB hF
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
  have h2657 : mixedVector B (Sum.inr 2657) = Sparse.eval nodeValue2657 (mixedVector B) := by
    change mixedMoment B node2657 node2657Labels = _
    exact sound2657 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3259 : mixedVector B (Sum.inr 3259) = Sparse.eval nodeValue3259 (mixedVector B) := by
    change mixedMoment B node3259 node3259Labels = _
    exact sound3259 B hB hF
  have h3266 : mixedVector B (Sum.inr 3266) = Sparse.eval nodeValue3266 (mixedVector B) := by
    change mixedMoment B node3266 node3266Labels = _
    exact sound3266 B hB hF
  have h3271 : mixedVector B (Sum.inr 3271) = Sparse.eval nodeValue3271 (mixedVector B) := by
    change mixedMoment B node3271 node3271Labels = _
    exact sound3271 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  simpa only [sourceForm1663, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1512, h1513, h1520, h1526, h2657, h2683, h2737, h3259, h3266, h3271, h3293, h3296, h3300, h3301, h3302, h3303, h3306, h3547, h3564, h3582, h3583, reducedSource1424] using sourceEq1663 B hB

theorem rowSound1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1424 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1424, numericCheck1424, reducedZero1424 B hB hF, mul_zero]

theorem reducedZero1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1425 (mixedVector B) = 0 := by
  have h638 : mixedVector B (Sum.inr 638) = Sparse.eval nodeValue638 (mixedVector B) := by
    change mixedMoment B node638 node638Labels = _
    exact sound638 B hB hF
  have h641 : mixedVector B (Sum.inr 641) = Sparse.eval nodeValue641 (mixedVector B) := by
    change mixedMoment B node641 node641Labels = _
    exact sound641 B hB hF
  have h642 : mixedVector B (Sum.inr 642) = Sparse.eval nodeValue642 (mixedVector B) := by
    change mixedMoment B node642 node642Labels = _
    exact sound642 B hB hF
  have h653 : mixedVector B (Sum.inr 653) = Sparse.eval nodeValue653 (mixedVector B) := by
    change mixedMoment B node653 node653Labels = _
    exact sound653 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1664, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h638, h641, h642, h653, h1294, h4092, reducedSource1425] using sourceEq1664 B hB

theorem rowSound1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1425 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1425, numericCheck1425, reducedZero1425 B hB hF, mul_zero]

theorem reducedZero1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1426 (mixedVector B) = 0 := by
  have h1287 : mixedVector B (Sum.inr 1287) = Sparse.eval nodeValue1287 (mixedVector B) := by
    change mixedMoment B node1287 node1287Labels = _
    exact sound1287 B hB hF
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1667, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1287, h2584, h2685, h2761, h4082, reducedSource1426] using sourceEq1667 B hB

theorem rowSound1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1426 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1426, numericCheck1426, reducedZero1426 B hB hF, mul_zero]

theorem reducedZero1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1427 (mixedVector B) = 0 := by
  have h1230 : mixedVector B (Sum.inr 1230) = Sparse.eval nodeValue1230 (mixedVector B) := by
    change mixedMoment B node1230 node1230Labels = _
    exact sound1230 B hB hF
  have h2505 : mixedVector B (Sum.inr 2505) = Sparse.eval nodeValue2505 (mixedVector B) := by
    change mixedMoment B node2505 node2505Labels = _
    exact sound2505 B hB hF
  have h2551 : mixedVector B (Sum.inr 2551) = Sparse.eval nodeValue2551 (mixedVector B) := by
    change mixedMoment B node2551 node2551Labels = _
    exact sound2551 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1668, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1230, h2505, h2551, h2705, h2729, h2736, h4088, reducedSource1427] using sourceEq1668 B hB

theorem rowSound1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1427 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1427, numericCheck1427, reducedZero1427 B hB hF, mul_zero]

theorem reducedZero1428 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1428 (mixedVector B) = 0 := by
  have h4150 : mixedVector B (Sum.inr 4150) = Sparse.eval nodeValue4150 (mixedVector B) := by
    change mixedMoment B node4150 node4150Labels = _
    exact sound4150 B hB hF
  have h4151 : mixedVector B (Sum.inr 4151) = Sparse.eval nodeValue4151 (mixedVector B) := by
    change mixedMoment B node4151 node4151Labels = _
    exact sound4151 B hB hF
  have h4155 : mixedVector B (Sum.inr 4155) = Sparse.eval nodeValue4155 (mixedVector B) := by
    change mixedMoment B node4155 node4155Labels = _
    exact sound4155 B hB hF
  have h4173 : mixedVector B (Sum.inr 4173) = Sparse.eval nodeValue4173 (mixedVector B) := by
    change mixedMoment B node4173 node4173Labels = _
    exact sound4173 B hB hF
  have h4527 : mixedVector B (Sum.inr 4527) = Sparse.eval nodeValue4527 (mixedVector B) := by
    change mixedMoment B node4527 node4527Labels = _
    exact sound4527 B hB hF
  have h4530 : mixedVector B (Sum.inr 4530) = Sparse.eval nodeValue4530 (mixedVector B) := by
    change mixedMoment B node4530 node4530Labels = _
    exact sound4530 B hB hF
  have h4542 : mixedVector B (Sum.inr 4542) = Sparse.eval nodeValue4542 (mixedVector B) := by
    change mixedMoment B node4542 node4542Labels = _
    exact sound4542 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4554 : mixedVector B (Sum.inr 4554) = Sparse.eval nodeValue4554 (mixedVector B) := by
    change mixedMoment B node4554 node4554Labels = _
    exact sound4554 B hB hF
  have h4590 : mixedVector B (Sum.inr 4590) = Sparse.eval nodeValue4590 (mixedVector B) := by
    change mixedMoment B node4590 node4590Labels = _
    exact sound4590 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4593 : mixedVector B (Sum.inr 4593) = Sparse.eval nodeValue4593 (mixedVector B) := by
    change mixedMoment B node4593 node4593Labels = _
    exact sound4593 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4603 : mixedVector B (Sum.inr 4603) = Sparse.eval nodeValue4603 (mixedVector B) := by
    change mixedMoment B node4603 node4603Labels = _
    exact sound4603 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  simpa only [sourceForm1669, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4150, h4151, h4155, h4173, h4527, h4530, h4542, h4544, h4551, h4554, h4590, h4591, h4593, h4601, h4603, h4606, h4618, h5104, h5137, h5259, h5273, reducedSource1428] using sourceEq1669 B hB

theorem rowSound1428 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1428 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1428, numericCheck1428, reducedZero1428 B hB hF, mul_zero]

theorem reducedZero1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1429 (mixedVector B) = 0 := by
  have h578 : mixedVector B (Sum.inr 578) = Sparse.eval nodeValue578 (mixedVector B) := by
    change mixedMoment B node578 node578Labels = _
    exact sound578 B hB hF
  have h579 : mixedVector B (Sum.inr 579) = Sparse.eval nodeValue579 (mixedVector B) := by
    change mixedMoment B node579 node579Labels = _
    exact sound579 B hB hF
  have h583 : mixedVector B (Sum.inr 583) = Sparse.eval nodeValue583 (mixedVector B) := by
    change mixedMoment B node583 node583Labels = _
    exact sound583 B hB hF
  have h601 : mixedVector B (Sum.inr 601) = Sparse.eval nodeValue601 (mixedVector B) := by
    change mixedMoment B node601 node601Labels = _
    exact sound601 B hB hF
  have h1111 : mixedVector B (Sum.inr 1111) = Sparse.eval nodeValue1111 (mixedVector B) := by
    change mixedMoment B node1111 node1111Labels = _
    exact sound1111 B hB hF
  have h1114 : mixedVector B (Sum.inr 1114) = Sparse.eval nodeValue1114 (mixedVector B) := by
    change mixedMoment B node1114 node1114Labels = _
    exact sound1114 B hB hF
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h1162 : mixedVector B (Sum.inr 1162) = Sparse.eval nodeValue1162 (mixedVector B) := by
    change mixedMoment B node1162 node1162Labels = _
    exact sound1162 B hB hF
  have h1163 : mixedVector B (Sum.inr 1163) = Sparse.eval nodeValue1163 (mixedVector B) := by
    change mixedMoment B node1163 node1163Labels = _
    exact sound1163 B hB hF
  have h1167 : mixedVector B (Sum.inr 1167) = Sparse.eval nodeValue1167 (mixedVector B) := by
    change mixedMoment B node1167 node1167Labels = _
    exact sound1167 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1265 : mixedVector B (Sum.inr 1265) = Sparse.eval nodeValue1265 (mixedVector B) := by
    change mixedMoment B node1265 node1265Labels = _
    exact sound1265 B hB hF
  have h1266 : mixedVector B (Sum.inr 1266) = Sparse.eval nodeValue1266 (mixedVector B) := by
    change mixedMoment B node1266 node1266Labels = _
    exact sound1266 B hB hF
  have h1298 : mixedVector B (Sum.inr 1298) = Sparse.eval nodeValue1298 (mixedVector B) := by
    change mixedMoment B node1298 node1298Labels = _
    exact sound1298 B hB hF
  have h2936 : mixedVector B (Sum.inr 2936) = Sparse.eval nodeValue2936 (mixedVector B) := by
    change mixedMoment B node2936 node2936Labels = _
    exact sound2936 B hB hF
  have h3000 : mixedVector B (Sum.inr 3000) = Sparse.eval nodeValue3000 (mixedVector B) := by
    change mixedMoment B node3000 node3000Labels = _
    exact sound3000 B hB hF
  have h3088 : mixedVector B (Sum.inr 3088) = Sparse.eval nodeValue3088 (mixedVector B) := by
    change mixedMoment B node3088 node3088Labels = _
    exact sound3088 B hB hF
  have h3111 : mixedVector B (Sum.inr 3111) = Sparse.eval nodeValue3111 (mixedVector B) := by
    change mixedMoment B node3111 node3111Labels = _
    exact sound3111 B hB hF
  simpa only [sourceForm1670, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h578, h579, h583, h601, h1111, h1114, h1127, h1162, h1163, h1167, h1213, h1215, h1220, h1237, h1265, h1266, h1298, h2936, h3000, h3088, h3111, reducedSource1429] using sourceEq1670 B hB

theorem rowSound1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1429 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1429, numericCheck1429, reducedZero1429 B hB hF, mul_zero]

theorem reducedZero1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1430 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h3255 : mixedVector B (Sum.inr 3255) = Sparse.eval nodeValue3255 (mixedVector B) := by
    change mixedMoment B node3255 node3255Labels = _
    exact sound3255 B hB hF
  have h3257 : mixedVector B (Sum.inr 3257) = Sparse.eval nodeValue3257 (mixedVector B) := by
    change mixedMoment B node3257 node3257Labels = _
    exact sound3257 B hB hF
  have h3261 : mixedVector B (Sum.inr 3261) = Sparse.eval nodeValue3261 (mixedVector B) := by
    change mixedMoment B node3261 node3261Labels = _
    exact sound3261 B hB hF
  have h3263 : mixedVector B (Sum.inr 3263) = Sparse.eval nodeValue3263 (mixedVector B) := by
    change mixedMoment B node3263 node3263Labels = _
    exact sound3263 B hB hF
  have h3273 : mixedVector B (Sum.inr 3273) = Sparse.eval nodeValue3273 (mixedVector B) := by
    change mixedMoment B node3273 node3273Labels = _
    exact sound3273 B hB hF
  have h3274 : mixedVector B (Sum.inr 3274) = Sparse.eval nodeValue3274 (mixedVector B) := by
    change mixedMoment B node3274 node3274Labels = _
    exact sound3274 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  simpa only [sourceForm1671, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1505, h1508, h1515, h3255, h3257, h3261, h3263, h3273, h3274, h3290, h3291, h3292, h3294, h3297, h3299, h3304, h3483, h3521, h3544, h3546, reducedSource1430] using sourceEq1671 B hB

theorem rowSound1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1430 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1430, numericCheck1430, reducedZero1430 B hB hF, mul_zero]

theorem reducedZero1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1431 (mixedVector B) = 0 := by
  have h625 : mixedVector B (Sum.inr 625) = Sparse.eval nodeValue625 (mixedVector B) := by
    change mixedMoment B node625 node625Labels = _
    exact sound625 B hB hF
  have h630 : mixedVector B (Sum.inr 630) = Sparse.eval nodeValue630 (mixedVector B) := by
    change mixedMoment B node630 node630Labels = _
    exact sound630 B hB hF
  have h632 : mixedVector B (Sum.inr 632) = Sparse.eval nodeValue632 (mixedVector B) := by
    change mixedMoment B node632 node632Labels = _
    exact sound632 B hB hF
  have h640 : mixedVector B (Sum.inr 640) = Sparse.eval nodeValue640 (mixedVector B) := by
    change mixedMoment B node640 node640Labels = _
    exact sound640 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1672, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h625, h630, h632, h640, h1240, h4091, reducedSource1431] using sourceEq1672 B hB

theorem rowSound1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1431 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1431, numericCheck1431, reducedZero1431 B hB hF, mul_zero]

theorem reducedZero1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1432 (mixedVector B) = 0 := by
  have h1150 : mixedVector B (Sum.inr 1150) = Sparse.eval nodeValue1150 (mixedVector B) := by
    change mixedMoment B node1150 node1150Labels = _
    exact sound1150 B hB hF
  have h1152 : mixedVector B (Sum.inr 1152) = Sparse.eval nodeValue1152 (mixedVector B) := by
    change mixedMoment B node1152 node1152Labels = _
    exact sound1152 B hB hF
  have h1158 : mixedVector B (Sum.inr 1158) = Sparse.eval nodeValue1158 (mixedVector B) := by
    change mixedMoment B node1158 node1158Labels = _
    exact sound1158 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1673, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1150, h1152, h1158, h1240, h2556, h4091, reducedSource1432] using sourceEq1673 B hB

theorem rowSound1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1432 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1432, numericCheck1432, reducedZero1432 B hB hF, mul_zero]

theorem reducedZero1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1433 (mixedVector B) = 0 := by
  have h4143 : mixedVector B (Sum.inr 4143) = Sparse.eval nodeValue4143 (mixedVector B) := by
    change mixedMoment B node4143 node4143Labels = _
    exact sound4143 B hB hF
  have h4144 : mixedVector B (Sum.inr 4144) = Sparse.eval nodeValue4144 (mixedVector B) := by
    change mixedMoment B node4144 node4144Labels = _
    exact sound4144 B hB hF
  have h4145 : mixedVector B (Sum.inr 4145) = Sparse.eval nodeValue4145 (mixedVector B) := by
    change mixedMoment B node4145 node4145Labels = _
    exact sound4145 B hB hF
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4516 : mixedVector B (Sum.inr 4516) = Sparse.eval nodeValue4516 (mixedVector B) := by
    change mixedMoment B node4516 node4516Labels = _
    exact sound4516 B hB hF
  have h4517 : mixedVector B (Sum.inr 4517) = Sparse.eval nodeValue4517 (mixedVector B) := by
    change mixedMoment B node4517 node4517Labels = _
    exact sound4517 B hB hF
  have h4518 : mixedVector B (Sum.inr 4518) = Sparse.eval nodeValue4518 (mixedVector B) := by
    change mixedMoment B node4518 node4518Labels = _
    exact sound4518 B hB hF
  have h4523 : mixedVector B (Sum.inr 4523) = Sparse.eval nodeValue4523 (mixedVector B) := by
    change mixedMoment B node4523 node4523Labels = _
    exact sound4523 B hB hF
  have h4524 : mixedVector B (Sum.inr 4524) = Sparse.eval nodeValue4524 (mixedVector B) := by
    change mixedMoment B node4524 node4524Labels = _
    exact sound4524 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
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
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm1674, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4143, h4144, h4145, h4175, h4516, h4517, h4518, h4523, h4524, h4544, h4601, h4602, h4606, h4608, h4612, h4622, h4624, h5148, h5203, h5292, h5293, reducedSource1433] using sourceEq1674 B hB

theorem rowSound1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1433 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1433, numericCheck1433, reducedZero1433 B hB hF, mul_zero]

theorem reducedZero1434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1434 (mixedVector B) = 0 := by
  have h571 : mixedVector B (Sum.inr 571) = Sparse.eval nodeValue571 (mixedVector B) := by
    change mixedMoment B node571 node571Labels = _
    exact sound571 B hB hF
  have h572 : mixedVector B (Sum.inr 572) = Sparse.eval nodeValue572 (mixedVector B) := by
    change mixedMoment B node572 node572Labels = _
    exact sound572 B hB hF
  have h573 : mixedVector B (Sum.inr 573) = Sparse.eval nodeValue573 (mixedVector B) := by
    change mixedMoment B node573 node573Labels = _
    exact sound573 B hB hF
  have h603 : mixedVector B (Sum.inr 603) = Sparse.eval nodeValue603 (mixedVector B) := by
    change mixedMoment B node603 node603Labels = _
    exact sound603 B hB hF
  have h1100 : mixedVector B (Sum.inr 1100) = Sparse.eval nodeValue1100 (mixedVector B) := by
    change mixedMoment B node1100 node1100Labels = _
    exact sound1100 B hB hF
  have h1101 : mixedVector B (Sum.inr 1101) = Sparse.eval nodeValue1101 (mixedVector B) := by
    change mixedMoment B node1101 node1101Labels = _
    exact sound1101 B hB hF
  have h1102 : mixedVector B (Sum.inr 1102) = Sparse.eval nodeValue1102 (mixedVector B) := by
    change mixedMoment B node1102 node1102Labels = _
    exact sound1102 B hB hF
  have h1107 : mixedVector B (Sum.inr 1107) = Sparse.eval nodeValue1107 (mixedVector B) := by
    change mixedMoment B node1107 node1107Labels = _
    exact sound1107 B hB hF
  have h1108 : mixedVector B (Sum.inr 1108) = Sparse.eval nodeValue1108 (mixedVector B) := by
    change mixedMoment B node1108 node1108Labels = _
    exact sound1108 B hB hF
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
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
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h2927 : mixedVector B (Sum.inr 2927) = Sparse.eval nodeValue2927 (mixedVector B) := by
    change mixedMoment B node2927 node2927Labels = _
    exact sound2927 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  simpa only [sourceForm1675, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h571, h572, h573, h603, h1100, h1101, h1102, h1107, h1108, h1129, h1235, h1236, h1240, h1242, h1246, h1299, h1301, h2884, h2927, h3100, h3102, reducedSource1434] using sourceEq1675 B hB

theorem rowSound1434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1434 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1434, numericCheck1434, reducedZero1434 B hB hF, mul_zero]

theorem reducedZero1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1435 (mixedVector B) = 0 := by
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h1004 : mixedVector B (Sum.inr 1004) = Sparse.eval nodeValue1004 (mixedVector B) := by
    change mixedMoment B node1004 node1004Labels = _
    exact sound1004 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h1180 : mixedVector B (Sum.inr 1180) = Sparse.eval nodeValue1180 (mixedVector B) := by
    change mixedMoment B node1180 node1180Labels = _
    exact sound1180 B hB hF
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h1189 : mixedVector B (Sum.inr 1189) = Sparse.eval nodeValue1189 (mixedVector B) := by
    change mixedMoment B node1189 node1189Labels = _
    exact sound1189 B hB hF
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1201 : mixedVector B (Sum.inr 1201) = Sparse.eval nodeValue1201 (mixedVector B) := by
    change mixedMoment B node1201 node1201Labels = _
    exact sound1201 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h1386 : mixedVector B (Sum.inr 1386) = Sparse.eval nodeValue1386 (mixedVector B) := by
    change mixedMoment B node1386 node1386Labels = _
    exact sound1386 B hB hF
  have h1411 : mixedVector B (Sum.inr 1411) = Sparse.eval nodeValue1411 (mixedVector B) := by
    change mixedMoment B node1411 node1411Labels = _
    exact sound1411 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  simpa only [sourceForm1677, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h980, h1004, h1005, h1086, h1180, h1188, h1189, h1200, h1201, h1213, h1216, h1236, h1237, h1240, h1241, h1301, h1305, h1370, h1386, h1411, h1414, reducedSource1435] using sourceEq1677 B hB

theorem rowSound1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1435 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1435, numericCheck1435, reducedZero1435 B hB hF, mul_zero]

theorem reducedZero1436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1436 (mixedVector B) = 0 := by
  have h4152 : mixedVector B (Sum.inr 4152) = Sparse.eval nodeValue4152 (mixedVector B) := by
    change mixedMoment B node4152 node4152Labels = _
    exact sound4152 B hB hF
  have h4153 : mixedVector B (Sum.inr 4153) = Sparse.eval nodeValue4153 (mixedVector B) := by
    change mixedMoment B node4153 node4153Labels = _
    exact sound4153 B hB hF
  have h4154 : mixedVector B (Sum.inr 4154) = Sparse.eval nodeValue4154 (mixedVector B) := by
    change mixedMoment B node4154 node4154Labels = _
    exact sound4154 B hB hF
  have h4158 : mixedVector B (Sum.inr 4158) = Sparse.eval nodeValue4158 (mixedVector B) := by
    change mixedMoment B node4158 node4158Labels = _
    exact sound4158 B hB hF
  have h4176 : mixedVector B (Sum.inr 4176) = Sparse.eval nodeValue4176 (mixedVector B) := by
    change mixedMoment B node4176 node4176Labels = _
    exact sound4176 B hB hF
  have h4528 : mixedVector B (Sum.inr 4528) = Sparse.eval nodeValue4528 (mixedVector B) := by
    change mixedMoment B node4528 node4528Labels = _
    exact sound4528 B hB hF
  have h4529 : mixedVector B (Sum.inr 4529) = Sparse.eval nodeValue4529 (mixedVector B) := by
    change mixedMoment B node4529 node4529Labels = _
    exact sound4529 B hB hF
  have h4533 : mixedVector B (Sum.inr 4533) = Sparse.eval nodeValue4533 (mixedVector B) := by
    change mixedMoment B node4533 node4533Labels = _
    exact sound4533 B hB hF
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4545 : mixedVector B (Sum.inr 4545) = Sparse.eval nodeValue4545 (mixedVector B) := by
    change mixedMoment B node4545 node4545Labels = _
    exact sound4545 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4553 : mixedVector B (Sum.inr 4553) = Sparse.eval nodeValue4553 (mixedVector B) := by
    change mixedMoment B node4553 node4553Labels = _
    exact sound4553 B hB hF
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4592 : mixedVector B (Sum.inr 4592) = Sparse.eval nodeValue4592 (mixedVector B) := by
    change mixedMoment B node4592 node4592Labels = _
    exact sound4592 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4603 : mixedVector B (Sum.inr 4603) = Sparse.eval nodeValue4603 (mixedVector B) := by
    change mixedMoment B node4603 node4603Labels = _
    exact sound4603 B hB hF
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4616 : mixedVector B (Sum.inr 4616) = Sparse.eval nodeValue4616 (mixedVector B) := by
    change mixedMoment B node4616 node4616Labels = _
    exact sound4616 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  simpa only [sourceForm1678, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4152, h4153, h4154, h4158, h4176, h4528, h4529, h4533, h4541, h4545, h4546, h4549, h4553, h4589, h4591, h4592, h4599, h4602, h4603, h4607, h4608, h4612, h4616, h4619, h5101, h5134, h5258, h5271, h5274, reducedSource1436] using sourceEq1678 B hB

theorem rowSound1436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1436 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1436, numericCheck1436, reducedZero1436 B hB hF, mul_zero]

theorem reducedZero1437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1437 (mixedVector B) = 0 := by
  have h580 : mixedVector B (Sum.inr 580) = Sparse.eval nodeValue580 (mixedVector B) := by
    change mixedMoment B node580 node580Labels = _
    exact sound580 B hB hF
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h582 : mixedVector B (Sum.inr 582) = Sparse.eval nodeValue582 (mixedVector B) := by
    change mixedMoment B node582 node582Labels = _
    exact sound582 B hB hF
  have h586 : mixedVector B (Sum.inr 586) = Sparse.eval nodeValue586 (mixedVector B) := by
    change mixedMoment B node586 node586Labels = _
    exact sound586 B hB hF
  have h604 : mixedVector B (Sum.inr 604) = Sparse.eval nodeValue604 (mixedVector B) := by
    change mixedMoment B node604 node604Labels = _
    exact sound604 B hB hF
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h1113 : mixedVector B (Sum.inr 1113) = Sparse.eval nodeValue1113 (mixedVector B) := by
    change mixedMoment B node1113 node1113Labels = _
    exact sound1113 B hB hF
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h1164 : mixedVector B (Sum.inr 1164) = Sparse.eval nodeValue1164 (mixedVector B) := by
    change mixedMoment B node1164 node1164Labels = _
    exact sound1164 B hB hF
  have h1165 : mixedVector B (Sum.inr 1165) = Sparse.eval nodeValue1165 (mixedVector B) := by
    change mixedMoment B node1165 node1165Labels = _
    exact sound1165 B hB hF
  have h1166 : mixedVector B (Sum.inr 1166) = Sparse.eval nodeValue1166 (mixedVector B) := by
    change mixedMoment B node1166 node1166Labels = _
    exact sound1166 B hB hF
  have h1172 : mixedVector B (Sum.inr 1172) = Sparse.eval nodeValue1172 (mixedVector B) := by
    change mixedMoment B node1172 node1172Labels = _
    exact sound1172 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
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
  have h1302 : mixedVector B (Sum.inr 1302) = Sparse.eval nodeValue1302 (mixedVector B) := by
    change mixedMoment B node1302 node1302Labels = _
    exact sound1302 B hB hF
  have h2937 : mixedVector B (Sum.inr 2937) = Sparse.eval nodeValue2937 (mixedVector B) := by
    change mixedMoment B node2937 node2937Labels = _
    exact sound2937 B hB hF
  have h3001 : mixedVector B (Sum.inr 3001) = Sparse.eval nodeValue3001 (mixedVector B) := by
    change mixedMoment B node3001 node3001Labels = _
    exact sound3001 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  simpa only [sourceForm1679, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h580, h581, h582, h586, h604, h1112, h1113, h1117, h1130, h1164, h1165, h1166, h1172, h1216, h1217, h1219, h1241, h1260, h1261, h1262, h1267, h1269, h1274, h1291, h1302, h2937, h3001, h3089, h3109, h3112, reducedSource1437] using sourceEq1679 B hB

theorem rowSound1437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1437 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1437, numericCheck1437, reducedZero1437 B hB hF, mul_zero]

theorem reducedZero1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1438 (mixedVector B) = 0 := by
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h3256 : mixedVector B (Sum.inr 3256) = Sparse.eval nodeValue3256 (mixedVector B) := by
    change mixedMoment B node3256 node3256Labels = _
    exact sound3256 B hB hF
  have h3258 : mixedVector B (Sum.inr 3258) = Sparse.eval nodeValue3258 (mixedVector B) := by
    change mixedMoment B node3258 node3258Labels = _
    exact sound3258 B hB hF
  have h3259 : mixedVector B (Sum.inr 3259) = Sparse.eval nodeValue3259 (mixedVector B) := by
    change mixedMoment B node3259 node3259Labels = _
    exact sound3259 B hB hF
  have h3260 : mixedVector B (Sum.inr 3260) = Sparse.eval nodeValue3260 (mixedVector B) := by
    change mixedMoment B node3260 node3260Labels = _
    exact sound3260 B hB hF
  have h3264 : mixedVector B (Sum.inr 3264) = Sparse.eval nodeValue3264 (mixedVector B) := by
    change mixedMoment B node3264 node3264Labels = _
    exact sound3264 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3270 : mixedVector B (Sum.inr 3270) = Sparse.eval nodeValue3270 (mixedVector B) := by
    change mixedMoment B node3270 node3270Labels = _
    exact sound3270 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3470 : mixedVector B (Sum.inr 3470) = Sparse.eval nodeValue3470 (mixedVector B) := by
    change mixedMoment B node3470 node3470Labels = _
    exact sound3470 B hB hF
  have h3514 : mixedVector B (Sum.inr 3514) = Sparse.eval nodeValue3514 (mixedVector B) := by
    change mixedMoment B node3514 node3514Labels = _
    exact sound3514 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  simpa only [sourceForm1680, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1510, h1511, h1512, h1514, h1522, h3256, h3258, h3259, h3260, h3264, h3265, h3267, h3270, h3288, h3289, h3291, h3293, h3294, h3295, h3296, h3300, h3301, h3303, h3305, h3470, h3514, h3533, h3534, h3547, reducedSource1438] using sourceEq1680 B hB

theorem rowSound1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1438 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1438, numericCheck1438, reducedZero1438 B hB hF, mul_zero]

theorem reducedZero1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1439 (mixedVector B) = 0 := by
  have h623 : mixedVector B (Sum.inr 623) = Sparse.eval nodeValue623 (mixedVector B) := by
    change mixedMoment B node623 node623Labels = _
    exact sound623 B hB hF
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h627 : mixedVector B (Sum.inr 627) = Sparse.eval nodeValue627 (mixedVector B) := by
    change mixedMoment B node627 node627Labels = _
    exact sound627 B hB hF
  have h631 : mixedVector B (Sum.inr 631) = Sparse.eval nodeValue631 (mixedVector B) := by
    change mixedMoment B node631 node631Labels = _
    exact sound631 B hB hF
  have h638 : mixedVector B (Sum.inr 638) = Sparse.eval nodeValue638 (mixedVector B) := by
    change mixedMoment B node638 node638Labels = _
    exact sound638 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1681, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h623, h626, h627, h631, h638, h1236, h4092, reducedSource1439] using sourceEq1681 B hB

theorem rowSound1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1439 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1439, numericCheck1439, reducedZero1439 B hB hF, mul_zero]

theorem sourceRowsAt1424 : MixedData.sourceRows (1424 : Fin 2425) =
    MixedData.row1424 := by decide +kernel

theorem sourceRowsAt1425 : MixedData.sourceRows (1425 : Fin 2425) =
    MixedData.row1425 := by decide +kernel

theorem sourceRowsAt1426 : MixedData.sourceRows (1426 : Fin 2425) =
    MixedData.row1426 := by decide +kernel

theorem sourceRowsAt1427 : MixedData.sourceRows (1427 : Fin 2425) =
    MixedData.row1427 := by decide +kernel

theorem sourceRowsAt1428 : MixedData.sourceRows (1428 : Fin 2425) =
    MixedData.row1428 := by decide +kernel

theorem sourceRowsAt1429 : MixedData.sourceRows (1429 : Fin 2425) =
    MixedData.row1429 := by decide +kernel

theorem sourceRowsAt1430 : MixedData.sourceRows (1430 : Fin 2425) =
    MixedData.row1430 := by decide +kernel

theorem sourceRowsAt1431 : MixedData.sourceRows (1431 : Fin 2425) =
    MixedData.row1431 := by decide +kernel

theorem sourceRowsAt1432 : MixedData.sourceRows (1432 : Fin 2425) =
    MixedData.row1432 := by decide +kernel

theorem sourceRowsAt1433 : MixedData.sourceRows (1433 : Fin 2425) =
    MixedData.row1433 := by decide +kernel

theorem sourceRowsAt1434 : MixedData.sourceRows (1434 : Fin 2425) =
    MixedData.row1434 := by decide +kernel

theorem sourceRowsAt1435 : MixedData.sourceRows (1435 : Fin 2425) =
    MixedData.row1435 := by decide +kernel

theorem sourceRowsAt1436 : MixedData.sourceRows (1436 : Fin 2425) =
    MixedData.row1436 := by decide +kernel

theorem sourceRowsAt1437 : MixedData.sourceRows (1437 : Fin 2425) =
    MixedData.row1437 := by decide +kernel

theorem sourceRowsAt1438 : MixedData.sourceRows (1438 : Fin 2425) =
    MixedData.row1438 := by decide +kernel

theorem sourceRowsAt1439 : MixedData.sourceRows (1439 : Fin 2425) =
    MixedData.row1439 := by decide +kernel

theorem chunkSound89 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 89) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1424 ∨ k.val = 1425 ∨ k.val = 1426 ∨ k.val = 1427 ∨ k.val = 1428 ∨ k.val = 1429 ∨ k.val = 1430 ∨ k.val = 1431 ∨ k.val = 1432 ∨ k.val = 1433 ∨ k.val = 1434 ∨ k.val = 1435 ∨ k.val = 1436 ∨ k.val = 1437 ∨ k.val = 1438 ∨ k.val = 1439 := by omega
  rcases heq with h1424 | h1425 | h1426 | h1427 | h1428 | h1429 | h1430 | h1431 | h1432 | h1433 | h1434 | h1435 | h1436 | h1437 | h1438 | h1439
  · have he : k = (1424 : Fin 2425) := Fin.ext h1424
    subst k
    rw [sourceRowsAt1424]
    exact rowSound1424 B hB hF
  · have he : k = (1425 : Fin 2425) := Fin.ext h1425
    subst k
    rw [sourceRowsAt1425]
    exact rowSound1425 B hB hF
  · have he : k = (1426 : Fin 2425) := Fin.ext h1426
    subst k
    rw [sourceRowsAt1426]
    exact rowSound1426 B hB hF
  · have he : k = (1427 : Fin 2425) := Fin.ext h1427
    subst k
    rw [sourceRowsAt1427]
    exact rowSound1427 B hB hF
  · have he : k = (1428 : Fin 2425) := Fin.ext h1428
    subst k
    rw [sourceRowsAt1428]
    exact rowSound1428 B hB hF
  · have he : k = (1429 : Fin 2425) := Fin.ext h1429
    subst k
    rw [sourceRowsAt1429]
    exact rowSound1429 B hB hF
  · have he : k = (1430 : Fin 2425) := Fin.ext h1430
    subst k
    rw [sourceRowsAt1430]
    exact rowSound1430 B hB hF
  · have he : k = (1431 : Fin 2425) := Fin.ext h1431
    subst k
    rw [sourceRowsAt1431]
    exact rowSound1431 B hB hF
  · have he : k = (1432 : Fin 2425) := Fin.ext h1432
    subst k
    rw [sourceRowsAt1432]
    exact rowSound1432 B hB hF
  · have he : k = (1433 : Fin 2425) := Fin.ext h1433
    subst k
    rw [sourceRowsAt1433]
    exact rowSound1433 B hB hF
  · have he : k = (1434 : Fin 2425) := Fin.ext h1434
    subst k
    rw [sourceRowsAt1434]
    exact rowSound1434 B hB hF
  · have he : k = (1435 : Fin 2425) := Fin.ext h1435
    subst k
    rw [sourceRowsAt1435]
    exact rowSound1435 B hB hF
  · have he : k = (1436 : Fin 2425) := Fin.ext h1436
    subst k
    rw [sourceRowsAt1436]
    exact rowSound1436 B hB hF
  · have he : k = (1437 : Fin 2425) := Fin.ext h1437
    subst k
    rw [sourceRowsAt1437]
    exact rowSound1437 B hB hF
  · have he : k = (1438 : Fin 2425) := Fin.ext h1438
    subst k
    rw [sourceRowsAt1438]
    exact rowSound1438 B hB hF
  · have he : k = (1439 : Fin 2425) := Fin.ext h1439
    subst k
    rw [sourceRowsAt1439]
    exact rowSound1439 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
