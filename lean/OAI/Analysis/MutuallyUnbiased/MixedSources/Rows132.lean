import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic132
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources83

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2112 (mixedVector B) = 0 := by
  have h1534 : mixedVector B (Sum.inr 1534) = Sparse.eval nodeValue1534 (mixedVector B) := by
    change mixedMoment B node1534 node1534Labels = _
    exact sound1534 B hB hF
  have h1541 : mixedVector B (Sum.inr 1541) = Sparse.eval nodeValue1541 (mixedVector B) := by
    change mixedMoment B node1541 node1541Labels = _
    exact sound1541 B hB hF
  have h4062 : mixedVector B (Sum.inr 4062) = Sparse.eval nodeValue4062 (mixedVector B) := by
    change mixedMoment B node4062 node4062Labels = _
    exact sound4062 B hB hF
  simpa only [sourceForm2655, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1534, h1541, h4062, reducedSource2112] using sourceEq2655 B hB

theorem rowSound2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2112 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2112, numericCheck2112, reducedZero2112 B hB hF, mul_zero]

theorem reducedZero2113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2113 (mixedVector B) = 0 := by
  have h686 : mixedVector B (Sum.inr 686) = Sparse.eval nodeValue686 (mixedVector B) := by
    change mixedMoment B node686 node686Labels = _
    exact sound686 B hB hF
  have h697 : mixedVector B (Sum.inr 697) = Sparse.eval nodeValue697 (mixedVector B) := by
    change mixedMoment B node697 node697Labels = _
    exact sound697 B hB hF
  have h1541 : mixedVector B (Sum.inr 1541) = Sparse.eval nodeValue1541 (mixedVector B) := by
    change mixedMoment B node1541 node1541Labels = _
    exact sound1541 B hB hF
  have h4062 : mixedVector B (Sum.inr 4062) = Sparse.eval nodeValue4062 (mixedVector B) := by
    change mixedMoment B node4062 node4062Labels = _
    exact sound4062 B hB hF
  simpa only [sourceForm2656, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h686, h697, h1541, h4062, reducedSource2113] using sourceEq2656 B hB

theorem rowSound2113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2113 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2113, numericCheck2113, reducedZero2113 B hB hF, mul_zero]

theorem reducedZero2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2114 (mixedVector B) = 0 := by
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  simpa only [sourceForm2657, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1521, h1532, h1537, h1540, h4060, reducedSource2114] using sourceEq2657 B hB

theorem rowSound2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2114 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2114, numericCheck2114, reducedZero2114 B hB hF, mul_zero]

theorem reducedZero2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2115 (mixedVector B) = 0 := by
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  simpa only [sourceForm2658, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1516, h1521, h1537, h4060, reducedSource2115] using sourceEq2658 B hB

theorem rowSound2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2115 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2115, numericCheck2115, reducedZero2115 B hB hF, mul_zero]

theorem reducedZero2116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2116 (mixedVector B) = 0 := by
  have h683 : mixedVector B (Sum.inr 683) = Sparse.eval nodeValue683 (mixedVector B) := by
    change mixedMoment B node683 node683Labels = _
    exact sound683 B hB hF
  have h691 : mixedVector B (Sum.inr 691) = Sparse.eval nodeValue691 (mixedVector B) := by
    change mixedMoment B node691 node691Labels = _
    exact sound691 B hB hF
  have h695 : mixedVector B (Sum.inr 695) = Sparse.eval nodeValue695 (mixedVector B) := by
    change mixedMoment B node695 node695Labels = _
    exact sound695 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  simpa only [sourceForm2659, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h683, h691, h695, h1537, h4060, reducedSource2116] using sourceEq2659 B hB

theorem rowSound2116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2116 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2116, numericCheck2116, reducedZero2116 B hB hF, mul_zero]

theorem reducedZero2117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2117 (mixedVector B) = 0 := by
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1529 : mixedVector B (Sum.inr 1529) = Sparse.eval nodeValue1529 (mixedVector B) := by
    change mixedMoment B node1529 node1529Labels = _
    exact sound1529 B hB hF
  have h1531 : mixedVector B (Sum.inr 1531) = Sparse.eval nodeValue1531 (mixedVector B) := by
    change mixedMoment B node1531 node1531Labels = _
    exact sound1531 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2663, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1527, h1529, h1531, h1539, h4061, reducedSource2117] using sourceEq2663 B hB

theorem rowSound2117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2117 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2117, numericCheck2117, reducedZero2117 B hB hF, mul_zero]

theorem reducedZero2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2118 (mixedVector B) = 0 := by
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2664, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1523, h1527, h1538, h1539, h4061, reducedSource2118] using sourceEq2664 B hB

theorem rowSound2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2118 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2118, numericCheck2118, reducedZero2118 B hB hF, mul_zero]

theorem reducedZero2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2119 (mixedVector B) = 0 := by
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2665, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1533, h1538, h1539, h4061, reducedSource2119] using sourceEq2665 B hB

theorem rowSound2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2119 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2119, numericCheck2119, reducedZero2119 B hB hF, mul_zero]

theorem reducedZero2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2120 (mixedVector B) = 0 := by
  have h696 : mixedVector B (Sum.inr 696) = Sparse.eval nodeValue696 (mixedVector B) := by
    change mixedMoment B node696 node696Labels = _
    exact sound696 B hB hF
  have h1496 : mixedVector B (Sum.inr 1496) = Sparse.eval nodeValue1496 (mixedVector B) := by
    change mixedMoment B node1496 node1496Labels = _
    exact sound1496 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2667, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h696, h1496, h1538, h1539, h4061, reducedSource2120] using sourceEq2667 B hB

theorem rowSound2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2120 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2120, numericCheck2120, reducedZero2120 B hB hF, mul_zero]

theorem reducedZero2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2121 (mixedVector B) = 0 := by
  have h693 : mixedVector B (Sum.inr 693) = Sparse.eval nodeValue693 (mixedVector B) := by
    change mixedMoment B node693 node693Labels = _
    exact sound693 B hB hF
  have h1495 : mixedVector B (Sum.inr 1495) = Sparse.eval nodeValue1495 (mixedVector B) := by
    change mixedMoment B node1495 node1495Labels = _
    exact sound1495 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  simpa only [sourceForm2669, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h693, h1495, h1527, h1538, h4061, reducedSource2121] using sourceEq2669 B hB

theorem rowSound2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2121 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2121, numericCheck2121, reducedZero2121 B hB hF, mul_zero]

theorem reducedZero2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2122 (mixedVector B) = 0 := by
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  simpa only [sourceForm2671, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1514, h1518, h1520, h1535, h4058, reducedSource2122] using sourceEq2671 B hB

theorem rowSound2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2122 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2122, numericCheck2122, reducedZero2122 B hB hF, mul_zero]

theorem reducedZero2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2123 (mixedVector B) = 0 := by
  have h1509 : mixedVector B (Sum.inr 1509) = Sparse.eval nodeValue1509 (mixedVector B) := by
    change mixedMoment B node1509 node1509Labels = _
    exact sound1509 B hB hF
  have h1528 : mixedVector B (Sum.inr 1528) = Sparse.eval nodeValue1528 (mixedVector B) := by
    change mixedMoment B node1528 node1528Labels = _
    exact sound1528 B hB hF
  have h1530 : mixedVector B (Sum.inr 1530) = Sparse.eval nodeValue1530 (mixedVector B) := by
    change mixedMoment B node1530 node1530Labels = _
    exact sound1530 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  simpa only [sourceForm2672, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1509, h1528, h1530, h1535, h4058, reducedSource2123] using sourceEq2672 B hB

theorem rowSound2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2123 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2123, numericCheck2123, reducedZero2123 B hB hF, mul_zero]

theorem reducedZero2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2124 (mixedVector B) = 0 := by
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1509 : mixedVector B (Sum.inr 1509) = Sparse.eval nodeValue1509 (mixedVector B) := by
    change mixedMoment B node1509 node1509Labels = _
    exact sound1509 B hB hF
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1535 : mixedVector B (Sum.inr 1535) = Sparse.eval nodeValue1535 (mixedVector B) := by
    change mixedMoment B node1535 node1535Labels = _
    exact sound1535 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  simpa only [sourceForm2673, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1505, h1509, h1518, h1535, h4058, reducedSource2124] using sourceEq2673 B hB

theorem rowSound2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2124 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2124, numericCheck2124, reducedZero2124 B hB hF, mul_zero]

theorem reducedZero2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2125 (mixedVector B) = 0 := by
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1513 : mixedVector B (Sum.inr 1513) = Sparse.eval nodeValue1513 (mixedVector B) := by
    change mixedMoment B node1513 node1513Labels = _
    exact sound1513 B hB hF
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1525 : mixedVector B (Sum.inr 1525) = Sparse.eval nodeValue1525 (mixedVector B) := by
    change mixedMoment B node1525 node1525Labels = _
    exact sound1525 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  simpa only [sourceForm2679, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1511, h1513, h1519, h1525, h4059, reducedSource2125] using sourceEq2679 B hB

theorem rowSound2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2125 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2125, numericCheck2125, reducedZero2125 B hB hF, mul_zero]

theorem reducedZero2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2126 (mixedVector B) = 0 := by
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1525 : mixedVector B (Sum.inr 1525) = Sparse.eval nodeValue1525 (mixedVector B) := by
    change mixedMoment B node1525 node1525Labels = _
    exact sound1525 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
  have h1536 : mixedVector B (Sum.inr 1536) = Sparse.eval nodeValue1536 (mixedVector B) := by
    change mixedMoment B node1536 node1536Labels = _
    exact sound1536 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  simpa only [sourceForm2680, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1519, h1522, h1525, h1526, h1536, h4059, reducedSource2126] using sourceEq2680 B hB

theorem rowSound2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2126 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2126, numericCheck2126, reducedZero2126 B hB hF, mul_zero]

theorem reducedZero2127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2127 (mixedVector B) = 0 := by
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1536 : mixedVector B (Sum.inr 1536) = Sparse.eval nodeValue1536 (mixedVector B) := by
    change mixedMoment B node1536 node1536Labels = _
    exact sound1536 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  simpa only [sourceForm2681, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1515, h1519, h1536, h4059, reducedSource2127] using sourceEq2681 B hB

theorem rowSound2127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2127 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2127, numericCheck2127, reducedZero2127 B hB hF, mul_zero]

theorem sourceRowsAt2112 : MixedData.sourceRows (2112 : Fin 2425) =
    MixedData.row2112 := by decide +kernel

theorem sourceRowsAt2113 : MixedData.sourceRows (2113 : Fin 2425) =
    MixedData.row2113 := by decide +kernel

theorem sourceRowsAt2114 : MixedData.sourceRows (2114 : Fin 2425) =
    MixedData.row2114 := by decide +kernel

theorem sourceRowsAt2115 : MixedData.sourceRows (2115 : Fin 2425) =
    MixedData.row2115 := by decide +kernel

theorem sourceRowsAt2116 : MixedData.sourceRows (2116 : Fin 2425) =
    MixedData.row2116 := by decide +kernel

theorem sourceRowsAt2117 : MixedData.sourceRows (2117 : Fin 2425) =
    MixedData.row2117 := by decide +kernel

theorem sourceRowsAt2118 : MixedData.sourceRows (2118 : Fin 2425) =
    MixedData.row2118 := by decide +kernel

theorem sourceRowsAt2119 : MixedData.sourceRows (2119 : Fin 2425) =
    MixedData.row2119 := by decide +kernel

theorem sourceRowsAt2120 : MixedData.sourceRows (2120 : Fin 2425) =
    MixedData.row2120 := by decide +kernel

theorem sourceRowsAt2121 : MixedData.sourceRows (2121 : Fin 2425) =
    MixedData.row2121 := by decide +kernel

theorem sourceRowsAt2122 : MixedData.sourceRows (2122 : Fin 2425) =
    MixedData.row2122 := by decide +kernel

theorem sourceRowsAt2123 : MixedData.sourceRows (2123 : Fin 2425) =
    MixedData.row2123 := by decide +kernel

theorem sourceRowsAt2124 : MixedData.sourceRows (2124 : Fin 2425) =
    MixedData.row2124 := by decide +kernel

theorem sourceRowsAt2125 : MixedData.sourceRows (2125 : Fin 2425) =
    MixedData.row2125 := by decide +kernel

theorem sourceRowsAt2126 : MixedData.sourceRows (2126 : Fin 2425) =
    MixedData.row2126 := by decide +kernel

theorem sourceRowsAt2127 : MixedData.sourceRows (2127 : Fin 2425) =
    MixedData.row2127 := by decide +kernel

theorem chunkSound132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 132) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2112 ∨ k.val = 2113 ∨ k.val = 2114 ∨ k.val = 2115 ∨ k.val = 2116 ∨ k.val = 2117 ∨ k.val = 2118 ∨ k.val = 2119 ∨ k.val = 2120 ∨ k.val = 2121 ∨ k.val = 2122 ∨ k.val = 2123 ∨ k.val = 2124 ∨ k.val = 2125 ∨ k.val = 2126 ∨ k.val = 2127 := by omega
  rcases heq with h2112 | h2113 | h2114 | h2115 | h2116 | h2117 | h2118 | h2119 | h2120 | h2121 | h2122 | h2123 | h2124 | h2125 | h2126 | h2127
  · have he : k = (2112 : Fin 2425) := Fin.ext h2112
    subst k
    rw [sourceRowsAt2112]
    exact rowSound2112 B hB hF
  · have he : k = (2113 : Fin 2425) := Fin.ext h2113
    subst k
    rw [sourceRowsAt2113]
    exact rowSound2113 B hB hF
  · have he : k = (2114 : Fin 2425) := Fin.ext h2114
    subst k
    rw [sourceRowsAt2114]
    exact rowSound2114 B hB hF
  · have he : k = (2115 : Fin 2425) := Fin.ext h2115
    subst k
    rw [sourceRowsAt2115]
    exact rowSound2115 B hB hF
  · have he : k = (2116 : Fin 2425) := Fin.ext h2116
    subst k
    rw [sourceRowsAt2116]
    exact rowSound2116 B hB hF
  · have he : k = (2117 : Fin 2425) := Fin.ext h2117
    subst k
    rw [sourceRowsAt2117]
    exact rowSound2117 B hB hF
  · have he : k = (2118 : Fin 2425) := Fin.ext h2118
    subst k
    rw [sourceRowsAt2118]
    exact rowSound2118 B hB hF
  · have he : k = (2119 : Fin 2425) := Fin.ext h2119
    subst k
    rw [sourceRowsAt2119]
    exact rowSound2119 B hB hF
  · have he : k = (2120 : Fin 2425) := Fin.ext h2120
    subst k
    rw [sourceRowsAt2120]
    exact rowSound2120 B hB hF
  · have he : k = (2121 : Fin 2425) := Fin.ext h2121
    subst k
    rw [sourceRowsAt2121]
    exact rowSound2121 B hB hF
  · have he : k = (2122 : Fin 2425) := Fin.ext h2122
    subst k
    rw [sourceRowsAt2122]
    exact rowSound2122 B hB hF
  · have he : k = (2123 : Fin 2425) := Fin.ext h2123
    subst k
    rw [sourceRowsAt2123]
    exact rowSound2123 B hB hF
  · have he : k = (2124 : Fin 2425) := Fin.ext h2124
    subst k
    rw [sourceRowsAt2124]
    exact rowSound2124 B hB hF
  · have he : k = (2125 : Fin 2425) := Fin.ext h2125
    subst k
    rw [sourceRowsAt2125]
    exact rowSound2125 B hB hF
  · have he : k = (2126 : Fin 2425) := Fin.ext h2126
    subst k
    rw [sourceRowsAt2126]
    exact rowSound2126 B hB hF
  · have he : k = (2127 : Fin 2425) := Fin.ext h2127
    subst k
    rw [sourceRowsAt2127]
    exact rowSound2127 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
