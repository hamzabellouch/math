import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources42

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1168 (mixedVector B) = 0 := by
  have h847 : mixedVector B (Sum.inr 847) = Sparse.eval nodeValue847 (mixedVector B) := by
    change mixedMoment B node847 node847Labels = _
    exact sound847 B hB hF
  have h851 : mixedVector B (Sum.inr 851) = Sparse.eval nodeValue851 (mixedVector B) := by
    change mixedMoment B node851 node851Labels = _
    exact sound851 B hB hF
  have h853 : mixedVector B (Sum.inr 853) = Sparse.eval nodeValue853 (mixedVector B) := by
    change mixedMoment B node853 node853Labels = _
    exact sound853 B hB hF
  have h857 : mixedVector B (Sum.inr 857) = Sparse.eval nodeValue857 (mixedVector B) := by
    change mixedMoment B node857 node857Labels = _
    exact sound857 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1347, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h847, h851, h853, h857, h1750, h4070, reducedSource1168] using sourceEq1347 B hB

theorem rowSound1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1168 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1168, numericCheck1168, reducedZero1168 B hB hF, mul_zero]

theorem reducedZero1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1169 (mixedVector B) = 0 := by
  have h4151 : mixedVector B (Sum.inr 4151) = Sparse.eval nodeValue4151 (mixedVector B) := by
    change mixedMoment B node4151 node4151Labels = _
    exact sound4151 B hB hF
  have h4156 : mixedVector B (Sum.inr 4156) = Sparse.eval nodeValue4156 (mixedVector B) := by
    change mixedMoment B node4156 node4156Labels = _
    exact sound4156 B hB hF
  have h4160 : mixedVector B (Sum.inr 4160) = Sparse.eval nodeValue4160 (mixedVector B) := by
    change mixedMoment B node4160 node4160Labels = _
    exact sound4160 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4326 : mixedVector B (Sum.inr 4326) = Sparse.eval nodeValue4326 (mixedVector B) := by
    change mixedMoment B node4326 node4326Labels = _
    exact sound4326 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4373 : mixedVector B (Sum.inr 4373) = Sparse.eval nodeValue4373 (mixedVector B) := by
    change mixedMoment B node4373 node4373Labels = _
    exact sound4373 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1348, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4151, h4156, h4160, h4177, h4326, h4330, h4334, h4346, h4365, h4370, h4373, h4457, h4460, h4466, h4468, h4498, h4505, h4804, h4868, h4894, h4897, reducedSource1169] using sourceEq1348 B hB

theorem rowSound1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1169 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1169, numericCheck1169, reducedZero1169 B hB hF, mul_zero]

theorem reducedZero1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1170 (mixedVector B) = 0 := by
  have h630 : mixedVector B (Sum.inr 630) = Sparse.eval nodeValue630 (mixedVector B) := by
    change mixedMoment B node630 node630Labels = _
    exact sound630 B hB hF
  have h633 : mixedVector B (Sum.inr 633) = Sparse.eval nodeValue633 (mixedVector B) := by
    change mixedMoment B node633 node633Labels = _
    exact sound633 B hB hF
  have h636 : mixedVector B (Sum.inr 636) = Sparse.eval nodeValue636 (mixedVector B) := by
    change mixedMoment B node636 node636Labels = _
    exact sound636 B hB hF
  have h647 : mixedVector B (Sum.inr 647) = Sparse.eval nodeValue647 (mixedVector B) := by
    change mixedMoment B node647 node647Labels = _
    exact sound647 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1275 : mixedVector B (Sum.inr 1275) = Sparse.eval nodeValue1275 (mixedVector B) := by
    change mixedMoment B node1275 node1275Labels = _
    exact sound1275 B hB hF
  have h1320 : mixedVector B (Sum.inr 1320) = Sparse.eval nodeValue1320 (mixedVector B) := by
    change mixedMoment B node1320 node1320Labels = _
    exact sound1320 B hB hF
  have h1325 : mixedVector B (Sum.inr 1325) = Sparse.eval nodeValue1325 (mixedVector B) := by
    change mixedMoment B node1325 node1325Labels = _
    exact sound1325 B hB hF
  have h1329 : mixedVector B (Sum.inr 1329) = Sparse.eval nodeValue1329 (mixedVector B) := by
    change mixedMoment B node1329 node1329Labels = _
    exact sound1329 B hB hF
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h1342 : mixedVector B (Sum.inr 1342) = Sparse.eval nodeValue1342 (mixedVector B) := by
    change mixedMoment B node1342 node1342Labels = _
    exact sound1342 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1448 : mixedVector B (Sum.inr 1448) = Sparse.eval nodeValue1448 (mixedVector B) := by
    change mixedMoment B node1448 node1448Labels = _
    exact sound1448 B hB hF
  have h1450 : mixedVector B (Sum.inr 1450) = Sparse.eval nodeValue1450 (mixedVector B) := by
    change mixedMoment B node1450 node1450Labels = _
    exact sound1450 B hB hF
  have h2941 : mixedVector B (Sum.inr 2941) = Sparse.eval nodeValue2941 (mixedVector B) := by
    change mixedMoment B node2941 node2941Labels = _
    exact sound2941 B hB hF
  have h2966 : mixedVector B (Sum.inr 2966) = Sparse.eval nodeValue2966 (mixedVector B) := by
    change mixedMoment B node2966 node2966Labels = _
    exact sound2966 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm1349, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h630, h633, h636, h647, h1118, h1142, h1275, h1320, h1325, h1329, h1334, h1342, h1414, h1416, h1419, h1448, h1450, h2941, h2966, h3114, h3230, reducedSource1170] using sourceEq1349 B hB

theorem rowSound1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1170 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1170, numericCheck1170, reducedZero1170 B hB hF, mul_zero]

theorem reducedZero1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1171 (mixedVector B) = 0 := by
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  simpa only [sourceForm1350, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1505, h1516, h1518, h1523, h1663, h1672, h1674, h1679, h1704, h1707, h1722, h1725, h1727, h1735, h1738, h1752, h1754, h2203, h2261, h2264, h2292, reducedSource1171] using sourceEq1350 B hB

theorem rowSound1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1171 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1171, numericCheck1171, reducedZero1171 B hB hF, mul_zero]

theorem reducedZero1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1172 (mixedVector B) = 0 := by
  have h579 : mixedVector B (Sum.inr 579) = Sparse.eval nodeValue579 (mixedVector B) := by
    change mixedMoment B node579 node579Labels = _
    exact sound579 B hB hF
  have h584 : mixedVector B (Sum.inr 584) = Sparse.eval nodeValue584 (mixedVector B) := by
    change mixedMoment B node584 node584Labels = _
    exact sound584 B hB hF
  have h588 : mixedVector B (Sum.inr 588) = Sparse.eval nodeValue588 (mixedVector B) := by
    change mixedMoment B node588 node588Labels = _
    exact sound588 B hB hF
  have h605 : mixedVector B (Sum.inr 605) = Sparse.eval nodeValue605 (mixedVector B) := by
    change mixedMoment B node605 node605Labels = _
    exact sound605 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1351, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h579, h584, h588, h605, h1043, h4084, reducedSource1172] using sourceEq1351 B hB

theorem rowSound1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1172 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1172, numericCheck1172, reducedZero1172 B hB hF, mul_zero]

theorem reducedZero1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1173 (mixedVector B) = 0 := by
  have h605 : mixedVector B (Sum.inr 605) = Sparse.eval nodeValue605 (mixedVector B) := by
    change mixedMoment B node605 node605Labels = _
    exact sound605 B hB hF
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h1089 : mixedVector B (Sum.inr 1089) = Sparse.eval nodeValue1089 (mixedVector B) := by
    change mixedMoment B node1089 node1089Labels = _
    exact sound1089 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1352, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h605, h924, h1043, h1082, h1089, h4084, reducedSource1173] using sourceEq1352 B hB

theorem rowSound1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1173 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1173, numericCheck1173, reducedZero1173 B hB hF, mul_zero]

theorem reducedZero1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1174 (mixedVector B) = 0 := by
  have h943 : mixedVector B (Sum.inr 943) = Sparse.eval nodeValue943 (mixedVector B) := by
    change mixedMoment B node943 node943Labels = _
    exact sound943 B hB hF
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h952 : mixedVector B (Sum.inr 952) = Sparse.eval nodeValue952 (mixedVector B) := by
    change mixedMoment B node952 node952Labels = _
    exact sound952 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1353, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h943, h948, h952, h1043, h2109, h4084, reducedSource1174] using sourceEq1353 B hB

theorem rowSound1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1174 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1174, numericCheck1174, reducedZero1174 B hB hF, mul_zero]

theorem reducedZero1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1175 (mixedVector B) = 0 := by
  have h579 : mixedVector B (Sum.inr 579) = Sparse.eval nodeValue579 (mixedVector B) := by
    change mixedMoment B node579 node579Labels = _
    exact sound579 B hB hF
  have h904 : mixedVector B (Sum.inr 904) = Sparse.eval nodeValue904 (mixedVector B) := by
    change mixedMoment B node904 node904Labels = _
    exact sound904 B hB hF
  have h943 : mixedVector B (Sum.inr 943) = Sparse.eval nodeValue943 (mixedVector B) := by
    change mixedMoment B node943 node943Labels = _
    exact sound943 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1354, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h579, h904, h943, h1040, h1043, h4084, reducedSource1175] using sourceEq1354 B hB

theorem rowSound1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1175 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1175, numericCheck1175, reducedZero1175 B hB hF, mul_zero]

theorem reducedZero1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1176 (mixedVector B) = 0 := by
  have h904 : mixedVector B (Sum.inr 904) = Sparse.eval nodeValue904 (mixedVector B) := by
    change mixedMoment B node904 node904Labels = _
    exact sound904 B hB hF
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h912 : mixedVector B (Sum.inr 912) = Sparse.eval nodeValue912 (mixedVector B) := by
    change mixedMoment B node912 node912Labels = _
    exact sound912 B hB hF
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1355, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h904, h908, h912, h924, h1043, h2022, h4084, reducedSource1176] using sourceEq1355 B hB

theorem rowSound1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1176 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1176, numericCheck1176, reducedZero1176 B hB hF, mul_zero]

theorem reducedZero1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1177 (mixedVector B) = 0 := by
  have h4101 : mixedVector B (Sum.inr 4101) = Sparse.eval nodeValue4101 (mixedVector B) := by
    change mixedMoment B node4101 node4101Labels = _
    exact sound4101 B hB hF
  have h4103 : mixedVector B (Sum.inr 4103) = Sparse.eval nodeValue4103 (mixedVector B) := by
    change mixedMoment B node4103 node4103Labels = _
    exact sound4103 B hB hF
  have h4110 : mixedVector B (Sum.inr 4110) = Sparse.eval nodeValue4110 (mixedVector B) := by
    change mixedMoment B node4110 node4110Labels = _
    exact sound4110 B hB hF
  have h4121 : mixedVector B (Sum.inr 4121) = Sparse.eval nodeValue4121 (mixedVector B) := by
    change mixedMoment B node4121 node4121Labels = _
    exact sound4121 B hB hF
  have h4287 : mixedVector B (Sum.inr 4287) = Sparse.eval nodeValue4287 (mixedVector B) := by
    change mixedMoment B node4287 node4287Labels = _
    exact sound4287 B hB hF
  have h4289 : mixedVector B (Sum.inr 4289) = Sparse.eval nodeValue4289 (mixedVector B) := by
    change mixedMoment B node4289 node4289Labels = _
    exact sound4289 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4303 : mixedVector B (Sum.inr 4303) = Sparse.eval nodeValue4303 (mixedVector B) := by
    change mixedMoment B node4303 node4303Labels = _
    exact sound4303 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4350 : mixedVector B (Sum.inr 4350) = Sparse.eval nodeValue4350 (mixedVector B) := by
    change mixedMoment B node4350 node4350Labels = _
    exact sound4350 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4405 : mixedVector B (Sum.inr 4405) = Sparse.eval nodeValue4405 (mixedVector B) := by
    change mixedMoment B node4405 node4405Labels = _
    exact sound4405 B hB hF
  have h4428 : mixedVector B (Sum.inr 4428) = Sparse.eval nodeValue4428 (mixedVector B) := by
    change mixedMoment B node4428 node4428Labels = _
    exact sound4428 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm1356, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4101, h4103, h4110, h4121, h4287, h4289, h4295, h4303, h4346, h4350, h4360, h4401, h4405, h4428, h4458, h4467, h4499, h5075, h5171, h5261, h5293, reducedSource1177] using sourceEq1356 B hB

theorem rowSound1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1177 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1177, numericCheck1177, reducedZero1177 B hB hF, mul_zero]

theorem reducedZero1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1178 (mixedVector B) = 0 := by
  have h538 : mixedVector B (Sum.inr 538) = Sparse.eval nodeValue538 (mixedVector B) := by
    change mixedMoment B node538 node538Labels = _
    exact sound538 B hB hF
  have h540 : mixedVector B (Sum.inr 540) = Sparse.eval nodeValue540 (mixedVector B) := by
    change mixedMoment B node540 node540Labels = _
    exact sound540 B hB hF
  have h547 : mixedVector B (Sum.inr 547) = Sparse.eval nodeValue547 (mixedVector B) := by
    change mixedMoment B node547 node547Labels = _
    exact sound547 B hB hF
  have h555 : mixedVector B (Sum.inr 555) = Sparse.eval nodeValue555 (mixedVector B) := by
    change mixedMoment B node555 node555Labels = _
    exact sound555 B hB hF
  have h865 : mixedVector B (Sum.inr 865) = Sparse.eval nodeValue865 (mixedVector B) := by
    change mixedMoment B node865 node865Labels = _
    exact sound865 B hB hF
  have h867 : mixedVector B (Sum.inr 867) = Sparse.eval nodeValue867 (mixedVector B) := by
    change mixedMoment B node867 node867Labels = _
    exact sound867 B hB hF
  have h873 : mixedVector B (Sum.inr 873) = Sparse.eval nodeValue873 (mixedVector B) := by
    change mixedMoment B node873 node873Labels = _
    exact sound873 B hB hF
  have h881 : mixedVector B (Sum.inr 881) = Sparse.eval nodeValue881 (mixedVector B) := by
    change mixedMoment B node881 node881Labels = _
    exact sound881 B hB hF
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h928 : mixedVector B (Sum.inr 928) = Sparse.eval nodeValue928 (mixedVector B) := by
    change mixedMoment B node928 node928Labels = _
    exact sound928 B hB hF
  have h938 : mixedVector B (Sum.inr 938) = Sparse.eval nodeValue938 (mixedVector B) := by
    change mixedMoment B node938 node938Labels = _
    exact sound938 B hB hF
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h986 : mixedVector B (Sum.inr 986) = Sparse.eval nodeValue986 (mixedVector B) := by
    change mixedMoment B node986 node986Labels = _
    exact sound986 B hB hF
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2598 : mixedVector B (Sum.inr 2598) = Sparse.eval nodeValue2598 (mixedVector B) := by
    change mixedMoment B node2598 node2598Labels = _
    exact sound2598 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  simpa only [sourceForm1357, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h538, h540, h547, h555, h865, h867, h873, h881, h924, h928, h938, h982, h986, h1009, h1041, h1050, h1083, h2482, h2598, h2726, h2767, reducedSource1178] using sourceEq1357 B hB

theorem rowSound1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1178 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1178, numericCheck1178, reducedZero1178 B hB hF, mul_zero]

theorem reducedZero1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1179 (mixedVector B) = 0 := by
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h1361 : mixedVector B (Sum.inr 1361) = Sparse.eval nodeValue1361 (mixedVector B) := by
    change mixedMoment B node1361 node1361Labels = _
    exact sound1361 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h1373 : mixedVector B (Sum.inr 1373) = Sparse.eval nodeValue1373 (mixedVector B) := by
    change mixedMoment B node1373 node1373Labels = _
    exact sound1373 B hB hF
  have h1379 : mixedVector B (Sum.inr 1379) = Sparse.eval nodeValue1379 (mixedVector B) := by
    change mixedMoment B node1379 node1379Labels = _
    exact sound1379 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1389 : mixedVector B (Sum.inr 1389) = Sparse.eval nodeValue1389 (mixedVector B) := by
    change mixedMoment B node1389 node1389Labels = _
    exact sound1389 B hB hF
  have h1397 : mixedVector B (Sum.inr 1397) = Sparse.eval nodeValue1397 (mixedVector B) := by
    change mixedMoment B node1397 node1397Labels = _
    exact sound1397 B hB hF
  have h1399 : mixedVector B (Sum.inr 1399) = Sparse.eval nodeValue1399 (mixedVector B) := by
    change mixedMoment B node1399 node1399Labels = _
    exact sound1399 B hB hF
  have h1413 : mixedVector B (Sum.inr 1413) = Sparse.eval nodeValue1413 (mixedVector B) := by
    change mixedMoment B node1413 node1413Labels = _
    exact sound1413 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1417 : mixedVector B (Sum.inr 1417) = Sparse.eval nodeValue1417 (mixedVector B) := by
    change mixedMoment B node1417 node1417Labels = _
    exact sound1417 B hB hF
  have h1450 : mixedVector B (Sum.inr 1450) = Sparse.eval nodeValue1450 (mixedVector B) := by
    change mixedMoment B node1450 node1450Labels = _
    exact sound1450 B hB hF
  have h1452 : mixedVector B (Sum.inr 1452) = Sparse.eval nodeValue1452 (mixedVector B) := by
    change mixedMoment B node1452 node1452Labels = _
    exact sound1452 B hB hF
  have h1471 : mixedVector B (Sum.inr 1471) = Sparse.eval nodeValue1471 (mixedVector B) := by
    change mixedMoment B node1471 node1471Labels = _
    exact sound1471 B hB hF
  have h1478 : mixedVector B (Sum.inr 1478) = Sparse.eval nodeValue1478 (mixedVector B) := by
    change mixedMoment B node1478 node1478Labels = _
    exact sound1478 B hB hF
  have h1484 : mixedVector B (Sum.inr 1484) = Sparse.eval nodeValue1484 (mixedVector B) := by
    change mixedMoment B node1484 node1484Labels = _
    exact sound1484 B hB hF
  have h1485 : mixedVector B (Sum.inr 1485) = Sparse.eval nodeValue1485 (mixedVector B) := by
    change mixedMoment B node1485 node1485Labels = _
    exact sound1485 B hB hF
  simpa only [sourceForm1360, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1217, h1242, h1243, h1307, h1361, h1372, h1373, h1379, h1388, h1389, h1397, h1399, h1413, h1416, h1417, h1450, h1452, h1471, h1478, h1484, h1485, reducedSource1179] using sourceEq1360 B hB

theorem rowSound1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1179 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1179, numericCheck1179, reducedZero1179 B hB hF, mul_zero]

theorem reducedZero1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1180 (mixedVector B) = 0 := by
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2103 : mixedVector B (Sum.inr 2103) = Sparse.eval nodeValue2103 (mixedVector B) := by
    change mixedMoment B node2103 node2103Labels = _
    exact sound2103 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1361, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1037, h2018, h2103, h2208, h2261, h4081, reducedSource1180] using sourceEq1361 B hB

theorem rowSound1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1180 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1180, numericCheck1180, reducedZero1180 B hB hF, mul_zero]

theorem reducedZero1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1181 (mixedVector B) = 0 := by
  have h594 : mixedVector B (Sum.inr 594) = Sparse.eval nodeValue594 (mixedVector B) := by
    change mixedMoment B node594 node594Labels = _
    exact sound594 B hB hF
  have h916 : mixedVector B (Sum.inr 916) = Sparse.eval nodeValue916 (mixedVector B) := by
    change mixedMoment B node916 node916Labels = _
    exact sound916 B hB hF
  have h1007 : mixedVector B (Sum.inr 1007) = Sparse.eval nodeValue1007 (mixedVector B) := by
    change mixedMoment B node1007 node1007Labels = _
    exact sound1007 B hB hF
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h1074 : mixedVector B (Sum.inr 1074) = Sparse.eval nodeValue1074 (mixedVector B) := by
    change mixedMoment B node1074 node1074Labels = _
    exact sound1074 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1362, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h594, h916, h1007, h1037, h1074, h4081, reducedSource1181] using sourceEq1362 B hB

theorem rowSound1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1181 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1181, numericCheck1181, reducedZero1181 B hB hF, mul_zero]

theorem reducedZero1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1182 (mixedVector B) = 0 := by
  have h1033 : mixedVector B (Sum.inr 1033) = Sparse.eval nodeValue1033 (mixedVector B) := by
    change mixedMoment B node1033 node1033Labels = _
    exact sound1033 B hB hF
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h1048 : mixedVector B (Sum.inr 1048) = Sparse.eval nodeValue1048 (mixedVector B) := by
    change mixedMoment B node1048 node1048Labels = _
    exact sound1048 B hB hF
  have h1074 : mixedVector B (Sum.inr 1074) = Sparse.eval nodeValue1074 (mixedVector B) := by
    change mixedMoment B node1074 node1074Labels = _
    exact sound1074 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1363, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1033, h1037, h1048, h1074, h2261, h4081, reducedSource1182] using sourceEq1363 B hB

theorem rowSound1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1182 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1182, numericCheck1182, reducedZero1182 B hB hF, mul_zero]

theorem reducedZero1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1183 (mixedVector B) = 0 := by
  have h731 : mixedVector B (Sum.inr 731) = Sparse.eval nodeValue731 (mixedVector B) := by
    change mixedMoment B node731 node731Labels = _
    exact sound731 B hB hF
  have h735 : mixedVector B (Sum.inr 735) = Sparse.eval nodeValue735 (mixedVector B) := by
    change mixedMoment B node735 node735Labels = _
    exact sound735 B hB hF
  have h741 : mixedVector B (Sum.inr 741) = Sparse.eval nodeValue741 (mixedVector B) := by
    change mixedMoment B node741 node741Labels = _
    exact sound741 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1364, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h731, h735, h741, h809, h1647, h4070, reducedSource1183] using sourceEq1364 B hB

theorem rowSound1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1183 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1183, numericCheck1183, reducedZero1183 B hB hF, mul_zero]

theorem sourceRowsAt1168 : MixedData.sourceRows (1168 : Fin 2425) =
    MixedData.row1168 := by decide +kernel

theorem sourceRowsAt1169 : MixedData.sourceRows (1169 : Fin 2425) =
    MixedData.row1169 := by decide +kernel

theorem sourceRowsAt1170 : MixedData.sourceRows (1170 : Fin 2425) =
    MixedData.row1170 := by decide +kernel

theorem sourceRowsAt1171 : MixedData.sourceRows (1171 : Fin 2425) =
    MixedData.row1171 := by decide +kernel

theorem sourceRowsAt1172 : MixedData.sourceRows (1172 : Fin 2425) =
    MixedData.row1172 := by decide +kernel

theorem sourceRowsAt1173 : MixedData.sourceRows (1173 : Fin 2425) =
    MixedData.row1173 := by decide +kernel

theorem sourceRowsAt1174 : MixedData.sourceRows (1174 : Fin 2425) =
    MixedData.row1174 := by decide +kernel

theorem sourceRowsAt1175 : MixedData.sourceRows (1175 : Fin 2425) =
    MixedData.row1175 := by decide +kernel

theorem sourceRowsAt1176 : MixedData.sourceRows (1176 : Fin 2425) =
    MixedData.row1176 := by decide +kernel

theorem sourceRowsAt1177 : MixedData.sourceRows (1177 : Fin 2425) =
    MixedData.row1177 := by decide +kernel

theorem sourceRowsAt1178 : MixedData.sourceRows (1178 : Fin 2425) =
    MixedData.row1178 := by decide +kernel

theorem sourceRowsAt1179 : MixedData.sourceRows (1179 : Fin 2425) =
    MixedData.row1179 := by decide +kernel

theorem sourceRowsAt1180 : MixedData.sourceRows (1180 : Fin 2425) =
    MixedData.row1180 := by decide +kernel

theorem sourceRowsAt1181 : MixedData.sourceRows (1181 : Fin 2425) =
    MixedData.row1181 := by decide +kernel

theorem sourceRowsAt1182 : MixedData.sourceRows (1182 : Fin 2425) =
    MixedData.row1182 := by decide +kernel

theorem sourceRowsAt1183 : MixedData.sourceRows (1183 : Fin 2425) =
    MixedData.row1183 := by decide +kernel

theorem chunkSound73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 73) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1168 ∨ k.val = 1169 ∨ k.val = 1170 ∨ k.val = 1171 ∨ k.val = 1172 ∨ k.val = 1173 ∨ k.val = 1174 ∨ k.val = 1175 ∨ k.val = 1176 ∨ k.val = 1177 ∨ k.val = 1178 ∨ k.val = 1179 ∨ k.val = 1180 ∨ k.val = 1181 ∨ k.val = 1182 ∨ k.val = 1183 := by omega
  rcases heq with h1168 | h1169 | h1170 | h1171 | h1172 | h1173 | h1174 | h1175 | h1176 | h1177 | h1178 | h1179 | h1180 | h1181 | h1182 | h1183
  · have he : k = (1168 : Fin 2425) := Fin.ext h1168
    subst k
    rw [sourceRowsAt1168]
    exact rowSound1168 B hB hF
  · have he : k = (1169 : Fin 2425) := Fin.ext h1169
    subst k
    rw [sourceRowsAt1169]
    exact rowSound1169 B hB hF
  · have he : k = (1170 : Fin 2425) := Fin.ext h1170
    subst k
    rw [sourceRowsAt1170]
    exact rowSound1170 B hB hF
  · have he : k = (1171 : Fin 2425) := Fin.ext h1171
    subst k
    rw [sourceRowsAt1171]
    exact rowSound1171 B hB hF
  · have he : k = (1172 : Fin 2425) := Fin.ext h1172
    subst k
    rw [sourceRowsAt1172]
    exact rowSound1172 B hB hF
  · have he : k = (1173 : Fin 2425) := Fin.ext h1173
    subst k
    rw [sourceRowsAt1173]
    exact rowSound1173 B hB hF
  · have he : k = (1174 : Fin 2425) := Fin.ext h1174
    subst k
    rw [sourceRowsAt1174]
    exact rowSound1174 B hB hF
  · have he : k = (1175 : Fin 2425) := Fin.ext h1175
    subst k
    rw [sourceRowsAt1175]
    exact rowSound1175 B hB hF
  · have he : k = (1176 : Fin 2425) := Fin.ext h1176
    subst k
    rw [sourceRowsAt1176]
    exact rowSound1176 B hB hF
  · have he : k = (1177 : Fin 2425) := Fin.ext h1177
    subst k
    rw [sourceRowsAt1177]
    exact rowSound1177 B hB hF
  · have he : k = (1178 : Fin 2425) := Fin.ext h1178
    subst k
    rw [sourceRowsAt1178]
    exact rowSound1178 B hB hF
  · have he : k = (1179 : Fin 2425) := Fin.ext h1179
    subst k
    rw [sourceRowsAt1179]
    exact rowSound1179 B hB hF
  · have he : k = (1180 : Fin 2425) := Fin.ext h1180
    subst k
    rw [sourceRowsAt1180]
    exact rowSound1180 B hB hF
  · have he : k = (1181 : Fin 2425) := Fin.ext h1181
    subst k
    rw [sourceRowsAt1181]
    exact rowSound1181 B hB hF
  · have he : k = (1182 : Fin 2425) := Fin.ext h1182
    subst k
    rw [sourceRowsAt1182]
    exact rowSound1182 B hB hF
  · have he : k = (1183 : Fin 2425) := Fin.ext h1183
    subst k
    rw [sourceRowsAt1183]
    exact rowSound1183 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
