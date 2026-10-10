import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources49

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1344 (mixedVector B) = 0 := by
  have h604 : mixedVector B (Sum.inr 604) = Sparse.eval nodeValue604 (mixedVector B) := by
    change mixedMoment B node604 node604Labels = _
    exact sound604 B hB hF
  have h923 : mixedVector B (Sum.inr 923) = Sparse.eval nodeValue923 (mixedVector B) := by
    change mixedMoment B node923 node923Labels = _
    exact sound923 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1578, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h604, h923, h1042, h1058, h1079, h1087, h4084, reducedSource1344] using sourceEq1578 B hB

theorem rowSound1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1344 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1344, numericCheck1344, reducedZero1344 B hB hF, mul_zero]

theorem reducedZero1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1345 (mixedVector B) = 0 := by
  have h1335 : mixedVector B (Sum.inr 1335) = Sparse.eval nodeValue1335 (mixedVector B) := by
    change mixedMoment B node1335 node1335Labels = _
    exact sound1335 B hB hF
  have h1337 : mixedVector B (Sum.inr 1337) = Sparse.eval nodeValue1337 (mixedVector B) := by
    change mixedMoment B node1337 node1337Labels = _
    exact sound1337 B hB hF
  have h1338 : mixedVector B (Sum.inr 1338) = Sparse.eval nodeValue1338 (mixedVector B) := by
    change mixedMoment B node1338 node1338Labels = _
    exact sound1338 B hB hF
  have h1347 : mixedVector B (Sum.inr 1347) = Sparse.eval nodeValue1347 (mixedVector B) := by
    change mixedMoment B node1347 node1347Labels = _
    exact sound1347 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1579, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1335, h1337, h1338, h1347, h1406, h2954, h4091, reducedSource1345] using sourceEq1579 B hB

theorem rowSound1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1345 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1345, numericCheck1345, reducedZero1345 B hB hF, mul_zero]

theorem reducedZero1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1346 (mixedVector B) = 0 := by
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3287 : mixedVector B (Sum.inr 3287) = Sparse.eval nodeValue3287 (mixedVector B) := by
    change mixedMoment B node3287 node3287Labels = _
    exact sound3287 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1580, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1714, h2502, h3285, h3287, h3293, h3305, h4069, reducedSource1346] using sourceEq1580 B hB

theorem rowSound1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1346 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1346, numericCheck1346, reducedZero1346 B hB hF, mul_zero]

theorem reducedZero1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1347 (mixedVector B) = 0 := by
  have h824 : mixedVector B (Sum.inr 824) = Sparse.eval nodeValue824 (mixedVector B) := by
    change mixedMoment B node824 node824Labels = _
    exact sound824 B hB hF
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1581, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h824, h1607, h1656, h1714, h1737, h1739, h4069, reducedSource1347] using sourceEq1581 B hB

theorem rowSound1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1347 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1347, numericCheck1347, reducedZero1347 B hB hF, mul_zero]

theorem reducedZero1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1348 (mixedVector B) = 0 := by
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1582, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1713, h1714, h1715, h1724, h1737, h3293, h4069, reducedSource1348] using sourceEq1582 B hB

theorem rowSound1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1348 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1348, numericCheck1348, reducedZero1348 B hB hF, mul_zero]

theorem reducedZero1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1349 (mixedVector B) = 0 := by
  have h807 : mixedVector B (Sum.inr 807) = Sparse.eval nodeValue807 (mixedVector B) := by
    change mixedMoment B node807 node807Labels = _
    exact sound807 B hB hF
  have h1598 : mixedVector B (Sum.inr 1598) = Sparse.eval nodeValue1598 (mixedVector B) := by
    change mixedMoment B node1598 node1598Labels = _
    exact sound1598 B hB hF
  have h1646 : mixedVector B (Sum.inr 1646) = Sparse.eval nodeValue1646 (mixedVector B) := by
    change mixedMoment B node1646 node1646Labels = _
    exact sound1646 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1583, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h807, h1598, h1646, h1714, h1724, h1728, h4069, reducedSource1349] using sourceEq1583 B hB

theorem rowSound1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1349 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1349, numericCheck1349, reducedZero1349 B hB hF, mul_zero]

theorem reducedZero1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1350 (mixedVector B) = 0 := by
  have h601 : mixedVector B (Sum.inr 601) = Sparse.eval nodeValue601 (mixedVector B) := by
    change mixedMoment B node601 node601Labels = _
    exact sound601 B hB hF
  have h920 : mixedVector B (Sum.inr 920) = Sparse.eval nodeValue920 (mixedVector B) := by
    change mixedMoment B node920 node920Labels = _
    exact sound920 B hB hF
  have h1057 : mixedVector B (Sum.inr 1057) = Sparse.eval nodeValue1057 (mixedVector B) := by
    change mixedMoment B node1057 node1057Labels = _
    exact sound1057 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1584, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h601, h920, h1057, h1079, h1083, h4084, reducedSource1350] using sourceEq1584 B hB

theorem rowSound1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1350 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1350, numericCheck1350, reducedZero1350 B hB hF, mul_zero]

theorem reducedZero1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1351 (mixedVector B) = 0 := by
  have h1316 : mixedVector B (Sum.inr 1316) = Sparse.eval nodeValue1316 (mixedVector B) := by
    change mixedMoment B node1316 node1316Labels = _
    exact sound1316 B hB hF
  have h1320 : mixedVector B (Sum.inr 1320) = Sparse.eval nodeValue1320 (mixedVector B) := by
    change mixedMoment B node1320 node1320Labels = _
    exact sound1320 B hB hF
  have h1322 : mixedVector B (Sum.inr 1322) = Sparse.eval nodeValue1322 (mixedVector B) := by
    change mixedMoment B node1322 node1322Labels = _
    exact sound1322 B hB hF
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1585, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1316, h1320, h1322, h1370, h2884, h4091, reducedSource1351] using sourceEq1585 B hB

theorem rowSound1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1351 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1351, numericCheck1351, reducedZero1351 B hB hF, mul_zero]

theorem reducedZero1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1352 (mixedVector B) = 0 := by
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h3241 : mixedVector B (Sum.inr 3241) = Sparse.eval nodeValue3241 (mixedVector B) := by
    change mixedMoment B node3241 node3241Labels = _
    exact sound3241 B hB hF
  have h3245 : mixedVector B (Sum.inr 3245) = Sparse.eval nodeValue3245 (mixedVector B) := by
    change mixedMoment B node3245 node3245Labels = _
    exact sound3245 B hB hF
  have h3246 : mixedVector B (Sum.inr 3246) = Sparse.eval nodeValue3246 (mixedVector B) := by
    change mixedMoment B node3246 node3246Labels = _
    exact sound3246 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1586, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1709, h3241, h3245, h3246, h3299, h4069, reducedSource1352] using sourceEq1586 B hB

theorem rowSound1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1352 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1352, numericCheck1352, reducedZero1352 B hB hF, mul_zero]

theorem reducedZero1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1353 (mixedVector B) = 0 := by
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1587, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1705, h1707, h1709, h1724, h3299, h4069, reducedSource1353] using sourceEq1587 B hB

theorem rowSound1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1353 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1353, numericCheck1353, reducedZero1353 B hB hF, mul_zero]

theorem reducedZero1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1354 (mixedVector B) = 0 := by
  have h811 : mixedVector B (Sum.inr 811) = Sparse.eval nodeValue811 (mixedVector B) := by
    change mixedMoment B node811 node811Labels = _
    exact sound811 B hB hF
  have h1601 : mixedVector B (Sum.inr 1601) = Sparse.eval nodeValue1601 (mixedVector B) := by
    change mixedMoment B node1601 node1601Labels = _
    exact sound1601 B hB hF
  have h1649 : mixedVector B (Sum.inr 1649) = Sparse.eval nodeValue1649 (mixedVector B) := by
    change mixedMoment B node1649 node1649Labels = _
    exact sound1649 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1588, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h811, h1601, h1649, h1709, h1715, h1724, h4069, reducedSource1354] using sourceEq1588 B hB

theorem rowSound1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1354 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1354, numericCheck1354, reducedZero1354 B hB hF, mul_zero]

theorem reducedZero1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1355 (mixedVector B) = 0 := by
  have h1314 : mixedVector B (Sum.inr 1314) = Sparse.eval nodeValue1314 (mixedVector B) := by
    change mixedMoment B node1314 node1314Labels = _
    exact sound1314 B hB hF
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h1318 : mixedVector B (Sum.inr 1318) = Sparse.eval nodeValue1318 (mixedVector B) := by
    change mixedMoment B node1318 node1318Labels = _
    exact sound1318 B hB hF
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1590, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1314, h1317, h1318, h1321, h1367, h2881, h4092, reducedSource1355] using sourceEq1590 B hB

theorem rowSound1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1355 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1355, numericCheck1355, reducedZero1355 B hB hF, mul_zero]

theorem reducedZero1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1356 (mixedVector B) = 0 := by
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h2466 : mixedVector B (Sum.inr 2466) = Sparse.eval nodeValue2466 (mixedVector B) := by
    change mixedMoment B node2466 node2466Labels = _
    exact sound2466 B hB hF
  have h3238 : mixedVector B (Sum.inr 3238) = Sparse.eval nodeValue3238 (mixedVector B) := by
    change mixedMoment B node3238 node3238Labels = _
    exact sound3238 B hB hF
  have h3240 : mixedVector B (Sum.inr 3240) = Sparse.eval nodeValue3240 (mixedVector B) := by
    change mixedMoment B node3240 node3240Labels = _
    exact sound3240 B hB hF
  have h3245 : mixedVector B (Sum.inr 3245) = Sparse.eval nodeValue3245 (mixedVector B) := by
    change mixedMoment B node3245 node3245Labels = _
    exact sound3245 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1591, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1715, h2466, h3238, h3240, h3245, h3293, h4069, reducedSource1356] using sourceEq1591 B hB

theorem rowSound1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1356 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1356, numericCheck1356, reducedZero1356 B hB hF, mul_zero]

theorem reducedZero1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1357 (mixedVector B) = 0 := by
  have h827 : mixedVector B (Sum.inr 827) = Sparse.eval nodeValue827 (mixedVector B) := by
    change mixedMoment B node827 node827Labels = _
    exact sound827 B hB hF
  have h1609 : mixedVector B (Sum.inr 1609) = Sparse.eval nodeValue1609 (mixedVector B) := by
    change mixedMoment B node1609 node1609Labels = _
    exact sound1609 B hB hF
  have h1658 : mixedVector B (Sum.inr 1658) = Sparse.eval nodeValue1658 (mixedVector B) := by
    change mixedMoment B node1658 node1658Labels = _
    exact sound1658 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1592, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h827, h1609, h1658, h1715, h1737, h4069, reducedSource1357] using sourceEq1592 B hB

theorem rowSound1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1357 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1357, numericCheck1357, reducedZero1357 B hB hF, mul_zero]

theorem reducedZero1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1358 (mixedVector B) = 0 := by
  have h578 : mixedVector B (Sum.inr 578) = Sparse.eval nodeValue578 (mixedVector B) := by
    change mixedMoment B node578 node578Labels = _
    exact sound578 B hB hF
  have h942 : mixedVector B (Sum.inr 942) = Sparse.eval nodeValue942 (mixedVector B) := by
    change mixedMoment B node942 node942Labels = _
    exact sound942 B hB hF
  have h1020 : mixedVector B (Sum.inr 1020) = Sparse.eval nodeValue1020 (mixedVector B) := by
    change mixedMoment B node1020 node1020Labels = _
    exact sound1020 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1594, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h578, h942, h1020, h1039, h1041, h4083, reducedSource1358] using sourceEq1594 B hB

theorem rowSound1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1358 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1358, numericCheck1358, reducedZero1358 B hB hF, mul_zero]

theorem reducedZero1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1359 (mixedVector B) = 0 := by
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h3281 : mixedVector B (Sum.inr 3281) = Sparse.eval nodeValue3281 (mixedVector B) := by
    change mixedMoment B node3281 node3281Labels = _
    exact sound3281 B hB hF
  have h3282 : mixedVector B (Sum.inr 3282) = Sparse.eval nodeValue3282 (mixedVector B) := by
    change mixedMoment B node3282 node3282Labels = _
    exact sound3282 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1595, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1705, h3281, h3282, h3299, h4069, reducedSource1359] using sourceEq1595 B hB

theorem rowSound1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1359 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1359, numericCheck1359, reducedZero1359 B hB hF, mul_zero]

theorem sourceRowsAt1344 : MixedData.sourceRows (1344 : Fin 2425) =
    MixedData.row1344 := by decide +kernel

theorem sourceRowsAt1345 : MixedData.sourceRows (1345 : Fin 2425) =
    MixedData.row1345 := by decide +kernel

theorem sourceRowsAt1346 : MixedData.sourceRows (1346 : Fin 2425) =
    MixedData.row1346 := by decide +kernel

theorem sourceRowsAt1347 : MixedData.sourceRows (1347 : Fin 2425) =
    MixedData.row1347 := by decide +kernel

theorem sourceRowsAt1348 : MixedData.sourceRows (1348 : Fin 2425) =
    MixedData.row1348 := by decide +kernel

theorem sourceRowsAt1349 : MixedData.sourceRows (1349 : Fin 2425) =
    MixedData.row1349 := by decide +kernel

theorem sourceRowsAt1350 : MixedData.sourceRows (1350 : Fin 2425) =
    MixedData.row1350 := by decide +kernel

theorem sourceRowsAt1351 : MixedData.sourceRows (1351 : Fin 2425) =
    MixedData.row1351 := by decide +kernel

theorem sourceRowsAt1352 : MixedData.sourceRows (1352 : Fin 2425) =
    MixedData.row1352 := by decide +kernel

theorem sourceRowsAt1353 : MixedData.sourceRows (1353 : Fin 2425) =
    MixedData.row1353 := by decide +kernel

theorem sourceRowsAt1354 : MixedData.sourceRows (1354 : Fin 2425) =
    MixedData.row1354 := by decide +kernel

theorem sourceRowsAt1355 : MixedData.sourceRows (1355 : Fin 2425) =
    MixedData.row1355 := by decide +kernel

theorem sourceRowsAt1356 : MixedData.sourceRows (1356 : Fin 2425) =
    MixedData.row1356 := by decide +kernel

theorem sourceRowsAt1357 : MixedData.sourceRows (1357 : Fin 2425) =
    MixedData.row1357 := by decide +kernel

theorem sourceRowsAt1358 : MixedData.sourceRows (1358 : Fin 2425) =
    MixedData.row1358 := by decide +kernel

theorem sourceRowsAt1359 : MixedData.sourceRows (1359 : Fin 2425) =
    MixedData.row1359 := by decide +kernel

theorem chunkSound84 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 84) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1344 ∨ k.val = 1345 ∨ k.val = 1346 ∨ k.val = 1347 ∨ k.val = 1348 ∨ k.val = 1349 ∨ k.val = 1350 ∨ k.val = 1351 ∨ k.val = 1352 ∨ k.val = 1353 ∨ k.val = 1354 ∨ k.val = 1355 ∨ k.val = 1356 ∨ k.val = 1357 ∨ k.val = 1358 ∨ k.val = 1359 := by omega
  rcases heq with h1344 | h1345 | h1346 | h1347 | h1348 | h1349 | h1350 | h1351 | h1352 | h1353 | h1354 | h1355 | h1356 | h1357 | h1358 | h1359
  · have he : k = (1344 : Fin 2425) := Fin.ext h1344
    subst k
    rw [sourceRowsAt1344]
    exact rowSound1344 B hB hF
  · have he : k = (1345 : Fin 2425) := Fin.ext h1345
    subst k
    rw [sourceRowsAt1345]
    exact rowSound1345 B hB hF
  · have he : k = (1346 : Fin 2425) := Fin.ext h1346
    subst k
    rw [sourceRowsAt1346]
    exact rowSound1346 B hB hF
  · have he : k = (1347 : Fin 2425) := Fin.ext h1347
    subst k
    rw [sourceRowsAt1347]
    exact rowSound1347 B hB hF
  · have he : k = (1348 : Fin 2425) := Fin.ext h1348
    subst k
    rw [sourceRowsAt1348]
    exact rowSound1348 B hB hF
  · have he : k = (1349 : Fin 2425) := Fin.ext h1349
    subst k
    rw [sourceRowsAt1349]
    exact rowSound1349 B hB hF
  · have he : k = (1350 : Fin 2425) := Fin.ext h1350
    subst k
    rw [sourceRowsAt1350]
    exact rowSound1350 B hB hF
  · have he : k = (1351 : Fin 2425) := Fin.ext h1351
    subst k
    rw [sourceRowsAt1351]
    exact rowSound1351 B hB hF
  · have he : k = (1352 : Fin 2425) := Fin.ext h1352
    subst k
    rw [sourceRowsAt1352]
    exact rowSound1352 B hB hF
  · have he : k = (1353 : Fin 2425) := Fin.ext h1353
    subst k
    rw [sourceRowsAt1353]
    exact rowSound1353 B hB hF
  · have he : k = (1354 : Fin 2425) := Fin.ext h1354
    subst k
    rw [sourceRowsAt1354]
    exact rowSound1354 B hB hF
  · have he : k = (1355 : Fin 2425) := Fin.ext h1355
    subst k
    rw [sourceRowsAt1355]
    exact rowSound1355 B hB hF
  · have he : k = (1356 : Fin 2425) := Fin.ext h1356
    subst k
    rw [sourceRowsAt1356]
    exact rowSound1356 B hB hF
  · have he : k = (1357 : Fin 2425) := Fin.ext h1357
    subst k
    rw [sourceRowsAt1357]
    exact rowSound1357 B hB hF
  · have he : k = (1358 : Fin 2425) := Fin.ext h1358
    subst k
    rw [sourceRowsAt1358]
    exact rowSound1358 B hB hF
  · have he : k = (1359 : Fin 2425) := Fin.ext h1359
    subst k
    rw [sourceRowsAt1359]
    exact rowSound1359 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
