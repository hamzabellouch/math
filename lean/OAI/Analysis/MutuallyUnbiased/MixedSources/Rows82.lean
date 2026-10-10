import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources48

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1312 (mixedVector B) = 0 := by
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1312 : mixedVector B (Sum.inr 1312) = Sparse.eval nodeValue1312 (mixedVector B) := by
    change mixedMoment B node1312 node1312Labels = _
    exact sound1312 B hB hF
  have h1363 : mixedVector B (Sum.inr 1363) = Sparse.eval nodeValue1363 (mixedVector B) := by
    change mixedMoment B node1363 node1363Labels = _
    exact sound1363 B hB hF
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h1381 : mixedVector B (Sum.inr 1381) = Sparse.eval nodeValue1381 (mixedVector B) := by
    change mixedMoment B node1381 node1381Labels = _
    exact sound1381 B hB hF
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h1401 : mixedVector B (Sum.inr 1401) = Sparse.eval nodeValue1401 (mixedVector B) := by
    change mixedMoment B node1401 node1401Labels = _
    exact sound1401 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1420 : mixedVector B (Sum.inr 1420) = Sparse.eval nodeValue1420 (mixedVector B) := by
    change mixedMoment B node1420 node1420Labels = _
    exact sound1420 B hB hF
  have h1455 : mixedVector B (Sum.inr 1455) = Sparse.eval nodeValue1455 (mixedVector B) := by
    change mixedMoment B node1455 node1455Labels = _
    exact sound1455 B hB hF
  have h1473 : mixedVector B (Sum.inr 1473) = Sparse.eval nodeValue1473 (mixedVector B) := by
    change mixedMoment B node1473 node1473Labels = _
    exact sound1473 B hB hF
  have h1479 : mixedVector B (Sum.inr 1479) = Sparse.eval nodeValue1479 (mixedVector B) := by
    change mixedMoment B node1479 node1479Labels = _
    exact sound1479 B hB hF
  have h1486 : mixedVector B (Sum.inr 1486) = Sparse.eval nodeValue1486 (mixedVector B) := by
    change mixedMoment B node1486 node1486Labels = _
    exact sound1486 B hB hF
  simpa only [sourceForm1533, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1220, h1246, h1312, h1363, h1375, h1381, h1391, h1401, h1419, h1420, h1455, h1473, h1479, h1486, reducedSource1312] using sourceEq1533 B hB

theorem rowSound1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1312 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1312, numericCheck1312, reducedZero1312 B hB hF, mul_zero]

theorem reducedZero1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1313 (mixedVector B) = 0 := by
  have h984 : mixedVector B (Sum.inr 984) = Sparse.eval nodeValue984 (mixedVector B) := by
    change mixedMoment B node984 node984Labels = _
    exact sound984 B hB hF
  have h1917 : mixedVector B (Sum.inr 1917) = Sparse.eval nodeValue1917 (mixedVector B) := by
    change mixedMoment B node1917 node1917Labels = _
    exact sound1917 B hB hF
  have h1989 : mixedVector B (Sum.inr 1989) = Sparse.eval nodeValue1989 (mixedVector B) := by
    change mixedMoment B node1989 node1989Labels = _
    exact sound1989 B hB hF
  have h2081 : mixedVector B (Sum.inr 2081) = Sparse.eval nodeValue2081 (mixedVector B) := by
    change mixedMoment B node2081 node2081Labels = _
    exact sound2081 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1534, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h984, h1917, h1989, h2081, h2203, h2207, h4081, reducedSource1313] using sourceEq1534 B hB

theorem rowSound1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1313 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1313, numericCheck1313, reducedZero1313 B hB hF, mul_zero]

theorem reducedZero1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1314 (mixedVector B) = 0 := by
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1918 : mixedVector B (Sum.inr 1918) = Sparse.eval nodeValue1918 (mixedVector B) := by
    change mixedMoment B node1918 node1918Labels = _
    exact sound1918 B hB hF
  have h1990 : mixedVector B (Sum.inr 1990) = Sparse.eval nodeValue1990 (mixedVector B) := by
    change mixedMoment B node1990 node1990Labels = _
    exact sound1990 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1535, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h985, h1918, h1990, h2082, h2205, h2206, h4080, reducedSource1314] using sourceEq1535 B hB

theorem rowSound1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1314 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1314, numericCheck1314, reducedZero1314 B hB hF, mul_zero]

theorem reducedZero1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1315 (mixedVector B) = 0 := by
  have h866 : mixedVector B (Sum.inr 866) = Sparse.eval nodeValue866 (mixedVector B) := by
    change mixedMoment B node866 node866Labels = _
    exact sound866 B hB hF
  have h873 : mixedVector B (Sum.inr 873) = Sparse.eval nodeValue873 (mixedVector B) := by
    change mixedMoment B node873 node873Labels = _
    exact sound873 B hB hF
  have h874 : mixedVector B (Sum.inr 874) = Sparse.eval nodeValue874 (mixedVector B) := by
    change mixedMoment B node874 node874Labels = _
    exact sound874 B hB hF
  have h889 : mixedVector B (Sum.inr 889) = Sparse.eval nodeValue889 (mixedVector B) := by
    change mixedMoment B node889 node889Labels = _
    exact sound889 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1918 : mixedVector B (Sum.inr 1918) = Sparse.eval nodeValue1918 (mixedVector B) := by
    change mixedMoment B node1918 node1918Labels = _
    exact sound1918 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1537, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h866, h873, h874, h889, h985, h1918, h4080, reducedSource1315] using sourceEq1537 B hB

theorem rowSound1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1315 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1315, numericCheck1315, reducedZero1315 B hB hF, mul_zero]

theorem reducedZero1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1316 (mixedVector B) = 0 := by
  have h710 : mixedVector B (Sum.inr 710) = Sparse.eval nodeValue710 (mixedVector B) := by
    change mixedMoment B node710 node710Labels = _
    exact sound710 B hB hF
  have h715 : mixedVector B (Sum.inr 715) = Sparse.eval nodeValue715 (mixedVector B) := by
    change mixedMoment B node715 node715Labels = _
    exact sound715 B hB hF
  have h717 : mixedVector B (Sum.inr 717) = Sparse.eval nodeValue717 (mixedVector B) := by
    change mixedMoment B node717 node717Labels = _
    exact sound717 B hB hF
  have h724 : mixedVector B (Sum.inr 724) = Sparse.eval nodeValue724 (mixedVector B) := by
    change mixedMoment B node724 node724Labels = _
    exact sound724 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h1618 : mixedVector B (Sum.inr 1618) = Sparse.eval nodeValue1618 (mixedVector B) := by
    change mixedMoment B node1618 node1618Labels = _
    exact sound1618 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1538, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h710, h715, h717, h724, h852, h1618, h4071, reducedSource1316] using sourceEq1538 B hB

theorem rowSound1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1316 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1316, numericCheck1316, reducedZero1316 B hB hF, mul_zero]

theorem reducedZero1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1317 (mixedVector B) = 0 := by
  have h4179 : mixedVector B (Sum.inr 4179) = Sparse.eval nodeValue4179 (mixedVector B) := by
    change mixedMoment B node4179 node4179Labels = _
    exact sound4179 B hB hF
  have h4190 : mixedVector B (Sum.inr 4190) = Sparse.eval nodeValue4190 (mixedVector B) := by
    change mixedMoment B node4190 node4190Labels = _
    exact sound4190 B hB hF
  have h4193 : mixedVector B (Sum.inr 4193) = Sparse.eval nodeValue4193 (mixedVector B) := by
    change mixedMoment B node4193 node4193Labels = _
    exact sound4193 B hB hF
  have h4348 : mixedVector B (Sum.inr 4348) = Sparse.eval nodeValue4348 (mixedVector B) := by
    change mixedMoment B node4348 node4348Labels = _
    exact sound4348 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4362 : mixedVector B (Sum.inr 4362) = Sparse.eval nodeValue4362 (mixedVector B) := by
    change mixedMoment B node4362 node4362Labels = _
    exact sound4362 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4500 : mixedVector B (Sum.inr 4500) = Sparse.eval nodeValue4500 (mixedVector B) := by
    change mixedMoment B node4500 node4500Labels = _
    exact sound4500 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4508 : mixedVector B (Sum.inr 4508) = Sparse.eval nodeValue4508 (mixedVector B) := by
    change mixedMoment B node4508 node4508Labels = _
    exact sound4508 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  simpa only [sourceForm1540, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4179, h4190, h4193, h4348, h4359, h4362, h4496, h4500, h4501, h4508, h4845, h4897, h4899, reducedSource1317] using sourceEq1540 B hB

theorem rowSound1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1317 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1317, numericCheck1317, reducedZero1317 B hB hF, mul_zero]

theorem reducedZero1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1318 (mixedVector B) = 0 := by
  have h653 : mixedVector B (Sum.inr 653) = Sparse.eval nodeValue653 (mixedVector B) := by
    change mixedMoment B node653 node653Labels = _
    exact sound653 B hB hF
  have h654 : mixedVector B (Sum.inr 654) = Sparse.eval nodeValue654 (mixedVector B) := by
    change mixedMoment B node654 node654Labels = _
    exact sound654 B hB hF
  have h655 : mixedVector B (Sum.inr 655) = Sparse.eval nodeValue655 (mixedVector B) := by
    change mixedMoment B node655 node655Labels = _
    exact sound655 B hB hF
  have h1347 : mixedVector B (Sum.inr 1347) = Sparse.eval nodeValue1347 (mixedVector B) := by
    change mixedMoment B node1347 node1347Labels = _
    exact sound1347 B hB hF
  have h1348 : mixedVector B (Sum.inr 1348) = Sparse.eval nodeValue1348 (mixedVector B) := by
    change mixedMoment B node1348 node1348Labels = _
    exact sound1348 B hB hF
  have h1349 : mixedVector B (Sum.inr 1349) = Sparse.eval nodeValue1349 (mixedVector B) := by
    change mixedMoment B node1349 node1349Labels = _
    exact sound1349 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h1438 : mixedVector B (Sum.inr 1438) = Sparse.eval nodeValue1438 (mixedVector B) := by
    change mixedMoment B node1438 node1438Labels = _
    exact sound1438 B hB hF
  have h1451 : mixedVector B (Sum.inr 1451) = Sparse.eval nodeValue1451 (mixedVector B) := by
    change mixedMoment B node1451 node1451Labels = _
    exact sound1451 B hB hF
  have h1452 : mixedVector B (Sum.inr 1452) = Sparse.eval nodeValue1452 (mixedVector B) := by
    change mixedMoment B node1452 node1452Labels = _
    exact sound1452 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  have h3095 : mixedVector B (Sum.inr 3095) = Sparse.eval nodeValue3095 (mixedVector B) := by
    change mixedMoment B node3095 node3095Labels = _
    exact sound3095 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  simpa only [sourceForm1541, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h653, h654, h655, h1347, h1348, h1349, h1436, h1438, h1451, h1452, h2778, h3095, h3114, reducedSource1318] using sourceEq1541 B hB

theorem rowSound1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1318 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1318, numericCheck1318, reducedZero1318 B hB hF, mul_zero]

theorem reducedZero1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1319 (mixedVector B) = 0 := by
  have h1513 : mixedVector B (Sum.inr 1513) = Sparse.eval nodeValue1513 (mixedVector B) := by
    change mixedMoment B node1513 node1513Labels = _
    exact sound1513 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1531 : mixedVector B (Sum.inr 1531) = Sparse.eval nodeValue1531 (mixedVector B) := by
    change mixedMoment B node1531 node1531Labels = _
    exact sound1531 B hB hF
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1687 : mixedVector B (Sum.inr 1687) = Sparse.eval nodeValue1687 (mixedVector B) := by
    change mixedMoment B node1687 node1687Labels = _
    exact sound1687 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  simpa only [sourceForm1542, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1513, h1527, h1531, h1669, h1683, h1687, h1710, h1716, h1730, h1747, h2218, h2268, h2281, reducedSource1319] using sourceEq1542 B hB

theorem rowSound1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1319 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1319, numericCheck1319, reducedZero1319 B hB hF, mul_zero]

theorem reducedZero1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1320 (mixedVector B) = 0 := by
  have h607 : mixedVector B (Sum.inr 607) = Sparse.eval nodeValue607 (mixedVector B) := by
    change mixedMoment B node607 node607Labels = _
    exact sound607 B hB hF
  have h618 : mixedVector B (Sum.inr 618) = Sparse.eval nodeValue618 (mixedVector B) := by
    change mixedMoment B node618 node618Labels = _
    exact sound618 B hB hF
  have h621 : mixedVector B (Sum.inr 621) = Sparse.eval nodeValue621 (mixedVector B) := by
    change mixedMoment B node621 node621Labels = _
    exact sound621 B hB hF
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1543, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h607, h618, h621, h1094, h4085, reducedSource1320] using sourceEq1543 B hB

theorem rowSound1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1320 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1320, numericCheck1320, reducedZero1320 B hB hF, mul_zero]

theorem reducedZero1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1321 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4180 : mixedVector B (Sum.inr 4180) = Sparse.eval nodeValue4180 (mixedVector B) := by
    change mixedMoment B node4180 node4180Labels = _
    exact sound4180 B hB hF
  have h4191 : mixedVector B (Sum.inr 4191) = Sparse.eval nodeValue4191 (mixedVector B) := by
    change mixedMoment B node4191 node4191Labels = _
    exact sound4191 B hB hF
  have h4192 : mixedVector B (Sum.inr 4192) = Sparse.eval nodeValue4192 (mixedVector B) := by
    change mixedMoment B node4192 node4192Labels = _
    exact sound4192 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  simpa only [sourceForm1550, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4180, h4191, h4192, h4349, h4360, h4361, h4498, h4499, h4505, h4507, h4846, h4901, reducedSource1321] using sourceEq1550 B hB

theorem rowSound1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1321 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1321, numericCheck1321, reducedZero1321 B hB hF, mul_zero]

theorem reducedZero1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1322 (mixedVector B) = 0 := by
  have h1519 : mixedVector B (Sum.inr 1519) = Sparse.eval nodeValue1519 (mixedVector B) := by
    change mixedMoment B node1519 node1519Labels = _
    exact sound1519 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h1675 : mixedVector B (Sum.inr 1675) = Sparse.eval nodeValue1675 (mixedVector B) := by
    change mixedMoment B node1675 node1675Labels = _
    exact sound1675 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1551, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1519, h1538, h1539, h1675, h1693, h1694, h1727, h1728, h1754, h1756, h2229, h2293, h4084, reducedSource1322] using sourceEq1551 B hB

theorem rowSound1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1322 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1322, numericCheck1322, reducedZero1322 B hB hF, mul_zero]

theorem reducedZero1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1323 (mixedVector B) = 0 := by
  have h608 : mixedVector B (Sum.inr 608) = Sparse.eval nodeValue608 (mixedVector B) := by
    change mixedMoment B node608 node608Labels = _
    exact sound608 B hB hF
  have h619 : mixedVector B (Sum.inr 619) = Sparse.eval nodeValue619 (mixedVector B) := by
    change mixedMoment B node619 node619Labels = _
    exact sound619 B hB hF
  have h620 : mixedVector B (Sum.inr 620) = Sparse.eval nodeValue620 (mixedVector B) := by
    change mixedMoment B node620 node620Labels = _
    exact sound620 B hB hF
  have h1095 : mixedVector B (Sum.inr 1095) = Sparse.eval nodeValue1095 (mixedVector B) := by
    change mixedMoment B node1095 node1095Labels = _
    exact sound1095 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1552, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h608, h619, h620, h1095, h4084, reducedSource1323] using sourceEq1552 B hB

theorem rowSound1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1323 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1323, numericCheck1323, reducedZero1323 B hB hF, mul_zero]

theorem reducedZero1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1324 (mixedVector B) = 0 := by
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4273 : mixedVector B (Sum.inr 4273) = Sparse.eval nodeValue4273 (mixedVector B) := by
    change mixedMoment B node4273 node4273Labels = _
    exact sound4273 B hB hF
  have h4284 : mixedVector B (Sum.inr 4284) = Sparse.eval nodeValue4284 (mixedVector B) := by
    change mixedMoment B node4284 node4284Labels = _
    exact sound4284 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4431 : mixedVector B (Sum.inr 4431) = Sparse.eval nodeValue4431 (mixedVector B) := by
    change mixedMoment B node4431 node4431Labels = _
    exact sound4431 B hB hF
  have h4432 : mixedVector B (Sum.inr 4432) = Sparse.eval nodeValue4432 (mixedVector B) := by
    change mixedMoment B node4432 node4432Labels = _
    exact sound4432 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  simpa only [sourceForm1553, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4071, h4273, h4284, h4404, h4431, h4432, h4466, h4467, h4510, h4511, h4612, h4627, h4628, reducedSource1324] using sourceEq1553 B hB

theorem rowSound1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1324 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1324, numericCheck1324, reducedZero1324 B hB hF, mul_zero]

theorem reducedZero1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1325 (mixedVector B) = 0 := by
  have h1012 : mixedVector B (Sum.inr 1012) = Sparse.eval nodeValue1012 (mixedVector B) := by
    change mixedMoment B node1012 node1012Labels = _
    exact sound1012 B hB hF
  have h1953 : mixedVector B (Sum.inr 1953) = Sparse.eval nodeValue1953 (mixedVector B) := by
    change mixedMoment B node1953 node1953Labels = _
    exact sound1953 B hB hF
  have h2006 : mixedVector B (Sum.inr 2006) = Sparse.eval nodeValue2006 (mixedVector B) := by
    change mixedMoment B node2006 node2006Labels = _
    exact sound2006 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1554, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1012, h1953, h2006, h2228, h2230, h4081, reducedSource1325] using sourceEq1554 B hB

theorem rowSound1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1325 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1325, numericCheck1325, reducedZero1325 B hB hF, mul_zero]

theorem reducedZero1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1326 (mixedVector B) = 0 := by
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4141 : mixedVector B (Sum.inr 4141) = Sparse.eval nodeValue4141 (mixedVector B) := by
    change mixedMoment B node4141 node4141Labels = _
    exact sound4141 B hB hF
  have h4148 : mixedVector B (Sum.inr 4148) = Sparse.eval nodeValue4148 (mixedVector B) := by
    change mixedMoment B node4148 node4148Labels = _
    exact sound4148 B hB hF
  have h4167 : mixedVector B (Sum.inr 4167) = Sparse.eval nodeValue4167 (mixedVector B) := by
    change mixedMoment B node4167 node4167Labels = _
    exact sound4167 B hB hF
  have h4305 : mixedVector B (Sum.inr 4305) = Sparse.eval nodeValue4305 (mixedVector B) := by
    change mixedMoment B node4305 node4305Labels = _
    exact sound4305 B hB hF
  have h4318 : mixedVector B (Sum.inr 4318) = Sparse.eval nodeValue4318 (mixedVector B) := by
    change mixedMoment B node4318 node4318Labels = _
    exact sound4318 B hB hF
  have h4321 : mixedVector B (Sum.inr 4321) = Sparse.eval nodeValue4321 (mixedVector B) := by
    change mixedMoment B node4321 node4321Labels = _
    exact sound4321 B hB hF
  have h4325 : mixedVector B (Sum.inr 4325) = Sparse.eval nodeValue4325 (mixedVector B) := by
    change mixedMoment B node4325 node4325Labels = _
    exact sound4325 B hB hF
  have h4339 : mixedVector B (Sum.inr 4339) = Sparse.eval nodeValue4339 (mixedVector B) := by
    change mixedMoment B node4339 node4339Labels = _
    exact sound4339 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4428 : mixedVector B (Sum.inr 4428) = Sparse.eval nodeValue4428 (mixedVector B) := by
    change mixedMoment B node4428 node4428Labels = _
    exact sound4428 B hB hF
  have h4491 : mixedVector B (Sum.inr 4491) = Sparse.eval nodeValue4491 (mixedVector B) := by
    change mixedMoment B node4491 node4491Labels = _
    exact sound4491 B hB hF
  have h4790 : mixedVector B (Sum.inr 4790) = Sparse.eval nodeValue4790 (mixedVector B) := by
    change mixedMoment B node4790 node4790Labels = _
    exact sound4790 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  simpa only [sourceForm1556, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4082, h4141, h4148, h4167, h4305, h4318, h4321, h4325, h4339, h4419, h4428, h4491, h4790, h4846, reducedSource1326] using sourceEq1556 B hB

theorem rowSound1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1326 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1326, numericCheck1326, reducedZero1326 B hB hF, mul_zero]

theorem reducedZero1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1327 (mixedVector B) = 0 := by
  have h569 : mixedVector B (Sum.inr 569) = Sparse.eval nodeValue569 (mixedVector B) := by
    change mixedMoment B node569 node569Labels = _
    exact sound569 B hB hF
  have h576 : mixedVector B (Sum.inr 576) = Sparse.eval nodeValue576 (mixedVector B) := by
    change mixedMoment B node576 node576Labels = _
    exact sound576 B hB hF
  have h595 : mixedVector B (Sum.inr 595) = Sparse.eval nodeValue595 (mixedVector B) := by
    change mixedMoment B node595 node595Labels = _
    exact sound595 B hB hF
  have h1013 : mixedVector B (Sum.inr 1013) = Sparse.eval nodeValue1013 (mixedVector B) := by
    change mixedMoment B node1013 node1013Labels = _
    exact sound1013 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1558, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h569, h576, h595, h1013, h4082, reducedSource1327] using sourceEq1558 B hB

theorem rowSound1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1327 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1327, numericCheck1327, reducedZero1327 B hB hF, mul_zero]

theorem sourceRowsAt1312 : MixedData.sourceRows (1312 : Fin 2425) =
    MixedData.row1312 := by decide +kernel

theorem sourceRowsAt1313 : MixedData.sourceRows (1313 : Fin 2425) =
    MixedData.row1313 := by decide +kernel

theorem sourceRowsAt1314 : MixedData.sourceRows (1314 : Fin 2425) =
    MixedData.row1314 := by decide +kernel

theorem sourceRowsAt1315 : MixedData.sourceRows (1315 : Fin 2425) =
    MixedData.row1315 := by decide +kernel

theorem sourceRowsAt1316 : MixedData.sourceRows (1316 : Fin 2425) =
    MixedData.row1316 := by decide +kernel

theorem sourceRowsAt1317 : MixedData.sourceRows (1317 : Fin 2425) =
    MixedData.row1317 := by decide +kernel

theorem sourceRowsAt1318 : MixedData.sourceRows (1318 : Fin 2425) =
    MixedData.row1318 := by decide +kernel

theorem sourceRowsAt1319 : MixedData.sourceRows (1319 : Fin 2425) =
    MixedData.row1319 := by decide +kernel

theorem sourceRowsAt1320 : MixedData.sourceRows (1320 : Fin 2425) =
    MixedData.row1320 := by decide +kernel

theorem sourceRowsAt1321 : MixedData.sourceRows (1321 : Fin 2425) =
    MixedData.row1321 := by decide +kernel

theorem sourceRowsAt1322 : MixedData.sourceRows (1322 : Fin 2425) =
    MixedData.row1322 := by decide +kernel

theorem sourceRowsAt1323 : MixedData.sourceRows (1323 : Fin 2425) =
    MixedData.row1323 := by decide +kernel

theorem sourceRowsAt1324 : MixedData.sourceRows (1324 : Fin 2425) =
    MixedData.row1324 := by decide +kernel

theorem sourceRowsAt1325 : MixedData.sourceRows (1325 : Fin 2425) =
    MixedData.row1325 := by decide +kernel

theorem sourceRowsAt1326 : MixedData.sourceRows (1326 : Fin 2425) =
    MixedData.row1326 := by decide +kernel

theorem sourceRowsAt1327 : MixedData.sourceRows (1327 : Fin 2425) =
    MixedData.row1327 := by decide +kernel

theorem chunkSound82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 82) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1312 ∨ k.val = 1313 ∨ k.val = 1314 ∨ k.val = 1315 ∨ k.val = 1316 ∨ k.val = 1317 ∨ k.val = 1318 ∨ k.val = 1319 ∨ k.val = 1320 ∨ k.val = 1321 ∨ k.val = 1322 ∨ k.val = 1323 ∨ k.val = 1324 ∨ k.val = 1325 ∨ k.val = 1326 ∨ k.val = 1327 := by omega
  rcases heq with h1312 | h1313 | h1314 | h1315 | h1316 | h1317 | h1318 | h1319 | h1320 | h1321 | h1322 | h1323 | h1324 | h1325 | h1326 | h1327
  · have he : k = (1312 : Fin 2425) := Fin.ext h1312
    subst k
    rw [sourceRowsAt1312]
    exact rowSound1312 B hB hF
  · have he : k = (1313 : Fin 2425) := Fin.ext h1313
    subst k
    rw [sourceRowsAt1313]
    exact rowSound1313 B hB hF
  · have he : k = (1314 : Fin 2425) := Fin.ext h1314
    subst k
    rw [sourceRowsAt1314]
    exact rowSound1314 B hB hF
  · have he : k = (1315 : Fin 2425) := Fin.ext h1315
    subst k
    rw [sourceRowsAt1315]
    exact rowSound1315 B hB hF
  · have he : k = (1316 : Fin 2425) := Fin.ext h1316
    subst k
    rw [sourceRowsAt1316]
    exact rowSound1316 B hB hF
  · have he : k = (1317 : Fin 2425) := Fin.ext h1317
    subst k
    rw [sourceRowsAt1317]
    exact rowSound1317 B hB hF
  · have he : k = (1318 : Fin 2425) := Fin.ext h1318
    subst k
    rw [sourceRowsAt1318]
    exact rowSound1318 B hB hF
  · have he : k = (1319 : Fin 2425) := Fin.ext h1319
    subst k
    rw [sourceRowsAt1319]
    exact rowSound1319 B hB hF
  · have he : k = (1320 : Fin 2425) := Fin.ext h1320
    subst k
    rw [sourceRowsAt1320]
    exact rowSound1320 B hB hF
  · have he : k = (1321 : Fin 2425) := Fin.ext h1321
    subst k
    rw [sourceRowsAt1321]
    exact rowSound1321 B hB hF
  · have he : k = (1322 : Fin 2425) := Fin.ext h1322
    subst k
    rw [sourceRowsAt1322]
    exact rowSound1322 B hB hF
  · have he : k = (1323 : Fin 2425) := Fin.ext h1323
    subst k
    rw [sourceRowsAt1323]
    exact rowSound1323 B hB hF
  · have he : k = (1324 : Fin 2425) := Fin.ext h1324
    subst k
    rw [sourceRowsAt1324]
    exact rowSound1324 B hB hF
  · have he : k = (1325 : Fin 2425) := Fin.ext h1325
    subst k
    rw [sourceRowsAt1325]
    exact rowSound1325 B hB hF
  · have he : k = (1326 : Fin 2425) := Fin.ext h1326
    subst k
    rw [sourceRowsAt1326]
    exact rowSound1326 B hB hF
  · have he : k = (1327 : Fin 2425) := Fin.ext h1327
    subst k
    rw [sourceRowsAt1327]
    exact rowSound1327 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
