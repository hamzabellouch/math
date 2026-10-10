import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic92
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources54

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1472 (mixedVector B) = 0 := by
  have h625 : mixedVector B (Sum.inr 625) = Sparse.eval nodeValue625 (mixedVector B) := by
    change mixedMoment B node625 node625Labels = _
    exact sound625 B hB hF
  have h626 : mixedVector B (Sum.inr 626) = Sparse.eval nodeValue626 (mixedVector B) := by
    change mixedMoment B node626 node626Labels = _
    exact sound626 B hB hF
  have h627 : mixedVector B (Sum.inr 627) = Sparse.eval nodeValue627 (mixedVector B) := by
    change mixedMoment B node627 node627Labels = _
    exact sound627 B hB hF
  have h632 : mixedVector B (Sum.inr 632) = Sparse.eval nodeValue632 (mixedVector B) := by
    change mixedMoment B node632 node632Labels = _
    exact sound632 B hB hF
  have h644 : mixedVector B (Sum.inr 644) = Sparse.eval nodeValue644 (mixedVector B) := by
    change mixedMoment B node644 node644Labels = _
    exact sound644 B hB hF
  have h1316 : mixedVector B (Sum.inr 1316) = Sparse.eval nodeValue1316 (mixedVector B) := by
    change mixedMoment B node1316 node1316Labels = _
    exact sound1316 B hB hF
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h1318 : mixedVector B (Sum.inr 1318) = Sparse.eval nodeValue1318 (mixedVector B) := by
    change mixedMoment B node1318 node1318Labels = _
    exact sound1318 B hB hF
  have h1322 : mixedVector B (Sum.inr 1322) = Sparse.eval nodeValue1322 (mixedVector B) := by
    change mixedMoment B node1322 node1322Labels = _
    exact sound1322 B hB hF
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h1331 : mixedVector B (Sum.inr 1331) = Sparse.eval nodeValue1331 (mixedVector B) := by
    change mixedMoment B node1331 node1331Labels = _
    exact sound1331 B hB hF
  have h1339 : mixedVector B (Sum.inr 1339) = Sparse.eval nodeValue1339 (mixedVector B) := by
    change mixedMoment B node1339 node1339Labels = _
    exact sound1339 B hB hF
  have h1386 : mixedVector B (Sum.inr 1386) = Sparse.eval nodeValue1386 (mixedVector B) := by
    change mixedMoment B node1386 node1386Labels = _
    exact sound1386 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h1409 : mixedVector B (Sum.inr 1409) = Sparse.eval nodeValue1409 (mixedVector B) := by
    change mixedMoment B node1409 node1409Labels = _
    exact sound1409 B hB hF
  have h1410 : mixedVector B (Sum.inr 1410) = Sparse.eval nodeValue1410 (mixedVector B) := by
    change mixedMoment B node1410 node1410Labels = _
    exact sound1410 B hB hF
  have h1411 : mixedVector B (Sum.inr 1411) = Sparse.eval nodeValue1411 (mixedVector B) := by
    change mixedMoment B node1411 node1411Labels = _
    exact sound1411 B hB hF
  have h1413 : mixedVector B (Sum.inr 1413) = Sparse.eval nodeValue1413 (mixedVector B) := by
    change mixedMoment B node1413 node1413Labels = _
    exact sound1413 B hB hF
  have h1420 : mixedVector B (Sum.inr 1420) = Sparse.eval nodeValue1420 (mixedVector B) := by
    change mixedMoment B node1420 node1420Labels = _
    exact sound1420 B hB hF
  have h1446 : mixedVector B (Sum.inr 1446) = Sparse.eval nodeValue1446 (mixedVector B) := by
    change mixedMoment B node1446 node1446Labels = _
    exact sound1446 B hB hF
  have h1447 : mixedVector B (Sum.inr 1447) = Sparse.eval nodeValue1447 (mixedVector B) := by
    change mixedMoment B node1447 node1447Labels = _
    exact sound1447 B hB hF
  have h3184 : mixedVector B (Sum.inr 3184) = Sparse.eval nodeValue3184 (mixedVector B) := by
    change mixedMoment B node3184 node3184Labels = _
    exact sound3184 B hB hF
  have h3204 : mixedVector B (Sum.inr 3204) = Sparse.eval nodeValue3204 (mixedVector B) := by
    change mixedMoment B node3204 node3204Labels = _
    exact sound3204 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  have h3228 : mixedVector B (Sum.inr 3228) = Sparse.eval nodeValue3228 (mixedVector B) := by
    change mixedMoment B node3228 node3228Labels = _
    exact sound3228 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm1725, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h625, h626, h627, h632, h644, h1316, h1317, h1318, h1322, h1327, h1328, h1331, h1339, h1386, h1388, h1391, h1409, h1410, h1411, h1413, h1420, h1446, h1447, h3184, h3204, h3227, h3228, h3229, reducedSource1472] using sourceEq1725 B hB

theorem rowSound1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1472 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1472, numericCheck1472, reducedZero1472 B hB hF, mul_zero]

theorem reducedZero1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1473 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1673 : mixedVector B (Sum.inr 1673) = Sparse.eval nodeValue1673 (mixedVector B) := by
    change mixedMoment B node1673 node1673Labels = _
    exact sound1673 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  simpa only [sourceForm1726, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1514, h1515, h1517, h1522, h1670, h1671, h1673, h1678, h1703, h1705, h1706, h1720, h1721, h1723, h1724, h1726, h1734, h1736, h1737, h1750, h1751, h1753, h2202, h2260, h2262, h2263, h2291, reducedSource1473] using sourceEq1726 B hB

theorem rowSound1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1473 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1473, numericCheck1473, reducedZero1473 B hB hF, mul_zero]

theorem reducedZero1474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1474 (mixedVector B) = 0 := by
  have h578 : mixedVector B (Sum.inr 578) = Sparse.eval nodeValue578 (mixedVector B) := by
    change mixedMoment B node578 node578Labels = _
    exact sound578 B hB hF
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h583 : mixedVector B (Sum.inr 583) = Sparse.eval nodeValue583 (mixedVector B) := by
    change mixedMoment B node583 node583Labels = _
    exact sound583 B hB hF
  have h586 : mixedVector B (Sum.inr 586) = Sparse.eval nodeValue586 (mixedVector B) := by
    change mixedMoment B node586 node586Labels = _
    exact sound586 B hB hF
  have h603 : mixedVector B (Sum.inr 603) = Sparse.eval nodeValue603 (mixedVector B) := by
    change mixedMoment B node603 node603Labels = _
    exact sound603 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1727, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h578, h581, h583, h586, h603, h1041, h4083, reducedSource1474] using sourceEq1727 B hB

theorem rowSound1474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1474 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1474, numericCheck1474, reducedZero1474 B hB hF, mul_zero]

theorem reducedZero1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1475 (mixedVector B) = 0 := by
  have h603 : mixedVector B (Sum.inr 603) = Sparse.eval nodeValue603 (mixedVector B) := by
    change mixedMoment B node603 node603Labels = _
    exact sound603 B hB hF
  have h922 : mixedVector B (Sum.inr 922) = Sparse.eval nodeValue922 (mixedVector B) := by
    change mixedMoment B node922 node922Labels = _
    exact sound922 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1728, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h603, h922, h1041, h1081, h1086, h4083, reducedSource1475] using sourceEq1728 B hB

theorem rowSound1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1475 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1475, numericCheck1475, reducedZero1475 B hB hF, mul_zero]

theorem reducedZero1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1476 (mixedVector B) = 0 := by
  have h942 : mixedVector B (Sum.inr 942) = Sparse.eval nodeValue942 (mixedVector B) := by
    change mixedMoment B node942 node942Labels = _
    exact sound942 B hB hF
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1729, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h942, h945, h947, h950, h1041, h2107, h4083, reducedSource1476] using sourceEq1729 B hB

theorem rowSound1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1476 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1476, numericCheck1476, reducedZero1476 B hB hF, mul_zero]

theorem reducedZero1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1477 (mixedVector B) = 0 := by
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4101 : mixedVector B (Sum.inr 4101) = Sparse.eval nodeValue4101 (mixedVector B) := by
    change mixedMoment B node4101 node4101Labels = _
    exact sound4101 B hB hF
  have h4102 : mixedVector B (Sum.inr 4102) = Sparse.eval nodeValue4102 (mixedVector B) := by
    change mixedMoment B node4102 node4102Labels = _
    exact sound4102 B hB hF
  have h4107 : mixedVector B (Sum.inr 4107) = Sparse.eval nodeValue4107 (mixedVector B) := by
    change mixedMoment B node4107 node4107Labels = _
    exact sound4107 B hB hF
  have h4119 : mixedVector B (Sum.inr 4119) = Sparse.eval nodeValue4119 (mixedVector B) := by
    change mixedMoment B node4119 node4119Labels = _
    exact sound4119 B hB hF
  have h4287 : mixedVector B (Sum.inr 4287) = Sparse.eval nodeValue4287 (mixedVector B) := by
    change mixedMoment B node4287 node4287Labels = _
    exact sound4287 B hB hF
  have h4288 : mixedVector B (Sum.inr 4288) = Sparse.eval nodeValue4288 (mixedVector B) := by
    change mixedMoment B node4288 node4288Labels = _
    exact sound4288 B hB hF
  have h4292 : mixedVector B (Sum.inr 4292) = Sparse.eval nodeValue4292 (mixedVector B) := by
    change mixedMoment B node4292 node4292Labels = _
    exact sound4292 B hB hF
  have h4301 : mixedVector B (Sum.inr 4301) = Sparse.eval nodeValue4301 (mixedVector B) := by
    change mixedMoment B node4301 node4301Labels = _
    exact sound4301 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4424 : mixedVector B (Sum.inr 4424) = Sparse.eval nodeValue4424 (mixedVector B) := by
    change mixedMoment B node4424 node4424Labels = _
    exact sound4424 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm1730, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4100, h4101, h4102, h4107, h4119, h4287, h4288, h4292, h4301, h4344, h4346, h4349, h4355, h4399, h4401, h4404, h4424, h4456, h4457, h4458, h4460, h4467, h4495, h4499, h5073, h5169, h5259, h5292, h5293, reducedSource1477] using sourceEq1730 B hB

theorem rowSound1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1477 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1477, numericCheck1477, reducedZero1477 B hB hF, mul_zero]

theorem reducedZero1478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1478 (mixedVector B) = 0 := by
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4267 : mixedVector B (Sum.inr 4267) = Sparse.eval nodeValue4267 (mixedVector B) := by
    change mixedMoment B node4267 node4267Labels = _
    exact sound4267 B hB hF
  have h4268 : mixedVector B (Sum.inr 4268) = Sparse.eval nodeValue4268 (mixedVector B) := by
    change mixedMoment B node4268 node4268Labels = _
    exact sound4268 B hB hF
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4397 : mixedVector B (Sum.inr 4397) = Sparse.eval nodeValue4397 (mixedVector B) := by
    change mixedMoment B node4397 node4397Labels = _
    exact sound4397 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4407 : mixedVector B (Sum.inr 4407) = Sparse.eval nodeValue4407 (mixedVector B) := by
    change mixedMoment B node4407 node4407Labels = _
    exact sound4407 B hB hF
  have h4436 : mixedVector B (Sum.inr 4436) = Sparse.eval nodeValue4436 (mixedVector B) := by
    change mixedMoment B node4436 node4436Labels = _
    exact sound4436 B hB hF
  have h4438 : mixedVector B (Sum.inr 4438) = Sparse.eval nodeValue4438 (mixedVector B) := by
    change mixedMoment B node4438 node4438Labels = _
    exact sound4438 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4453 : mixedVector B (Sum.inr 4453) = Sparse.eval nodeValue4453 (mixedVector B) := by
    change mixedMoment B node4453 node4453Labels = _
    exact sound4453 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4471 : mixedVector B (Sum.inr 4471) = Sparse.eval nodeValue4471 (mixedVector B) := by
    change mixedMoment B node4471 node4471Labels = _
    exact sound4471 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4475 : mixedVector B (Sum.inr 4475) = Sparse.eval nodeValue4475 (mixedVector B) := by
    change mixedMoment B node4475 node4475Labels = _
    exact sound4475 B hB hF
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
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  simpa only [sourceForm1732, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4249, h4264, h4265, h4267, h4268, h4396, h4397, h4399, h4407, h4436, h4438, h4439, h4452, h4453, h4457, h4458, h4459, h4461, h4471, h4474, h4475, h4498, h4499, h4502, h4590, h4602, h4603, h4606, h4624, reducedSource1478] using sourceEq1732 B hB

theorem rowSound1478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1478 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1478, numericCheck1478, reducedZero1478 B hB hF, mul_zero]

theorem reducedZero1479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1479 (mixedVector B) = 0 := by
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h807 : mixedVector B (Sum.inr 807) = Sparse.eval nodeValue807 (mixedVector B) := by
    change mixedMoment B node807 node807Labels = _
    exact sound807 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h824 : mixedVector B (Sum.inr 824) = Sparse.eval nodeValue824 (mixedVector B) := by
    change mixedMoment B node824 node824Labels = _
    exact sound824 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h978 : mixedVector B (Sum.inr 978) = Sparse.eval nodeValue978 (mixedVector B) := by
    change mixedMoment B node978 node978Labels = _
    exact sound978 B hB hF
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h1020 : mixedVector B (Sum.inr 1020) = Sparse.eval nodeValue1020 (mixedVector B) := by
    change mixedMoment B node1020 node1020Labels = _
    exact sound1020 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h1054 : mixedVector B (Sum.inr 1054) = Sparse.eval nodeValue1054 (mixedVector B) := by
    change mixedMoment B node1054 node1054Labels = _
    exact sound1054 B hB hF
  have h1057 : mixedVector B (Sum.inr 1057) = Sparse.eval nodeValue1057 (mixedVector B) := by
    change mixedMoment B node1057 node1057Labels = _
    exact sound1057 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h1266 : mixedVector B (Sum.inr 1266) = Sparse.eval nodeValue1266 (mixedVector B) := by
    change mixedMoment B node1266 node1266Labels = _
    exact sound1266 B hB hF
  have h1267 : mixedVector B (Sum.inr 1267) = Sparse.eval nodeValue1267 (mixedVector B) := by
    change mixedMoment B node1267 node1267Labels = _
    exact sound1267 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  simpa only [sourceForm1733, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h783, h806, h807, h810, h824, h977, h978, h980, h988, h1018, h1020, h1021, h1035, h1036, h1040, h1041, h1042, h1044, h1054, h1057, h1058, h1082, h1083, h1086, h1213, h1262, h1266, h1267, h1301, reducedSource1479] using sourceEq1733 B hB

theorem rowSound1479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1479 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1479, numericCheck1479, reducedZero1479 B hB hF, mul_zero]

theorem reducedZero1480 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1480 (mixedVector B) = 0 := by
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h1358 : mixedVector B (Sum.inr 1358) = Sparse.eval nodeValue1358 (mixedVector B) := by
    change mixedMoment B node1358 node1358Labels = _
    exact sound1358 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1368 : mixedVector B (Sum.inr 1368) = Sparse.eval nodeValue1368 (mixedVector B) := by
    change mixedMoment B node1368 node1368Labels = _
    exact sound1368 B hB hF
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h1384 : mixedVector B (Sum.inr 1384) = Sparse.eval nodeValue1384 (mixedVector B) := by
    change mixedMoment B node1384 node1384Labels = _
    exact sound1384 B hB hF
  have h1386 : mixedVector B (Sum.inr 1386) = Sparse.eval nodeValue1386 (mixedVector B) := by
    change mixedMoment B node1386 node1386Labels = _
    exact sound1386 B hB hF
  have h1393 : mixedVector B (Sum.inr 1393) = Sparse.eval nodeValue1393 (mixedVector B) := by
    change mixedMoment B node1393 node1393Labels = _
    exact sound1393 B hB hF
  have h1395 : mixedVector B (Sum.inr 1395) = Sparse.eval nodeValue1395 (mixedVector B) := by
    change mixedMoment B node1395 node1395Labels = _
    exact sound1395 B hB hF
  have h1396 : mixedVector B (Sum.inr 1396) = Sparse.eval nodeValue1396 (mixedVector B) := by
    change mixedMoment B node1396 node1396Labels = _
    exact sound1396 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h1407 : mixedVector B (Sum.inr 1407) = Sparse.eval nodeValue1407 (mixedVector B) := by
    change mixedMoment B node1407 node1407Labels = _
    exact sound1407 B hB hF
  have h1410 : mixedVector B (Sum.inr 1410) = Sparse.eval nodeValue1410 (mixedVector B) := by
    change mixedMoment B node1410 node1410Labels = _
    exact sound1410 B hB hF
  have h1411 : mixedVector B (Sum.inr 1411) = Sparse.eval nodeValue1411 (mixedVector B) := by
    change mixedMoment B node1411 node1411Labels = _
    exact sound1411 B hB hF
  have h1412 : mixedVector B (Sum.inr 1412) = Sparse.eval nodeValue1412 (mixedVector B) := by
    change mixedMoment B node1412 node1412Labels = _
    exact sound1412 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h1443 : mixedVector B (Sum.inr 1443) = Sparse.eval nodeValue1443 (mixedVector B) := by
    change mixedMoment B node1443 node1443Labels = _
    exact sound1443 B hB hF
  have h1447 : mixedVector B (Sum.inr 1447) = Sparse.eval nodeValue1447 (mixedVector B) := by
    change mixedMoment B node1447 node1447Labels = _
    exact sound1447 B hB hF
  have h1448 : mixedVector B (Sum.inr 1448) = Sparse.eval nodeValue1448 (mixedVector B) := by
    change mixedMoment B node1448 node1448Labels = _
    exact sound1448 B hB hF
  have h1468 : mixedVector B (Sum.inr 1468) = Sparse.eval nodeValue1468 (mixedVector B) := by
    change mixedMoment B node1468 node1468Labels = _
    exact sound1468 B hB hF
  have h1475 : mixedVector B (Sum.inr 1475) = Sparse.eval nodeValue1475 (mixedVector B) := by
    change mixedMoment B node1475 node1475Labels = _
    exact sound1475 B hB hF
  have h1480 : mixedVector B (Sum.inr 1480) = Sparse.eval nodeValue1480 (mixedVector B) := by
    change mixedMoment B node1480 node1480Labels = _
    exact sound1480 B hB hF
  have h1482 : mixedVector B (Sum.inr 1482) = Sparse.eval nodeValue1482 (mixedVector B) := by
    change mixedMoment B node1482 node1482Labels = _
    exact sound1482 B hB hF
  have h1483 : mixedVector B (Sum.inr 1483) = Sparse.eval nodeValue1483 (mixedVector B) := by
    change mixedMoment B node1483 node1483Labels = _
    exact sound1483 B hB hF
  simpa only [sourceForm1734, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1213, h1236, h1237, h1240, h1301, h1358, h1367, h1368, h1370, h1383, h1384, h1386, h1393, h1395, h1396, h1406, h1407, h1410, h1411, h1412, h1414, h1443, h1447, h1448, h1468, h1475, h1480, h1482, h1483, reducedSource1480] using sourceEq1734 B hB

theorem rowSound1480 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1480 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1480, numericCheck1480, reducedZero1480 B hB hF, mul_zero]

theorem reducedZero1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1481 (mixedVector B) = 0 := by
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h2016 : mixedVector B (Sum.inr 2016) = Sparse.eval nodeValue2016 (mixedVector B) := by
    change mixedMoment B node2016 node2016Labels = _
    exact sound2016 B hB hF
  have h2101 : mixedVector B (Sum.inr 2101) = Sparse.eval nodeValue2101 (mixedVector B) := by
    change mixedMoment B node2101 node2101Labels = _
    exact sound2101 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1735, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1035, h2016, h2101, h2205, h2242, h2260, h4080, reducedSource1481] using sourceEq1735 B hB

theorem rowSound1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1481 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1481, numericCheck1481, reducedZero1481 B hB hF, mul_zero]

theorem reducedZero1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1482 (mixedVector B) = 0 := by
  have h730 : mixedVector B (Sum.inr 730) = Sparse.eval nodeValue730 (mixedVector B) := by
    change mixedMoment B node730 node730Labels = _
    exact sound730 B hB hF
  have h733 : mixedVector B (Sum.inr 733) = Sparse.eval nodeValue733 (mixedVector B) := by
    change mixedMoment B node733 node733Labels = _
    exact sound733 B hB hF
  have h734 : mixedVector B (Sum.inr 734) = Sparse.eval nodeValue734 (mixedVector B) := by
    change mixedMoment B node734 node734Labels = _
    exact sound734 B hB hF
  have h738 : mixedVector B (Sum.inr 738) = Sparse.eval nodeValue738 (mixedVector B) := by
    change mixedMoment B node738 node738Labels = _
    exact sound738 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1737, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h730, h733, h734, h738, h806, h1645, h4069, reducedSource1482] using sourceEq1737 B hB

theorem rowSound1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1482 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1482, numericCheck1482, reducedZero1482 B hB hF, mul_zero]

theorem reducedZero1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1483 (mixedVector B) = 0 := by
  have h4149 : mixedVector B (Sum.inr 4149) = Sparse.eval nodeValue4149 (mixedVector B) := by
    change mixedMoment B node4149 node4149Labels = _
    exact sound4149 B hB hF
  have h4151 : mixedVector B (Sum.inr 4151) = Sparse.eval nodeValue4151 (mixedVector B) := by
    change mixedMoment B node4151 node4151Labels = _
    exact sound4151 B hB hF
  have h4154 : mixedVector B (Sum.inr 4154) = Sparse.eval nodeValue4154 (mixedVector B) := by
    change mixedMoment B node4154 node4154Labels = _
    exact sound4154 B hB hF
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4326 : mixedVector B (Sum.inr 4326) = Sparse.eval nodeValue4326 (mixedVector B) := by
    change mixedMoment B node4326 node4326Labels = _
    exact sound4326 B hB hF
  have h4328 : mixedVector B (Sum.inr 4328) = Sparse.eval nodeValue4328 (mixedVector B) := by
    change mixedMoment B node4328 node4328Labels = _
    exact sound4328 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4363 : mixedVector B (Sum.inr 4363) = Sparse.eval nodeValue4363 (mixedVector B) := by
    change mixedMoment B node4363 node4363Labels = _
    exact sound4363 B hB hF
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4368 : mixedVector B (Sum.inr 4368) = Sparse.eval nodeValue4368 (mixedVector B) := by
    change mixedMoment B node4368 node4368Labels = _
    exact sound4368 B hB hF
  have h4455 : mixedVector B (Sum.inr 4455) = Sparse.eval nodeValue4455 (mixedVector B) := by
    change mixedMoment B node4455 node4455Labels = _
    exact sound4455 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  simpa only [sourceForm1738, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4149, h4151, h4154, h4172, h4326, h4328, h4341, h4363, h4365, h4368, h4455, h4457, h4459, h4460, h4466, h4495, h4498, h4801, h4865, h4888, h4894, reducedSource1483] using sourceEq1738 B hB

theorem rowSound1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1483 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1483, numericCheck1483, reducedZero1483 B hB hF, mul_zero]

theorem reducedZero1484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1484 (mixedVector B) = 0 := by
  have h629 : mixedVector B (Sum.inr 629) = Sparse.eval nodeValue629 (mixedVector B) := by
    change mixedMoment B node629 node629Labels = _
    exact sound629 B hB hF
  have h630 : mixedVector B (Sum.inr 630) = Sparse.eval nodeValue630 (mixedVector B) := by
    change mixedMoment B node630 node630Labels = _
    exact sound630 B hB hF
  have h631 : mixedVector B (Sum.inr 631) = Sparse.eval nodeValue631 (mixedVector B) := by
    change mixedMoment B node631 node631Labels = _
    exact sound631 B hB hF
  have h646 : mixedVector B (Sum.inr 646) = Sparse.eval nodeValue646 (mixedVector B) := by
    change mixedMoment B node646 node646Labels = _
    exact sound646 B hB hF
  have h1319 : mixedVector B (Sum.inr 1319) = Sparse.eval nodeValue1319 (mixedVector B) := by
    change mixedMoment B node1319 node1319Labels = _
    exact sound1319 B hB hF
  have h1320 : mixedVector B (Sum.inr 1320) = Sparse.eval nodeValue1320 (mixedVector B) := by
    change mixedMoment B node1320 node1320Labels = _
    exact sound1320 B hB hF
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h1329 : mixedVector B (Sum.inr 1329) = Sparse.eval nodeValue1329 (mixedVector B) := by
    change mixedMoment B node1329 node1329Labels = _
    exact sound1329 B hB hF
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h1341 : mixedVector B (Sum.inr 1341) = Sparse.eval nodeValue1341 (mixedVector B) := by
    change mixedMoment B node1341 node1341Labels = _
    exact sound1341 B hB hF
  have h1405 : mixedVector B (Sum.inr 1405) = Sparse.eval nodeValue1405 (mixedVector B) := by
    change mixedMoment B node1405 node1405Labels = _
    exact sound1405 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1441 : mixedVector B (Sum.inr 1441) = Sparse.eval nodeValue1441 (mixedVector B) := by
    change mixedMoment B node1441 node1441Labels = _
    exact sound1441 B hB hF
  have h1448 : mixedVector B (Sum.inr 1448) = Sparse.eval nodeValue1448 (mixedVector B) := by
    change mixedMoment B node1448 node1448Labels = _
    exact sound1448 B hB hF
  have h3185 : mixedVector B (Sum.inr 3185) = Sparse.eval nodeValue3185 (mixedVector B) := by
    change mixedMoment B node3185 node3185Labels = _
    exact sound3185 B hB hF
  have h3205 : mixedVector B (Sum.inr 3205) = Sparse.eval nodeValue3205 (mixedVector B) := by
    change mixedMoment B node3205 node3205Labels = _
    exact sound3205 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm1739, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h629, h630, h631, h646, h1319, h1320, h1321, h1329, h1330, h1341, h1405, h1406, h1414, h1416, h1419, h1441, h1448, h3185, h3205, h3227, h3230, reducedSource1484] using sourceEq1739 B hB

theorem rowSound1484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1484 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1484, numericCheck1484, reducedZero1484 B hB hF, mul_zero]

theorem reducedZero1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1485 (mixedVector B) = 0 := by
  have h1501 : mixedVector B (Sum.inr 1501) = Sparse.eval nodeValue1501 (mixedVector B) := by
    change mixedMoment B node1501 node1501Labels = _
    exact sound1501 B hB hF
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1697 : mixedVector B (Sum.inr 1697) = Sparse.eval nodeValue1697 (mixedVector B) := by
    change mixedMoment B node1697 node1697Labels = _
    exact sound1697 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  simpa only [sourceForm1740, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1501, h1505, h1507, h1511, h1663, h1664, h1667, h1697, h1698, h1704, h1707, h1708, h1712, h1714, h1725, h1727, h1738, h2190, h2242, h2244, h2264, reducedSource1485] using sourceEq1740 B hB

theorem rowSound1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1485 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1485, numericCheck1485, reducedZero1485 B hB hF, mul_zero]

theorem reducedZero1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1486 (mixedVector B) = 0 := by
  have h577 : mixedVector B (Sum.inr 577) = Sparse.eval nodeValue577 (mixedVector B) := by
    change mixedMoment B node577 node577Labels = _
    exact sound577 B hB hF
  have h579 : mixedVector B (Sum.inr 579) = Sparse.eval nodeValue579 (mixedVector B) := by
    change mixedMoment B node579 node579Labels = _
    exact sound579 B hB hF
  have h582 : mixedVector B (Sum.inr 582) = Sparse.eval nodeValue582 (mixedVector B) := by
    change mixedMoment B node582 node582Labels = _
    exact sound582 B hB hF
  have h600 : mixedVector B (Sum.inr 600) = Sparse.eval nodeValue600 (mixedVector B) := by
    change mixedMoment B node600 node600Labels = _
    exact sound600 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1741, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h577, h579, h582, h600, h1040, h4084, reducedSource1486] using sourceEq1741 B hB

theorem rowSound1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1486 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1486, numericCheck1486, reducedZero1486 B hB hF, mul_zero]

theorem reducedZero1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1487 (mixedVector B) = 0 := by
  have h600 : mixedVector B (Sum.inr 600) = Sparse.eval nodeValue600 (mixedVector B) := by
    change mixedMoment B node600 node600Labels = _
    exact sound600 B hB hF
  have h919 : mixedVector B (Sum.inr 919) = Sparse.eval nodeValue919 (mixedVector B) := by
    change mixedMoment B node919 node919Labels = _
    exact sound919 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1742, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h600, h919, h1040, h1079, h1082, h4084, reducedSource1487] using sourceEq1742 B hB

theorem rowSound1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1487 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1487, numericCheck1487, reducedZero1487 B hB hF, mul_zero]

theorem sourceRowsAt1472 : MixedData.sourceRows (1472 : Fin 2425) =
    MixedData.row1472 := by decide +kernel

theorem sourceRowsAt1473 : MixedData.sourceRows (1473 : Fin 2425) =
    MixedData.row1473 := by decide +kernel

theorem sourceRowsAt1474 : MixedData.sourceRows (1474 : Fin 2425) =
    MixedData.row1474 := by decide +kernel

theorem sourceRowsAt1475 : MixedData.sourceRows (1475 : Fin 2425) =
    MixedData.row1475 := by decide +kernel

theorem sourceRowsAt1476 : MixedData.sourceRows (1476 : Fin 2425) =
    MixedData.row1476 := by decide +kernel

theorem sourceRowsAt1477 : MixedData.sourceRows (1477 : Fin 2425) =
    MixedData.row1477 := by decide +kernel

theorem sourceRowsAt1478 : MixedData.sourceRows (1478 : Fin 2425) =
    MixedData.row1478 := by decide +kernel

theorem sourceRowsAt1479 : MixedData.sourceRows (1479 : Fin 2425) =
    MixedData.row1479 := by decide +kernel

theorem sourceRowsAt1480 : MixedData.sourceRows (1480 : Fin 2425) =
    MixedData.row1480 := by decide +kernel

theorem sourceRowsAt1481 : MixedData.sourceRows (1481 : Fin 2425) =
    MixedData.row1481 := by decide +kernel

theorem sourceRowsAt1482 : MixedData.sourceRows (1482 : Fin 2425) =
    MixedData.row1482 := by decide +kernel

theorem sourceRowsAt1483 : MixedData.sourceRows (1483 : Fin 2425) =
    MixedData.row1483 := by decide +kernel

theorem sourceRowsAt1484 : MixedData.sourceRows (1484 : Fin 2425) =
    MixedData.row1484 := by decide +kernel

theorem sourceRowsAt1485 : MixedData.sourceRows (1485 : Fin 2425) =
    MixedData.row1485 := by decide +kernel

theorem sourceRowsAt1486 : MixedData.sourceRows (1486 : Fin 2425) =
    MixedData.row1486 := by decide +kernel

theorem sourceRowsAt1487 : MixedData.sourceRows (1487 : Fin 2425) =
    MixedData.row1487 := by decide +kernel

theorem chunkSound92 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 92) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1472 ∨ k.val = 1473 ∨ k.val = 1474 ∨ k.val = 1475 ∨ k.val = 1476 ∨ k.val = 1477 ∨ k.val = 1478 ∨ k.val = 1479 ∨ k.val = 1480 ∨ k.val = 1481 ∨ k.val = 1482 ∨ k.val = 1483 ∨ k.val = 1484 ∨ k.val = 1485 ∨ k.val = 1486 ∨ k.val = 1487 := by omega
  rcases heq with h1472 | h1473 | h1474 | h1475 | h1476 | h1477 | h1478 | h1479 | h1480 | h1481 | h1482 | h1483 | h1484 | h1485 | h1486 | h1487
  · have he : k = (1472 : Fin 2425) := Fin.ext h1472
    subst k
    rw [sourceRowsAt1472]
    exact rowSound1472 B hB hF
  · have he : k = (1473 : Fin 2425) := Fin.ext h1473
    subst k
    rw [sourceRowsAt1473]
    exact rowSound1473 B hB hF
  · have he : k = (1474 : Fin 2425) := Fin.ext h1474
    subst k
    rw [sourceRowsAt1474]
    exact rowSound1474 B hB hF
  · have he : k = (1475 : Fin 2425) := Fin.ext h1475
    subst k
    rw [sourceRowsAt1475]
    exact rowSound1475 B hB hF
  · have he : k = (1476 : Fin 2425) := Fin.ext h1476
    subst k
    rw [sourceRowsAt1476]
    exact rowSound1476 B hB hF
  · have he : k = (1477 : Fin 2425) := Fin.ext h1477
    subst k
    rw [sourceRowsAt1477]
    exact rowSound1477 B hB hF
  · have he : k = (1478 : Fin 2425) := Fin.ext h1478
    subst k
    rw [sourceRowsAt1478]
    exact rowSound1478 B hB hF
  · have he : k = (1479 : Fin 2425) := Fin.ext h1479
    subst k
    rw [sourceRowsAt1479]
    exact rowSound1479 B hB hF
  · have he : k = (1480 : Fin 2425) := Fin.ext h1480
    subst k
    rw [sourceRowsAt1480]
    exact rowSound1480 B hB hF
  · have he : k = (1481 : Fin 2425) := Fin.ext h1481
    subst k
    rw [sourceRowsAt1481]
    exact rowSound1481 B hB hF
  · have he : k = (1482 : Fin 2425) := Fin.ext h1482
    subst k
    rw [sourceRowsAt1482]
    exact rowSound1482 B hB hF
  · have he : k = (1483 : Fin 2425) := Fin.ext h1483
    subst k
    rw [sourceRowsAt1483]
    exact rowSound1483 B hB hF
  · have he : k = (1484 : Fin 2425) := Fin.ext h1484
    subst k
    rw [sourceRowsAt1484]
    exact rowSound1484 B hB hF
  · have he : k = (1485 : Fin 2425) := Fin.ext h1485
    subst k
    rw [sourceRowsAt1485]
    exact rowSound1485 B hB hF
  · have he : k = (1486 : Fin 2425) := Fin.ext h1486
    subst k
    rw [sourceRowsAt1486]
    exact rowSound1486 B hB hF
  · have he : k = (1487 : Fin 2425) := Fin.ext h1487
    subst k
    rw [sourceRowsAt1487]
    exact rowSound1487 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
