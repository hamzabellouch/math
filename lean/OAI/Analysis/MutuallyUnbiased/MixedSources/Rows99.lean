import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic99
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources59

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1584 (mixedVector B) = 0 := by
  have h4150 : mixedVector B (Sum.inr 4150) = Sparse.eval nodeValue4150 (mixedVector B) := by
    change mixedMoment B node4150 node4150Labels = _
    exact sound4150 B hB hF
  have h4152 : mixedVector B (Sum.inr 4152) = Sparse.eval nodeValue4152 (mixedVector B) := by
    change mixedMoment B node4152 node4152Labels = _
    exact sound4152 B hB hF
  have h4171 : mixedVector B (Sum.inr 4171) = Sparse.eval nodeValue4171 (mixedVector B) := by
    change mixedMoment B node4171 node4171Labels = _
    exact sound4171 B hB hF
  have h4364 : mixedVector B (Sum.inr 4364) = Sparse.eval nodeValue4364 (mixedVector B) := by
    change mixedMoment B node4364 node4364Labels = _
    exact sound4364 B hB hF
  have h4366 : mixedVector B (Sum.inr 4366) = Sparse.eval nodeValue4366 (mixedVector B) := by
    change mixedMoment B node4366 node4366Labels = _
    exact sound4366 B hB hF
  have h4438 : mixedVector B (Sum.inr 4438) = Sparse.eval nodeValue4438 (mixedVector B) := by
    change mixedMoment B node4438 node4438Labels = _
    exact sound4438 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  simpa only [sourceForm1871, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4150, h4152, h4171, h4364, h4366, h4438, h4439, h4456, h4458, h4461, h4497, h4864, h4887, h4893, reducedSource1584] using sourceEq1871 B hB

theorem rowSound1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1584 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1584, numericCheck1584, reducedZero1584 B hB hF, mul_zero]

theorem reducedZero1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1585 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1506 : mixedVector B (Sum.inr 1506) = Sparse.eval nodeValue1506 (mixedVector B) := by
    change mixedMoment B node1506 node1506Labels = _
    exact sound1506 B hB hF
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  simpa only [sourceForm1872, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1506, h1510, h1703, h1705, h1706, h1711, h1713, h1724, h1726, h1737, h2241, h2243, h2263, reducedSource1585] using sourceEq1872 B hB

theorem rowSound1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1585 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1585, numericCheck1585, reducedZero1585 B hB hF, mul_zero]

theorem reducedZero1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1586 (mixedVector B) = 0 := by
  have h599 : mixedVector B (Sum.inr 599) = Sparse.eval nodeValue599 (mixedVector B) := by
    change mixedMoment B node599 node599Labels = _
    exact sound599 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1873, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h599, h1039, h1081, h4083, reducedSource1586] using sourceEq1873 B hB

theorem rowSound1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1586 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1586, numericCheck1586, reducedZero1586 B hB hF, mul_zero]

theorem reducedZero1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1587 (mixedVector B) = 0 := by
  have h4098 : mixedVector B (Sum.inr 4098) = Sparse.eval nodeValue4098 (mixedVector B) := by
    change mixedMoment B node4098 node4098Labels = _
    exact sound4098 B hB hF
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4113 : mixedVector B (Sum.inr 4113) = Sparse.eval nodeValue4113 (mixedVector B) := by
    change mixedMoment B node4113 node4113Labels = _
    exact sound4113 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4417 : mixedVector B (Sum.inr 4417) = Sparse.eval nodeValue4417 (mixedVector B) := by
    change mixedMoment B node4417 node4417Labels = _
    exact sound4417 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  simpa only [sourceForm1874, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4098, h4100, h4113, h4341, h4344, h4396, h4399, h4417, h4457, h4458, h4495, h5167, h5257, h5292, reducedSource1587] using sourceEq1874 B hB

theorem rowSound1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1587 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1587, numericCheck1587, reducedZero1587 B hB hF, mul_zero]

theorem reducedZero1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1588 (mixedVector B) = 0 := by
  have h535 : mixedVector B (Sum.inr 535) = Sparse.eval nodeValue535 (mixedVector B) := by
    change mixedMoment B node535 node535Labels = _
    exact sound535 B hB hF
  have h537 : mixedVector B (Sum.inr 537) = Sparse.eval nodeValue537 (mixedVector B) := by
    change mixedMoment B node537 node537Labels = _
    exact sound537 B hB hF
  have h550 : mixedVector B (Sum.inr 550) = Sparse.eval nodeValue550 (mixedVector B) := by
    change mixedMoment B node550 node550Labels = _
    exact sound550 B hB hF
  have h919 : mixedVector B (Sum.inr 919) = Sparse.eval nodeValue919 (mixedVector B) := by
    change mixedMoment B node919 node919Labels = _
    exact sound919 B hB hF
  have h922 : mixedVector B (Sum.inr 922) = Sparse.eval nodeValue922 (mixedVector B) := by
    change mixedMoment B node922 node922Labels = _
    exact sound922 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h2593 : mixedVector B (Sum.inr 2593) = Sparse.eval nodeValue2593 (mixedVector B) := by
    change mixedMoment B node2593 node2593Labels = _
    exact sound2593 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  simpa only [sourceForm1875, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h535, h537, h550, h919, h922, h977, h980, h998, h1040, h1041, h1079, h2593, h2721, h2766, reducedSource1588] using sourceEq1875 B hB

theorem rowSound1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1588 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1588, numericCheck1588, reducedZero1588 B hB hF, mul_zero]

theorem reducedZero1589 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1589 (mixedVector B) = 0 := by
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4263 : mixedVector B (Sum.inr 4263) = Sparse.eval nodeValue4263 (mixedVector B) := by
    change mixedMoment B node4263 node4263Labels = _
    exact sound4263 B hB hF
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4455 : mixedVector B (Sum.inr 4455) = Sparse.eval nodeValue4455 (mixedVector B) := by
    change mixedMoment B node4455 node4455Labels = _
    exact sound4455 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4469 : mixedVector B (Sum.inr 4469) = Sparse.eval nodeValue4469 (mixedVector B) := by
    change mixedMoment B node4469 node4469Labels = _
    exact sound4469 B hB hF
  have h4473 : mixedVector B (Sum.inr 4473) = Sparse.eval nodeValue4473 (mixedVector B) := by
    change mixedMoment B node4473 node4473Labels = _
    exact sound4473 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  simpa only [sourceForm1876, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4249, h4252, h4263, h4449, h4451, h4455, h4456, h4469, h4473, h4495, h4497, h4599, h4601, h4622, reducedSource1589] using sourceEq1876 B hB

theorem rowSound1589 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1589 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1589, numericCheck1589, reducedZero1589 B hB hF, mul_zero]

theorem reducedZero1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1590 (mixedVector B) = 0 := by
  have h1070 : mixedVector B (Sum.inr 1070) = Sparse.eval nodeValue1070 (mixedVector B) := by
    change mixedMoment B node1070 node1070Labels = _
    exact sound1070 B hB hF
  have h2043 : mixedVector B (Sum.inr 2043) = Sparse.eval nodeValue2043 (mixedVector B) := by
    change mixedMoment B node2043 node2043Labels = _
    exact sound2043 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1877, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1070, h2043, h2220, h2224, h2259, h2287, h4081, reducedSource1590] using sourceEq1877 B hB

theorem rowSound1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1590 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1590, numericCheck1590, reducedZero1590 B hB hF, mul_zero]

theorem reducedZero1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1591 (mixedVector B) = 0 := by
  have h1071 : mixedVector B (Sum.inr 1071) = Sparse.eval nodeValue1071 (mixedVector B) := by
    change mixedMoment B node1071 node1071Labels = _
    exact sound1071 B hB hF
  have h2044 : mixedVector B (Sum.inr 2044) = Sparse.eval nodeValue2044 (mixedVector B) := by
    change mixedMoment B node2044 node2044Labels = _
    exact sound2044 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1878, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1071, h2044, h2225, h2274, h2288, h4082, reducedSource1591] using sourceEq1878 B hB

theorem rowSound1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1591 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1591, numericCheck1591, reducedZero1591 B hB hF, mul_zero]

theorem reducedZero1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1592 (mixedVector B) = 0 := by
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2046 : mixedVector B (Sum.inr 2046) = Sparse.eval nodeValue2046 (mixedVector B) := by
    change mixedMoment B node2046 node2046Labels = _
    exact sound2046 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1879, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1073, h2046, h2227, h2260, h2275, h4080, reducedSource1592] using sourceEq1879 B hB

theorem rowSound1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1592 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1592, numericCheck1592, reducedZero1592 B hB hF, mul_zero]

theorem reducedZero1593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1593 (mixedVector B) = 0 := by
  have h4169 : mixedVector B (Sum.inr 4169) = Sparse.eval nodeValue4169 (mixedVector B) := by
    change mixedMoment B node4169 node4169Labels = _
    exact sound4169 B hB hF
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4173 : mixedVector B (Sum.inr 4173) = Sparse.eval nodeValue4173 (mixedVector B) := by
    change mixedMoment B node4173 node4173Labels = _
    exact sound4173 B hB hF
  have h4176 : mixedVector B (Sum.inr 4176) = Sparse.eval nodeValue4176 (mixedVector B) := by
    change mixedMoment B node4176 node4176Labels = _
    exact sound4176 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4342 : mixedVector B (Sum.inr 4342) = Sparse.eval nodeValue4342 (mixedVector B) := by
    change mixedMoment B node4342 node4342Labels = _
    exact sound4342 B hB hF
  have h4345 : mixedVector B (Sum.inr 4345) = Sparse.eval nodeValue4345 (mixedVector B) := by
    change mixedMoment B node4345 node4345Labels = _
    exact sound4345 B hB hF
  have h4455 : mixedVector B (Sum.inr 4455) = Sparse.eval nodeValue4455 (mixedVector B) := by
    change mixedMoment B node4455 node4455Labels = _
    exact sound4455 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4473 : mixedVector B (Sum.inr 4473) = Sparse.eval nodeValue4473 (mixedVector B) := by
    change mixedMoment B node4473 node4473Labels = _
    exact sound4473 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4475 : mixedVector B (Sum.inr 4475) = Sparse.eval nodeValue4475 (mixedVector B) := by
    change mixedMoment B node4475 node4475Labels = _
    exact sound4475 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1880, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4169, h4172, h4173, h4176, h4341, h4342, h4345, h4455, h4457, h4459, h4473, h4474, h4475, h4495, h4498, h4499, h4503, h4831, h4888, h4889, h4895, reducedSource1593] using sourceEq1880 B hB

theorem rowSound1593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1593 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1593, numericCheck1593, reducedZero1593 B hB hF, mul_zero]

theorem reducedZero1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1594 (mixedVector B) = 0 := by
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1665 : mixedVector B (Sum.inr 1665) = Sparse.eval nodeValue1665 (mixedVector B) := by
    change mixedMoment B node1665 node1665Labels = _
    exact sound1665 B hB hF
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  simpa only [sourceForm1881, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1502, h1507, h1508, h1512, h1664, h1665, h1668, h1698, h1699, h1707, h1708, h1709, h1714, h1715, h1727, h1728, h1739, h2191, h2244, h2245, h2265, reducedSource1594] using sourceEq1881 B hB

theorem rowSound1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1594 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1594, numericCheck1594, reducedZero1594 B hB hF, mul_zero]

theorem reducedZero1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1595 (mixedVector B) = 0 := by
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4171 : mixedVector B (Sum.inr 4171) = Sparse.eval nodeValue4171 (mixedVector B) := by
    change mixedMoment B node4171 node4171Labels = _
    exact sound4171 B hB hF
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4182 : mixedVector B (Sum.inr 4182) = Sparse.eval nodeValue4182 (mixedVector B) := by
    change mixedMoment B node4182 node4182Labels = _
    exact sound4182 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  simpa only [sourceForm1884, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4083, h4171, h4175, h4182, h4344, h4351, h4456, h4458, h4461, h4497, h4502, h4833, h4893, reducedSource1595] using sourceEq1884 B hB

theorem rowSound1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1595 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1595, numericCheck1595, reducedZero1595 B hB hF, mul_zero]

theorem reducedZero1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1596 (mixedVector B) = 0 := by
  have h995 : mixedVector B (Sum.inr 995) = Sparse.eval nodeValue995 (mixedVector B) := by
    change mixedMoment B node995 node995Labels = _
    exact sound995 B hB hF
  have h1940 : mixedVector B (Sum.inr 1940) = Sparse.eval nodeValue1940 (mixedVector B) := by
    change mixedMoment B node1940 node1940Labels = _
    exact sound1940 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2219 : mixedVector B (Sum.inr 2219) = Sparse.eval nodeValue2219 (mixedVector B) := by
    change mixedMoment B node2219 node2219Labels = _
    exact sound2219 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1885, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h995, h1940, h2201, h2219, h2224, h4081, reducedSource1596] using sourceEq1885 B hB

theorem rowSound1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1596 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1596, numericCheck1596, reducedZero1596 B hB hF, mul_zero]

theorem reducedZero1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1597 (mixedVector B) = 0 := by
  have h996 : mixedVector B (Sum.inr 996) = Sparse.eval nodeValue996 (mixedVector B) := by
    change mixedMoment B node996 node996Labels = _
    exact sound996 B hB hF
  have h1941 : mixedVector B (Sum.inr 1941) = Sparse.eval nodeValue1941 (mixedVector B) := by
    change mixedMoment B node1941 node1941Labels = _
    exact sound1941 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1886, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h996, h1941, h2213, h2225, h4082, reducedSource1597] using sourceEq1886 B hB

theorem rowSound1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1597 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1597, numericCheck1597, reducedZero1597 B hB hF, mul_zero]

theorem reducedZero1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1598 (mixedVector B) = 0 := by
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4143 : mixedVector B (Sum.inr 4143) = Sparse.eval nodeValue4143 (mixedVector B) := by
    change mixedMoment B node4143 node4143Labels = _
    exact sound4143 B hB hF
  have h4164 : mixedVector B (Sum.inr 4164) = Sparse.eval nodeValue4164 (mixedVector B) := by
    change mixedMoment B node4164 node4164Labels = _
    exact sound4164 B hB hF
  have h4306 : mixedVector B (Sum.inr 4306) = Sparse.eval nodeValue4306 (mixedVector B) := by
    change mixedMoment B node4306 node4306Labels = _
    exact sound4306 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  simpa only [sourceForm1887, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4079, h4143, h4164, h4306, h4399, h4451, h4833, reducedSource1598] using sourceEq1887 B hB

theorem rowSound1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1598 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1598, numericCheck1598, reducedZero1598 B hB hF, mul_zero]

theorem reducedZero1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1599 (mixedVector B) = 0 := by
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4104 : mixedVector B (Sum.inr 4104) = Sparse.eval nodeValue4104 (mixedVector B) := by
    change mixedMoment B node4104 node4104Labels = _
    exact sound4104 B hB hF
  have h4117 : mixedVector B (Sum.inr 4117) = Sparse.eval nodeValue4117 (mixedVector B) := by
    change mixedMoment B node4117 node4117Labels = _
    exact sound4117 B hB hF
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4236 : mixedVector B (Sum.inr 4236) = Sparse.eval nodeValue4236 (mixedVector B) := by
    change mixedMoment B node4236 node4236Labels = _
    exact sound4236 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4263 : mixedVector B (Sum.inr 4263) = Sparse.eval nodeValue4263 (mixedVector B) := by
    change mixedMoment B node4263 node4263Labels = _
    exact sound4263 B hB hF
  have h4267 : mixedVector B (Sum.inr 4267) = Sparse.eval nodeValue4267 (mixedVector B) := by
    change mixedMoment B node4267 node4267Labels = _
    exact sound4267 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  simpa only [sourceForm1889, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4068, h4100, h4104, h4117, h4232, h4236, h4249, h4252, h4263, h4267, h4451, h4456, h4497, reducedSource1599] using sourceEq1889 B hB

theorem rowSound1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1599 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1599, numericCheck1599, reducedZero1599 B hB hF, mul_zero]

theorem sourceRowsAt1584 : MixedData.sourceRows (1584 : Fin 2425) =
    MixedData.row1584 := by decide +kernel

theorem sourceRowsAt1585 : MixedData.sourceRows (1585 : Fin 2425) =
    MixedData.row1585 := by decide +kernel

theorem sourceRowsAt1586 : MixedData.sourceRows (1586 : Fin 2425) =
    MixedData.row1586 := by decide +kernel

theorem sourceRowsAt1587 : MixedData.sourceRows (1587 : Fin 2425) =
    MixedData.row1587 := by decide +kernel

theorem sourceRowsAt1588 : MixedData.sourceRows (1588 : Fin 2425) =
    MixedData.row1588 := by decide +kernel

theorem sourceRowsAt1589 : MixedData.sourceRows (1589 : Fin 2425) =
    MixedData.row1589 := by decide +kernel

theorem sourceRowsAt1590 : MixedData.sourceRows (1590 : Fin 2425) =
    MixedData.row1590 := by decide +kernel

theorem sourceRowsAt1591 : MixedData.sourceRows (1591 : Fin 2425) =
    MixedData.row1591 := by decide +kernel

theorem sourceRowsAt1592 : MixedData.sourceRows (1592 : Fin 2425) =
    MixedData.row1592 := by decide +kernel

theorem sourceRowsAt1593 : MixedData.sourceRows (1593 : Fin 2425) =
    MixedData.row1593 := by decide +kernel

theorem sourceRowsAt1594 : MixedData.sourceRows (1594 : Fin 2425) =
    MixedData.row1594 := by decide +kernel

theorem sourceRowsAt1595 : MixedData.sourceRows (1595 : Fin 2425) =
    MixedData.row1595 := by decide +kernel

theorem sourceRowsAt1596 : MixedData.sourceRows (1596 : Fin 2425) =
    MixedData.row1596 := by decide +kernel

theorem sourceRowsAt1597 : MixedData.sourceRows (1597 : Fin 2425) =
    MixedData.row1597 := by decide +kernel

theorem sourceRowsAt1598 : MixedData.sourceRows (1598 : Fin 2425) =
    MixedData.row1598 := by decide +kernel

theorem sourceRowsAt1599 : MixedData.sourceRows (1599 : Fin 2425) =
    MixedData.row1599 := by decide +kernel

theorem chunkSound99 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 99) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1584 ∨ k.val = 1585 ∨ k.val = 1586 ∨ k.val = 1587 ∨ k.val = 1588 ∨ k.val = 1589 ∨ k.val = 1590 ∨ k.val = 1591 ∨ k.val = 1592 ∨ k.val = 1593 ∨ k.val = 1594 ∨ k.val = 1595 ∨ k.val = 1596 ∨ k.val = 1597 ∨ k.val = 1598 ∨ k.val = 1599 := by omega
  rcases heq with h1584 | h1585 | h1586 | h1587 | h1588 | h1589 | h1590 | h1591 | h1592 | h1593 | h1594 | h1595 | h1596 | h1597 | h1598 | h1599
  · have he : k = (1584 : Fin 2425) := Fin.ext h1584
    subst k
    rw [sourceRowsAt1584]
    exact rowSound1584 B hB hF
  · have he : k = (1585 : Fin 2425) := Fin.ext h1585
    subst k
    rw [sourceRowsAt1585]
    exact rowSound1585 B hB hF
  · have he : k = (1586 : Fin 2425) := Fin.ext h1586
    subst k
    rw [sourceRowsAt1586]
    exact rowSound1586 B hB hF
  · have he : k = (1587 : Fin 2425) := Fin.ext h1587
    subst k
    rw [sourceRowsAt1587]
    exact rowSound1587 B hB hF
  · have he : k = (1588 : Fin 2425) := Fin.ext h1588
    subst k
    rw [sourceRowsAt1588]
    exact rowSound1588 B hB hF
  · have he : k = (1589 : Fin 2425) := Fin.ext h1589
    subst k
    rw [sourceRowsAt1589]
    exact rowSound1589 B hB hF
  · have he : k = (1590 : Fin 2425) := Fin.ext h1590
    subst k
    rw [sourceRowsAt1590]
    exact rowSound1590 B hB hF
  · have he : k = (1591 : Fin 2425) := Fin.ext h1591
    subst k
    rw [sourceRowsAt1591]
    exact rowSound1591 B hB hF
  · have he : k = (1592 : Fin 2425) := Fin.ext h1592
    subst k
    rw [sourceRowsAt1592]
    exact rowSound1592 B hB hF
  · have he : k = (1593 : Fin 2425) := Fin.ext h1593
    subst k
    rw [sourceRowsAt1593]
    exact rowSound1593 B hB hF
  · have he : k = (1594 : Fin 2425) := Fin.ext h1594
    subst k
    rw [sourceRowsAt1594]
    exact rowSound1594 B hB hF
  · have he : k = (1595 : Fin 2425) := Fin.ext h1595
    subst k
    rw [sourceRowsAt1595]
    exact rowSound1595 B hB hF
  · have he : k = (1596 : Fin 2425) := Fin.ext h1596
    subst k
    rw [sourceRowsAt1596]
    exact rowSound1596 B hB hF
  · have he : k = (1597 : Fin 2425) := Fin.ext h1597
    subst k
    rw [sourceRowsAt1597]
    exact rowSound1597 B hB hF
  · have he : k = (1598 : Fin 2425) := Fin.ext h1598
    subst k
    rw [sourceRowsAt1598]
    exact rowSound1598 B hB hF
  · have he : k = (1599 : Fin 2425) := Fin.ext h1599
    subst k
    rw [sourceRowsAt1599]
    exact rowSound1599 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
