import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic105
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources62

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1680 (mixedVector B) = 0 := by
  have h2390 : mixedVector B (Sum.inr 2390) = Sparse.eval nodeValue2390 (mixedVector B) := by
    change mixedMoment B node2390 node2390Labels = _
    exact sound2390 B hB hF
  have h2393 : mixedVector B (Sum.inr 2393) = Sparse.eval nodeValue2393 (mixedVector B) := by
    change mixedMoment B node2393 node2393Labels = _
    exact sound2393 B hB hF
  have h2395 : mixedVector B (Sum.inr 2395) = Sparse.eval nodeValue2395 (mixedVector B) := by
    change mixedMoment B node2395 node2395Labels = _
    exact sound2395 B hB hF
  have h2404 : mixedVector B (Sum.inr 2404) = Sparse.eval nodeValue2404 (mixedVector B) := by
    change mixedMoment B node2404 node2404Labels = _
    exact sound2404 B hB hF
  have h2678 : mixedVector B (Sum.inr 2678) = Sparse.eval nodeValue2678 (mixedVector B) := by
    change mixedMoment B node2678 node2678Labels = _
    exact sound2678 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1981, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2390, h2393, h2395, h2404, h2678, h3771, h4088, reducedSource1680] using sourceEq1981 B hB

theorem rowSound1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1680 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1680, numericCheck1680, reducedZero1680 B hB hF, mul_zero]

theorem reducedZero1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1681 (mixedVector B) = 0 := by
  have h1898 : mixedVector B (Sum.inr 1898) = Sparse.eval nodeValue1898 (mixedVector B) := by
    change mixedMoment B node1898 node1898Labels = _
    exact sound1898 B hB hF
  have h1901 : mixedVector B (Sum.inr 1901) = Sparse.eval nodeValue1901 (mixedVector B) := by
    change mixedMoment B node1901 node1901Labels = _
    exact sound1901 B hB hF
  have h1912 : mixedVector B (Sum.inr 1912) = Sparse.eval nodeValue1912 (mixedVector B) := by
    change mixedMoment B node1912 node1912Labels = _
    exact sound1912 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1987, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1898, h1901, h1912, h2191, h3460, h4079, reducedSource1681] using sourceEq1987 B hB

theorem rowSound1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1681 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1681, numericCheck1681, reducedZero1681 B hB hF, mul_zero]

theorem reducedZero1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1682 (mixedVector B) = 0 := by
  have h2076 : mixedVector B (Sum.inr 2076) = Sparse.eval nodeValue2076 (mixedVector B) := by
    change mixedMoment B node2076 node2076Labels = _
    exact sound2076 B hB hF
  have h2080 : mixedVector B (Sum.inr 2080) = Sparse.eval nodeValue2080 (mixedVector B) := by
    change mixedMoment B node2080 node2080Labels = _
    exact sound2080 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2102 : mixedVector B (Sum.inr 2102) = Sparse.eval nodeValue2102 (mixedVector B) := by
    change mixedMoment B node2102 node2102Labels = _
    exact sound2102 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1991, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2076, h2080, h2082, h2102, h2206, h3565, h4080, reducedSource1682] using sourceEq1991 B hB

theorem rowSound1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1682 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1682, numericCheck1682, reducedZero1682 B hB hF, mul_zero]

theorem reducedZero1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1683 (mixedVector B) = 0 := by
  have h1325 : mixedVector B (Sum.inr 1325) = Sparse.eval nodeValue1325 (mixedVector B) := by
    change mixedMoment B node1325 node1325Labels = _
    exact sound1325 B hB hF
  have h2811 : mixedVector B (Sum.inr 2811) = Sparse.eval nodeValue2811 (mixedVector B) := by
    change mixedMoment B node2811 node2811Labels = _
    exact sound2811 B hB hF
  have h2820 : mixedVector B (Sum.inr 2820) = Sparse.eval nodeValue2820 (mixedVector B) := by
    change mixedMoment B node2820 node2820Labels = _
    exact sound2820 B hB hF
  have h2886 : mixedVector B (Sum.inr 2886) = Sparse.eval nodeValue2886 (mixedVector B) := by
    change mixedMoment B node2886 node2886Labels = _
    exact sound2886 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1993, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1325, h2811, h2820, h2886, h2889, h4092, reducedSource1683] using sourceEq1993 B hB

theorem rowSound1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1683 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1683, numericCheck1683, reducedZero1683 B hB hF, mul_zero]

theorem reducedZero1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1684 (mixedVector B) = 0 := by
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4476 : mixedVector B (Sum.inr 4476) = Sparse.eval nodeValue4476 (mixedVector B) := by
    change mixedMoment B node4476 node4476Labels = _
    exact sound4476 B hB hF
  have h4547 : mixedVector B (Sum.inr 4547) = Sparse.eval nodeValue4547 (mixedVector B) := by
    change mixedMoment B node4547 node4547Labels = _
    exact sound4547 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h5034 : mixedVector B (Sum.inr 5034) = Sparse.eval nodeValue5034 (mixedVector B) := by
    change mixedMoment B node5034 node5034Labels = _
    exact sound5034 B hB hF
  have h5087 : mixedVector B (Sum.inr 5087) = Sparse.eval nodeValue5087 (mixedVector B) := by
    change mixedMoment B node5087 node5087Labels = _
    exact sound5087 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5268 : mixedVector B (Sum.inr 5268) = Sparse.eval nodeValue5268 (mixedVector B) := by
    change mixedMoment B node5268 node5268Labels = _
    exact sound5268 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  simpa only [sourceForm1996, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4367, h4370, h4374, h4476, h4547, h4559, h4609, h4944, h4953, h4972, h5034, h5087, h5102, h5111, h5139, h5204, h5207, h5268, h5275, h5302, h5413, reducedSource1684] using sourceEq1996 B hB

theorem rowSound1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1684 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1684, numericCheck1684, reducedZero1684 B hB hF, mul_zero]

theorem reducedZero1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1685 (mixedVector B) = 0 := by
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h3266 : mixedVector B (Sum.inr 3266) = Sparse.eval nodeValue3266 (mixedVector B) := by
    change mixedMoment B node3266 node3266Labels = _
    exact sound3266 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3423 : mixedVector B (Sum.inr 3423) = Sparse.eval nodeValue3423 (mixedVector B) := by
    change mixedMoment B node3423 node3423Labels = _
    exact sound3423 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3471 : mixedVector B (Sum.inr 3471) = Sparse.eval nodeValue3471 (mixedVector B) := by
    change mixedMoment B node3471 node3471Labels = _
    exact sound3471 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3624 : mixedVector B (Sum.inr 3624) = Sparse.eval nodeValue3624 (mixedVector B) := by
    change mixedMoment B node3624 node3624Labels = _
    exact sound3624 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3631 : mixedVector B (Sum.inr 3631) = Sparse.eval nodeValue3631 (mixedVector B) := by
    change mixedMoment B node3631 node3631Labels = _
    exact sound3631 B hB hF
  have h3817 : mixedVector B (Sum.inr 3817) = Sparse.eval nodeValue3817 (mixedVector B) := by
    change mixedMoment B node3817 node3817Labels = _
    exact sound3817 B hB hF
  simpa only [sourceForm1997, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1720, h1722, h1729, h1748, h3266, h3277, h3302, h3413, h3423, h3451, h3457, h3471, h3472, h3485, h3523, h3548, h3549, h3624, h3626, h3631, h3817, reducedSource1685] using sourceEq1997 B hB

theorem rowSound1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1685 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1685, numericCheck1685, reducedZero1685 B hB hF, mul_zero]

theorem reducedZero1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1686 (mixedVector B) = 0 := by
  have h4219 : mixedVector B (Sum.inr 4219) = Sparse.eval nodeValue4219 (mixedVector B) := by
    change mixedMoment B node4219 node4219Labels = _
    exact sound4219 B hB hF
  have h4225 : mixedVector B (Sum.inr 4225) = Sparse.eval nodeValue4225 (mixedVector B) := by
    change mixedMoment B node4225 node4225Labels = _
    exact sound4225 B hB hF
  have h4229 : mixedVector B (Sum.inr 4229) = Sparse.eval nodeValue4229 (mixedVector B) := by
    change mixedMoment B node4229 node4229Labels = _
    exact sound4229 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4514 : mixedVector B (Sum.inr 4514) = Sparse.eval nodeValue4514 (mixedVector B) := by
    change mixedMoment B node4514 node4514Labels = _
    exact sound4514 B hB hF
  have h4519 : mixedVector B (Sum.inr 4519) = Sparse.eval nodeValue4519 (mixedVector B) := by
    change mixedMoment B node4519 node4519Labels = _
    exact sound4519 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4650 : mixedVector B (Sum.inr 4650) = Sparse.eval nodeValue4650 (mixedVector B) := by
    change mixedMoment B node4650 node4650Labels = _
    exact sound4650 B hB hF
  have h4657 : mixedVector B (Sum.inr 4657) = Sparse.eval nodeValue4657 (mixedVector B) := by
    change mixedMoment B node4657 node4657Labels = _
    exact sound4657 B hB hF
  have h4713 : mixedVector B (Sum.inr 4713) = Sparse.eval nodeValue4713 (mixedVector B) := by
    change mixedMoment B node4713 node4713Labels = _
    exact sound4713 B hB hF
  have h4719 : mixedVector B (Sum.inr 4719) = Sparse.eval nodeValue4719 (mixedVector B) := by
    change mixedMoment B node4719 node4719Labels = _
    exact sound4719 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  simpa only [sourceForm1998, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4219, h4225, h4229, h4270, h4514, h4519, h4605, h4650, h4657, h4713, h4719, h4742, h4807, h4839, h4845, h4890, h4896, h5204, h5207, h5294, h5443, reducedSource1686] using sourceEq1998 B hB

theorem rowSound1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1686 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1686, numericCheck1686, reducedZero1686 B hB hF, mul_zero]

theorem reducedZero1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1687 (mixedVector B) = 0 := by
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4358 : mixedVector B (Sum.inr 4358) = Sparse.eval nodeValue4358 (mixedVector B) := by
    change mixedMoment B node4358 node4358Labels = _
    exact sound4358 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4371 : mixedVector B (Sum.inr 4371) = Sparse.eval nodeValue4371 (mixedVector B) := by
    change mixedMoment B node4371 node4371Labels = _
    exact sound4371 B hB hF
  have h4375 : mixedVector B (Sum.inr 4375) = Sparse.eval nodeValue4375 (mixedVector B) := by
    change mixedMoment B node4375 node4375Labels = _
    exact sound4375 B hB hF
  have h4478 : mixedVector B (Sum.inr 4478) = Sparse.eval nodeValue4478 (mixedVector B) := by
    change mixedMoment B node4478 node4478Labels = _
    exact sound4478 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4682 : mixedVector B (Sum.inr 4682) = Sparse.eval nodeValue4682 (mixedVector B) := by
    change mixedMoment B node4682 node4682Labels = _
    exact sound4682 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4761 : mixedVector B (Sum.inr 4761) = Sparse.eval nodeValue4761 (mixedVector B) := by
    change mixedMoment B node4761 node4761Labels = _
    exact sound4761 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  have h5205 : mixedVector B (Sum.inr 5205) = Sparse.eval nodeValue5205 (mixedVector B) := by
    change mixedMoment B node5205 node5205Labels = _
    exact sound5205 B hB hF
  have h5206 : mixedVector B (Sum.inr 5206) = Sparse.eval nodeValue5206 (mixedVector B) := by
    change mixedMoment B node5206 node5206Labels = _
    exact sound5206 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  simpa only [sourceForm2000, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4347, h4358, h4361, h4371, h4375, h4478, h4507, h4682, h4693, h4761, h4770, h4817, h4835, h4843, h4846, h4899, h4901, h5205, h5206, h5275, h5276, reducedSource1687] using sourceEq2000 B hB

theorem rowSound1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1687 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1687, numericCheck1687, reducedZero1687 B hB hF, mul_zero]

theorem reducedZero1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1688 (mixedVector B) = 0 := by
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1742 : mixedVector B (Sum.inr 1742) = Sparse.eval nodeValue1742 (mixedVector B) := by
    change mixedMoment B node1742 node1742Labels = _
    exact sound1742 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2153 : mixedVector B (Sum.inr 2153) = Sparse.eval nodeValue2153 (mixedVector B) := by
    change mixedMoment B node2153 node2153Labels = _
    exact sound2153 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2175 : mixedVector B (Sum.inr 2175) = Sparse.eval nodeValue2175 (mixedVector B) := by
    change mixedMoment B node2175 node2175Labels = _
    exact sound2175 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  simpa only [sourceForm2001, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1676, h1694, h1695, h1742, h1743, h1746, h1756, h2153, h2169, h2175, h2186, h2206, h2207, h2229, h2230, h2293, h2294, h2687, h2706, h2743, h2744, reducedSource1688] using sourceEq2001 B hB

theorem rowSound1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1688 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1688, numericCheck1688, reducedZero1688 B hB hF, mul_zero]

theorem reducedZero1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1689 (mixedVector B) = 0 := by
  have h939 : mixedVector B (Sum.inr 939) = Sparse.eval nodeValue939 (mixedVector B) := by
    change mixedMoment B node939 node939Labels = _
    exact sound939 B hB hF
  have h1819 : mixedVector B (Sum.inr 1819) = Sparse.eval nodeValue1819 (mixedVector B) := by
    change mixedMoment B node1819 node1819Labels = _
    exact sound1819 B hB hF
  have h1970 : mixedVector B (Sum.inr 1970) = Sparse.eval nodeValue1970 (mixedVector B) := by
    change mixedMoment B node1970 node1970Labels = _
    exact sound1970 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2066 : mixedVector B (Sum.inr 2066) = Sparse.eval nodeValue2066 (mixedVector B) := by
    change mixedMoment B node2066 node2066Labels = _
    exact sound2066 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2002, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h939, h1819, h1970, h2062, h2066, h4084, reducedSource1689] using sourceEq2002 B hB

theorem rowSound1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1689 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1689, numericCheck1689, reducedZero1689 B hB hF, mul_zero]

theorem reducedZero1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1690 (mixedVector B) = 0 := by
  have h1315 : mixedVector B (Sum.inr 1315) = Sparse.eval nodeValue1315 (mixedVector B) := by
    change mixedMoment B node1315 node1315Labels = _
    exact sound1315 B hB hF
  have h1961 : mixedVector B (Sum.inr 1961) = Sparse.eval nodeValue1961 (mixedVector B) := by
    change mixedMoment B node1961 node1961Labels = _
    exact sound1961 B hB hF
  have h1970 : mixedVector B (Sum.inr 1970) = Sparse.eval nodeValue1970 (mixedVector B) := by
    change mixedMoment B node1970 node1970Labels = _
    exact sound1970 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2003, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1315, h1961, h1970, h2062, h2879, h4084, reducedSource1690] using sourceEq2003 B hB

theorem rowSound1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1690 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1690, numericCheck1690, reducedZero1690 B hB hF, mul_zero]

theorem reducedZero1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1691 (mixedVector B) = 0 := by
  have h2128 : mixedVector B (Sum.inr 2128) = Sparse.eval nodeValue2128 (mixedVector B) := by
    change mixedMoment B node2128 node2128Labels = _
    exact sound2128 B hB hF
  have h2130 : mixedVector B (Sum.inr 2130) = Sparse.eval nodeValue2130 (mixedVector B) := by
    change mixedMoment B node2130 node2130Labels = _
    exact sound2130 B hB hF
  have h2137 : mixedVector B (Sum.inr 2137) = Sparse.eval nodeValue2137 (mixedVector B) := by
    change mixedMoment B node2137 node2137Labels = _
    exact sound2137 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2008, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2128, h2130, h2137, h2276, h2687, h4082, reducedSource1691] using sourceEq2008 B hB

theorem rowSound1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1691 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1691, numericCheck1691, reducedZero1691 B hB hF, mul_zero]

theorem reducedZero1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1692 (mixedVector B) = 0 := by
  have h2085 : mixedVector B (Sum.inr 2085) = Sparse.eval nodeValue2085 (mixedVector B) := by
    change mixedMoment B node2085 node2085Labels = _
    exact sound2085 B hB hF
  have h2087 : mixedVector B (Sum.inr 2087) = Sparse.eval nodeValue2087 (mixedVector B) := by
    change mixedMoment B node2087 node2087Labels = _
    exact sound2087 B hB hF
  have h2093 : mixedVector B (Sum.inr 2093) = Sparse.eval nodeValue2093 (mixedVector B) := by
    change mixedMoment B node2093 node2093Labels = _
    exact sound2093 B hB hF
  have h2101 : mixedVector B (Sum.inr 2101) = Sparse.eval nodeValue2101 (mixedVector B) := by
    change mixedMoment B node2101 node2101Labels = _
    exact sound2101 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2009, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2085, h2087, h2093, h2101, h2242, h3570, h4080, reducedSource1692] using sourceEq2009 B hB

theorem rowSound1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1692 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1692, numericCheck1692, reducedZero1692 B hB hF, mul_zero]

theorem reducedZero1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1693 (mixedVector B) = 0 := by
  have h2492 : mixedVector B (Sum.inr 2492) = Sparse.eval nodeValue2492 (mixedVector B) := by
    change mixedMoment B node2492 node2492Labels = _
    exact sound2492 B hB hF
  have h2606 : mixedVector B (Sum.inr 2606) = Sparse.eval nodeValue2606 (mixedVector B) := by
    change mixedMoment B node2606 node2606Labels = _
    exact sound2606 B hB hF
  have h2608 : mixedVector B (Sum.inr 2608) = Sparse.eval nodeValue2608 (mixedVector B) := by
    change mixedMoment B node2608 node2608Labels = _
    exact sound2608 B hB hF
  have h2629 : mixedVector B (Sum.inr 2629) = Sparse.eval nodeValue2629 (mixedVector B) := by
    change mixedMoment B node2629 node2629Labels = _
    exact sound2629 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2011, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2492, h2606, h2608, h2629, h2672, h3811, h4088, reducedSource1693] using sourceEq2011 B hB

theorem rowSound1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1693 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1693, numericCheck1693, reducedZero1693 B hB hF, mul_zero]

theorem reducedZero1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1694 (mixedVector B) = 0 := by
  have h2030 : mixedVector B (Sum.inr 2030) = Sparse.eval nodeValue2030 (mixedVector B) := by
    change mixedMoment B node2030 node2030Labels = _
    exact sound2030 B hB hF
  have h2032 : mixedVector B (Sum.inr 2032) = Sparse.eval nodeValue2032 (mixedVector B) := by
    change mixedMoment B node2032 node2032Labels = _
    exact sound2032 B hB hF
  have h2038 : mixedVector B (Sum.inr 2038) = Sparse.eval nodeValue2038 (mixedVector B) := by
    change mixedMoment B node2038 node2038Labels = _
    exact sound2038 B hB hF
  have h2048 : mixedVector B (Sum.inr 2048) = Sparse.eval nodeValue2048 (mixedVector B) := by
    change mixedMoment B node2048 node2048Labels = _
    exact sound2048 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2012, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2030, h2032, h2038, h2048, h2276, h3538, h4082, reducedSource1694] using sourceEq2012 B hB

theorem rowSound1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1694 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1694, numericCheck1694, reducedZero1694 B hB hF, mul_zero]

theorem reducedZero1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1695 (mixedVector B) = 0 := by
  have h2469 : mixedVector B (Sum.inr 2469) = Sparse.eval nodeValue2469 (mixedVector B) := by
    change mixedMoment B node2469 node2469Labels = _
    exact sound2469 B hB hF
  have h2609 : mixedVector B (Sum.inr 2609) = Sparse.eval nodeValue2609 (mixedVector B) := by
    change mixedMoment B node2609 node2609Labels = _
    exact sound2609 B hB hF
  have h2613 : mixedVector B (Sum.inr 2613) = Sparse.eval nodeValue2613 (mixedVector B) := by
    change mixedMoment B node2613 node2613Labels = _
    exact sound2613 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm2014, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2469, h2609, h2613, h2694, h3799, h4090, reducedSource1695] using sourceEq2014 B hB

theorem rowSound1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1695 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1695, numericCheck1695, reducedZero1695 B hB hF, mul_zero]

theorem sourceRowsAt1680 : MixedData.sourceRows (1680 : Fin 2425) =
    MixedData.row1680 := by decide +kernel

theorem sourceRowsAt1681 : MixedData.sourceRows (1681 : Fin 2425) =
    MixedData.row1681 := by decide +kernel

theorem sourceRowsAt1682 : MixedData.sourceRows (1682 : Fin 2425) =
    MixedData.row1682 := by decide +kernel

theorem sourceRowsAt1683 : MixedData.sourceRows (1683 : Fin 2425) =
    MixedData.row1683 := by decide +kernel

theorem sourceRowsAt1684 : MixedData.sourceRows (1684 : Fin 2425) =
    MixedData.row1684 := by decide +kernel

theorem sourceRowsAt1685 : MixedData.sourceRows (1685 : Fin 2425) =
    MixedData.row1685 := by decide +kernel

theorem sourceRowsAt1686 : MixedData.sourceRows (1686 : Fin 2425) =
    MixedData.row1686 := by decide +kernel

theorem sourceRowsAt1687 : MixedData.sourceRows (1687 : Fin 2425) =
    MixedData.row1687 := by decide +kernel

theorem sourceRowsAt1688 : MixedData.sourceRows (1688 : Fin 2425) =
    MixedData.row1688 := by decide +kernel

theorem sourceRowsAt1689 : MixedData.sourceRows (1689 : Fin 2425) =
    MixedData.row1689 := by decide +kernel

theorem sourceRowsAt1690 : MixedData.sourceRows (1690 : Fin 2425) =
    MixedData.row1690 := by decide +kernel

theorem sourceRowsAt1691 : MixedData.sourceRows (1691 : Fin 2425) =
    MixedData.row1691 := by decide +kernel

theorem sourceRowsAt1692 : MixedData.sourceRows (1692 : Fin 2425) =
    MixedData.row1692 := by decide +kernel

theorem sourceRowsAt1693 : MixedData.sourceRows (1693 : Fin 2425) =
    MixedData.row1693 := by decide +kernel

theorem sourceRowsAt1694 : MixedData.sourceRows (1694 : Fin 2425) =
    MixedData.row1694 := by decide +kernel

theorem sourceRowsAt1695 : MixedData.sourceRows (1695 : Fin 2425) =
    MixedData.row1695 := by decide +kernel

theorem chunkSound105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 105) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1680 ∨ k.val = 1681 ∨ k.val = 1682 ∨ k.val = 1683 ∨ k.val = 1684 ∨ k.val = 1685 ∨ k.val = 1686 ∨ k.val = 1687 ∨ k.val = 1688 ∨ k.val = 1689 ∨ k.val = 1690 ∨ k.val = 1691 ∨ k.val = 1692 ∨ k.val = 1693 ∨ k.val = 1694 ∨ k.val = 1695 := by omega
  rcases heq with h1680 | h1681 | h1682 | h1683 | h1684 | h1685 | h1686 | h1687 | h1688 | h1689 | h1690 | h1691 | h1692 | h1693 | h1694 | h1695
  · have he : k = (1680 : Fin 2425) := Fin.ext h1680
    subst k
    rw [sourceRowsAt1680]
    exact rowSound1680 B hB hF
  · have he : k = (1681 : Fin 2425) := Fin.ext h1681
    subst k
    rw [sourceRowsAt1681]
    exact rowSound1681 B hB hF
  · have he : k = (1682 : Fin 2425) := Fin.ext h1682
    subst k
    rw [sourceRowsAt1682]
    exact rowSound1682 B hB hF
  · have he : k = (1683 : Fin 2425) := Fin.ext h1683
    subst k
    rw [sourceRowsAt1683]
    exact rowSound1683 B hB hF
  · have he : k = (1684 : Fin 2425) := Fin.ext h1684
    subst k
    rw [sourceRowsAt1684]
    exact rowSound1684 B hB hF
  · have he : k = (1685 : Fin 2425) := Fin.ext h1685
    subst k
    rw [sourceRowsAt1685]
    exact rowSound1685 B hB hF
  · have he : k = (1686 : Fin 2425) := Fin.ext h1686
    subst k
    rw [sourceRowsAt1686]
    exact rowSound1686 B hB hF
  · have he : k = (1687 : Fin 2425) := Fin.ext h1687
    subst k
    rw [sourceRowsAt1687]
    exact rowSound1687 B hB hF
  · have he : k = (1688 : Fin 2425) := Fin.ext h1688
    subst k
    rw [sourceRowsAt1688]
    exact rowSound1688 B hB hF
  · have he : k = (1689 : Fin 2425) := Fin.ext h1689
    subst k
    rw [sourceRowsAt1689]
    exact rowSound1689 B hB hF
  · have he : k = (1690 : Fin 2425) := Fin.ext h1690
    subst k
    rw [sourceRowsAt1690]
    exact rowSound1690 B hB hF
  · have he : k = (1691 : Fin 2425) := Fin.ext h1691
    subst k
    rw [sourceRowsAt1691]
    exact rowSound1691 B hB hF
  · have he : k = (1692 : Fin 2425) := Fin.ext h1692
    subst k
    rw [sourceRowsAt1692]
    exact rowSound1692 B hB hF
  · have he : k = (1693 : Fin 2425) := Fin.ext h1693
    subst k
    rw [sourceRowsAt1693]
    exact rowSound1693 B hB hF
  · have he : k = (1694 : Fin 2425) := Fin.ext h1694
    subst k
    rw [sourceRowsAt1694]
    exact rowSound1694 B hB hF
  · have he : k = (1695 : Fin 2425) := Fin.ext h1695
    subst k
    rw [sourceRowsAt1695]
    exact rowSound1695 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
