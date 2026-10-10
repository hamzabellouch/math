import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic102
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources60

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1632 (mixedVector B) = 0 := by
  have h1337 : mixedVector B (Sum.inr 1337) = Sparse.eval nodeValue1337 (mixedVector B) := by
    change mixedMoment B node1337 node1337Labels = _
    exact sound1337 B hB hF
  have h2437 : mixedVector B (Sum.inr 2437) = Sparse.eval nodeValue2437 (mixedVector B) := by
    change mixedMoment B node2437 node2437Labels = _
    exact sound2437 B hB hF
  have h2442 : mixedVector B (Sum.inr 2442) = Sparse.eval nodeValue2442 (mixedVector B) := by
    change mixedMoment B node2442 node2442Labels = _
    exact sound2442 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1925, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1337, h2437, h2442, h2485, h2618, h2954, h4091, reducedSource1632] using sourceEq1925 B hB

theorem rowSound1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1632 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1632, numericCheck1632, reducedZero1632 B hB hF, mul_zero]

theorem reducedZero1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1633 (mixedVector B) = 0 := by
  have h2047 : mixedVector B (Sum.inr 2047) = Sparse.eval nodeValue2047 (mixedVector B) := by
    change mixedMoment B node2047 node2047Labels = _
    exact sound2047 B hB hF
  have h3385 : mixedVector B (Sum.inr 3385) = Sparse.eval nodeValue3385 (mixedVector B) := by
    change mixedMoment B node3385 node3385Labels = _
    exact sound3385 B hB hF
  have h3443 : mixedVector B (Sum.inr 3443) = Sparse.eval nodeValue3443 (mixedVector B) := by
    change mixedMoment B node3443 node3443Labels = _
    exact sound3443 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1926, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2047, h3385, h3443, h3468, h3523, h3530, h4081, reducedSource1633] using sourceEq1926 B hB

theorem rowSound1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1633 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1633, numericCheck1633, reducedZero1633 B hB hF, mul_zero]

theorem reducedZero1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1634 (mixedVector B) = 0 := by
  have h1998 : mixedVector B (Sum.inr 1998) = Sparse.eval nodeValue1998 (mixedVector B) := by
    change mixedMoment B node1998 node1998Labels = _
    exact sound1998 B hB hF
  have h2004 : mixedVector B (Sum.inr 2004) = Sparse.eval nodeValue2004 (mixedVector B) := by
    change mixedMoment B node2004 node2004Labels = _
    exact sound2004 B hB hF
  have h2006 : mixedVector B (Sum.inr 2006) = Sparse.eval nodeValue2006 (mixedVector B) := by
    change mixedMoment B node2006 node2006Labels = _
    exact sound2006 B hB hF
  have h2049 : mixedVector B (Sum.inr 2049) = Sparse.eval nodeValue2049 (mixedVector B) := by
    change mixedMoment B node2049 node2049Labels = _
    exact sound2049 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1927, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1998, h2004, h2006, h2049, h2230, h3523, h4081, reducedSource1634] using sourceEq1927 B hB

theorem rowSound1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1634 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1634, numericCheck1634, reducedZero1634 B hB hF, mul_zero]

theorem reducedZero1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1635 (mixedVector B) = 0 := by
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3615 : mixedVector B (Sum.inr 3615) = Sparse.eval nodeValue3615 (mixedVector B) := by
    change mixedMoment B node3615 node3615Labels = _
    exact sound3615 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1929, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3468, h3519, h3523, h3615, h4081, reducedSource1635] using sourceEq1929 B hB

theorem rowSound1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1635 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1635, numericCheck1635, reducedZero1635 B hB hF, mul_zero]

theorem reducedZero1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1636 (mixedVector B) = 0 := by
  have h2006 : mixedVector B (Sum.inr 2006) = Sparse.eval nodeValue2006 (mixedVector B) := by
    change mixedMoment B node2006 node2006Labels = _
    exact sound2006 B hB hF
  have h3339 : mixedVector B (Sum.inr 3339) = Sparse.eval nodeValue3339 (mixedVector B) := by
    change mixedMoment B node3339 node3339Labels = _
    exact sound3339 B hB hF
  have h3343 : mixedVector B (Sum.inr 3343) = Sparse.eval nodeValue3343 (mixedVector B) := by
    change mixedMoment B node3343 node3343Labels = _
    exact sound3343 B hB hF
  have h3353 : mixedVector B (Sum.inr 3353) = Sparse.eval nodeValue3353 (mixedVector B) := by
    change mixedMoment B node3353 node3353Labels = _
    exact sound3353 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1930, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2006, h3339, h3343, h3353, h3468, h3523, h4081, reducedSource1636] using sourceEq1930 B hB

theorem rowSound1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1636 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1636, numericCheck1636, reducedZero1636 B hB hF, mul_zero]

theorem reducedZero1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1637 (mixedVector B) = 0 := by
  have h2118 : mixedVector B (Sum.inr 2118) = Sparse.eval nodeValue2118 (mixedVector B) := by
    change mixedMoment B node2118 node2118Labels = _
    exact sound2118 B hB hF
  have h2121 : mixedVector B (Sum.inr 2121) = Sparse.eval nodeValue2121 (mixedVector B) := by
    change mixedMoment B node2121 node2121Labels = _
    exact sound2121 B hB hF
  have h2123 : mixedVector B (Sum.inr 2123) = Sparse.eval nodeValue2123 (mixedVector B) := by
    change mixedMoment B node2123 node2123Labels = _
    exact sound2123 B hB hF
  have h2129 : mixedVector B (Sum.inr 2129) = Sparse.eval nodeValue2129 (mixedVector B) := by
    change mixedMoment B node2129 node2129Labels = _
    exact sound2129 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1931, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2118, h2121, h2123, h2129, h2216, h2735, h4080, reducedSource1637] using sourceEq1931 B hB

theorem rowSound1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1637 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1637, numericCheck1637, reducedZero1637 B hB hF, mul_zero]

theorem reducedZero1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1638 (mixedVector B) = 0 := by
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2425 : mixedVector B (Sum.inr 2425) = Sparse.eval nodeValue2425 (mixedVector B) := by
    change mixedMoment B node2425 node2425Labels = _
    exact sound2425 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2542 : mixedVector B (Sum.inr 2542) = Sparse.eval nodeValue2542 (mixedVector B) := by
    change mixedMoment B node2542 node2542Labels = _
    exact sound2542 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1932, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1148, h2347, h2425, h2482, h2542, h2553, h4092, reducedSource1638] using sourceEq1932 B hB

theorem rowSound1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1638 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1638, numericCheck1638, reducedZero1638 B hB hF, mul_zero]

theorem reducedZero1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1639 (mixedVector B) = 0 := by
  have h3432 : mixedVector B (Sum.inr 3432) = Sparse.eval nodeValue3432 (mixedVector B) := by
    change mixedMoment B node3432 node3432Labels = _
    exact sound3432 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1933, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3432, h3434, h3437, h3481, h3513, h3519, h4081, reducedSource1639] using sourceEq1933 B hB

theorem rowSound1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1639 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1639, numericCheck1639, reducedZero1639 B hB hF, mul_zero]

theorem reducedZero1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1640 (mixedVector B) = 0 := by
  have h1986 : mixedVector B (Sum.inr 1986) = Sparse.eval nodeValue1986 (mixedVector B) := by
    change mixedMoment B node1986 node1986Labels = _
    exact sound1986 B hB hF
  have h1989 : mixedVector B (Sum.inr 1989) = Sparse.eval nodeValue1989 (mixedVector B) := by
    change mixedMoment B node1989 node1989Labels = _
    exact sound1989 B hB hF
  have h1996 : mixedVector B (Sum.inr 1996) = Sparse.eval nodeValue1996 (mixedVector B) := by
    change mixedMoment B node1996 node1996Labels = _
    exact sound1996 B hB hF
  have h2015 : mixedVector B (Sum.inr 2015) = Sparse.eval nodeValue2015 (mixedVector B) := by
    change mixedMoment B node2015 node2015Labels = _
    exact sound2015 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1934, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1986, h1989, h1996, h2015, h2203, h3513, h4081, reducedSource1640] using sourceEq1934 B hB

theorem rowSound1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1640 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1640, numericCheck1640, reducedZero1640 B hB hF, mul_zero]

theorem reducedZero1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1641 (mixedVector B) = 0 := by
  have h1996 : mixedVector B (Sum.inr 1996) = Sparse.eval nodeValue1996 (mixedVector B) := by
    change mixedMoment B node1996 node1996Labels = _
    exact sound1996 B hB hF
  have h3368 : mixedVector B (Sum.inr 3368) = Sparse.eval nodeValue3368 (mixedVector B) := by
    change mixedMoment B node3368 node3368Labels = _
    exact sound3368 B hB hF
  have h3432 : mixedVector B (Sum.inr 3432) = Sparse.eval nodeValue3432 (mixedVector B) := by
    change mixedMoment B node3432 node3432Labels = _
    exact sound3432 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1935, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1996, h3368, h3432, h3468, h3513, h3519, h4081, reducedSource1641] using sourceEq1935 B hB

theorem rowSound1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1641 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1641, numericCheck1641, reducedZero1641 B hB hF, mul_zero]

theorem reducedZero1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1642 (mixedVector B) = 0 := by
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3608 : mixedVector B (Sum.inr 3608) = Sparse.eval nodeValue3608 (mixedVector B) := by
    change mixedMoment B node3608 node3608Labels = _
    exact sound3608 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1936, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2203, h3468, h3481, h3513, h3530, h3608, h4081, reducedSource1642] using sourceEq1936 B hB

theorem rowSound1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1642 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1642, numericCheck1642, reducedZero1642 B hB hF, mul_zero]

theorem reducedZero1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1643 (mixedVector B) = 0 := by
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1937, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1327, h2422, h2429, h2485, h2543, h2924, h4091, reducedSource1643] using sourceEq1937 B hB

theorem rowSound1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1643 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1643, numericCheck1643, reducedZero1643 B hB hF, mul_zero]

theorem reducedZero1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1644 (mixedVector B) = 0 := by
  have h1150 : mixedVector B (Sum.inr 1150) = Sparse.eval nodeValue1150 (mixedVector B) := by
    change mixedMoment B node1150 node1150Labels = _
    exact sound1150 B hB hF
  have h2349 : mixedVector B (Sum.inr 2349) = Sparse.eval nodeValue2349 (mixedVector B) := by
    change mixedMoment B node2349 node2349Labels = _
    exact sound2349 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1938, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1150, h2349, h2429, h2543, h2556, h4091, reducedSource1644] using sourceEq1938 B hB

theorem rowSound1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1644 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1644, numericCheck1644, reducedZero1644 B hB hF, mul_zero]

theorem reducedZero1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1645 (mixedVector B) = 0 := by
  have h2071 : mixedVector B (Sum.inr 2071) = Sparse.eval nodeValue2071 (mixedVector B) := by
    change mixedMoment B node2071 node2071Labels = _
    exact sound2071 B hB hF
  have h2073 : mixedVector B (Sum.inr 2073) = Sparse.eval nodeValue2073 (mixedVector B) := by
    change mixedMoment B node2073 node2073Labels = _
    exact sound2073 B hB hF
  have h2077 : mixedVector B (Sum.inr 2077) = Sparse.eval nodeValue2077 (mixedVector B) := by
    change mixedMoment B node2077 node2077Labels = _
    exact sound2077 B hB hF
  have h2086 : mixedVector B (Sum.inr 2086) = Sparse.eval nodeValue2086 (mixedVector B) := by
    change mixedMoment B node2086 node2086Labels = _
    exact sound2086 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1939, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2071, h2073, h2077, h2086, h2191, h3558, h4079, reducedSource1645] using sourceEq1939 B hB

theorem rowSound1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1645 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1645, numericCheck1645, reducedZero1645 B hB hF, mul_zero]

theorem reducedZero1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1646 (mixedVector B) = 0 := by
  have h2454 : mixedVector B (Sum.inr 2454) = Sparse.eval nodeValue2454 (mixedVector B) := by
    change mixedMoment B node2454 node2454Labels = _
    exact sound2454 B hB hF
  have h2456 : mixedVector B (Sum.inr 2456) = Sparse.eval nodeValue2456 (mixedVector B) := by
    change mixedMoment B node2456 node2456Labels = _
    exact sound2456 B hB hF
  have h2462 : mixedVector B (Sum.inr 2462) = Sparse.eval nodeValue2462 (mixedVector B) := by
    change mixedMoment B node2462 node2462Labels = _
    exact sound2462 B hB hF
  have h2491 : mixedVector B (Sum.inr 2491) = Sparse.eval nodeValue2491 (mixedVector B) := by
    change mixedMoment B node2491 node2491Labels = _
    exact sound2491 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1940, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2454, h2456, h2462, h2491, h2698, h3796, h4090, reducedSource1646] using sourceEq1940 B hB

theorem rowSound1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1646 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1646, numericCheck1646, reducedZero1646 B hB hF, mul_zero]

theorem reducedZero1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1647 (mixedVector B) = 0 := by
  have h1992 : mixedVector B (Sum.inr 1992) = Sparse.eval nodeValue1992 (mixedVector B) := by
    change mixedMoment B node1992 node1992Labels = _
    exact sound1992 B hB hF
  have h1994 : mixedVector B (Sum.inr 1994) = Sparse.eval nodeValue1994 (mixedVector B) := by
    change mixedMoment B node1994 node1994Labels = _
    exact sound1994 B hB hF
  have h2000 : mixedVector B (Sum.inr 2000) = Sparse.eval nodeValue2000 (mixedVector B) := by
    change mixedMoment B node2000 node2000Labels = _
    exact sound2000 B hB hF
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1942, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1992, h1994, h2000, h2031, h2216, h3517, h4080, reducedSource1647] using sourceEq1942 B hB

theorem rowSound1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1647 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1647, numericCheck1647, reducedZero1647 B hB hF, mul_zero]

theorem sourceRowsAt1632 : MixedData.sourceRows (1632 : Fin 2425) =
    MixedData.row1632 := by decide +kernel

theorem sourceRowsAt1633 : MixedData.sourceRows (1633 : Fin 2425) =
    MixedData.row1633 := by decide +kernel

theorem sourceRowsAt1634 : MixedData.sourceRows (1634 : Fin 2425) =
    MixedData.row1634 := by decide +kernel

theorem sourceRowsAt1635 : MixedData.sourceRows (1635 : Fin 2425) =
    MixedData.row1635 := by decide +kernel

theorem sourceRowsAt1636 : MixedData.sourceRows (1636 : Fin 2425) =
    MixedData.row1636 := by decide +kernel

theorem sourceRowsAt1637 : MixedData.sourceRows (1637 : Fin 2425) =
    MixedData.row1637 := by decide +kernel

theorem sourceRowsAt1638 : MixedData.sourceRows (1638 : Fin 2425) =
    MixedData.row1638 := by decide +kernel

theorem sourceRowsAt1639 : MixedData.sourceRows (1639 : Fin 2425) =
    MixedData.row1639 := by decide +kernel

theorem sourceRowsAt1640 : MixedData.sourceRows (1640 : Fin 2425) =
    MixedData.row1640 := by decide +kernel

theorem sourceRowsAt1641 : MixedData.sourceRows (1641 : Fin 2425) =
    MixedData.row1641 := by decide +kernel

theorem sourceRowsAt1642 : MixedData.sourceRows (1642 : Fin 2425) =
    MixedData.row1642 := by decide +kernel

theorem sourceRowsAt1643 : MixedData.sourceRows (1643 : Fin 2425) =
    MixedData.row1643 := by decide +kernel

theorem sourceRowsAt1644 : MixedData.sourceRows (1644 : Fin 2425) =
    MixedData.row1644 := by decide +kernel

theorem sourceRowsAt1645 : MixedData.sourceRows (1645 : Fin 2425) =
    MixedData.row1645 := by decide +kernel

theorem sourceRowsAt1646 : MixedData.sourceRows (1646 : Fin 2425) =
    MixedData.row1646 := by decide +kernel

theorem sourceRowsAt1647 : MixedData.sourceRows (1647 : Fin 2425) =
    MixedData.row1647 := by decide +kernel

theorem chunkSound102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 102) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1632 ∨ k.val = 1633 ∨ k.val = 1634 ∨ k.val = 1635 ∨ k.val = 1636 ∨ k.val = 1637 ∨ k.val = 1638 ∨ k.val = 1639 ∨ k.val = 1640 ∨ k.val = 1641 ∨ k.val = 1642 ∨ k.val = 1643 ∨ k.val = 1644 ∨ k.val = 1645 ∨ k.val = 1646 ∨ k.val = 1647 := by omega
  rcases heq with h1632 | h1633 | h1634 | h1635 | h1636 | h1637 | h1638 | h1639 | h1640 | h1641 | h1642 | h1643 | h1644 | h1645 | h1646 | h1647
  · have he : k = (1632 : Fin 2425) := Fin.ext h1632
    subst k
    rw [sourceRowsAt1632]
    exact rowSound1632 B hB hF
  · have he : k = (1633 : Fin 2425) := Fin.ext h1633
    subst k
    rw [sourceRowsAt1633]
    exact rowSound1633 B hB hF
  · have he : k = (1634 : Fin 2425) := Fin.ext h1634
    subst k
    rw [sourceRowsAt1634]
    exact rowSound1634 B hB hF
  · have he : k = (1635 : Fin 2425) := Fin.ext h1635
    subst k
    rw [sourceRowsAt1635]
    exact rowSound1635 B hB hF
  · have he : k = (1636 : Fin 2425) := Fin.ext h1636
    subst k
    rw [sourceRowsAt1636]
    exact rowSound1636 B hB hF
  · have he : k = (1637 : Fin 2425) := Fin.ext h1637
    subst k
    rw [sourceRowsAt1637]
    exact rowSound1637 B hB hF
  · have he : k = (1638 : Fin 2425) := Fin.ext h1638
    subst k
    rw [sourceRowsAt1638]
    exact rowSound1638 B hB hF
  · have he : k = (1639 : Fin 2425) := Fin.ext h1639
    subst k
    rw [sourceRowsAt1639]
    exact rowSound1639 B hB hF
  · have he : k = (1640 : Fin 2425) := Fin.ext h1640
    subst k
    rw [sourceRowsAt1640]
    exact rowSound1640 B hB hF
  · have he : k = (1641 : Fin 2425) := Fin.ext h1641
    subst k
    rw [sourceRowsAt1641]
    exact rowSound1641 B hB hF
  · have he : k = (1642 : Fin 2425) := Fin.ext h1642
    subst k
    rw [sourceRowsAt1642]
    exact rowSound1642 B hB hF
  · have he : k = (1643 : Fin 2425) := Fin.ext h1643
    subst k
    rw [sourceRowsAt1643]
    exact rowSound1643 B hB hF
  · have he : k = (1644 : Fin 2425) := Fin.ext h1644
    subst k
    rw [sourceRowsAt1644]
    exact rowSound1644 B hB hF
  · have he : k = (1645 : Fin 2425) := Fin.ext h1645
    subst k
    rw [sourceRowsAt1645]
    exact rowSound1645 B hB hF
  · have he : k = (1646 : Fin 2425) := Fin.ext h1646
    subst k
    rw [sourceRowsAt1646]
    exact rowSound1646 B hB hF
  · have he : k = (1647 : Fin 2425) := Fin.ext h1647
    subst k
    rw [sourceRowsAt1647]
    exact rowSound1647 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
