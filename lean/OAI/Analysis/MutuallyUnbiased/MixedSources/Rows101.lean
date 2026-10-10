import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic101
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources60

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1616 (mixedVector B) = 0 := by
  have h1903 : mixedVector B (Sum.inr 1903) = Sparse.eval nodeValue1903 (mixedVector B) := by
    change mixedMoment B node1903 node1903Labels = _
    exact sound1903 B hB hF
  have h1904 : mixedVector B (Sum.inr 1904) = Sparse.eval nodeValue1904 (mixedVector B) := by
    change mixedMoment B node1904 node1904Labels = _
    exact sound1904 B hB hF
  have h1913 : mixedVector B (Sum.inr 1913) = Sparse.eval nodeValue1913 (mixedVector B) := by
    change mixedMoment B node1913 node1913Labels = _
    exact sound1913 B hB hF
  have h1925 : mixedVector B (Sum.inr 1925) = Sparse.eval nodeValue1925 (mixedVector B) := by
    change mixedMoment B node1925 node1925Labels = _
    exact sound1925 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1908, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1903, h1904, h1913, h1925, h2196, h3464, h4080, reducedSource1616] using sourceEq1908 B hB

theorem rowSound1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1616 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1616, numericCheck1616, reducedZero1616 B hB hF, mul_zero]

theorem reducedZero1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1617 (mixedVector B) = 0 := by
  have h954 : mixedVector B (Sum.inr 954) = Sparse.eval nodeValue954 (mixedVector B) := by
    change mixedMoment B node954 node954Labels = _
    exact sound954 B hB hF
  have h1832 : mixedVector B (Sum.inr 1832) = Sparse.eval nodeValue1832 (mixedVector B) := by
    change mixedMoment B node1832 node1832Labels = _
    exact sound1832 B hB hF
  have h1980 : mixedVector B (Sum.inr 1980) = Sparse.eval nodeValue1980 (mixedVector B) := by
    change mixedMoment B node1980 node1980Labels = _
    exact sound1980 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1909, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h954, h1832, h1980, h2113, h2115, h4084, reducedSource1617] using sourceEq1909 B hB

theorem rowSound1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1617 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1617, numericCheck1617, reducedZero1617 B hB hF, mul_zero]

theorem reducedZero1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1618 (mixedVector B) = 0 := by
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h1825 : mixedVector B (Sum.inr 1825) = Sparse.eval nodeValue1825 (mixedVector B) := by
    change mixedMoment B node1825 node1825Labels = _
    exact sound1825 B hB hF
  have h1973 : mixedVector B (Sum.inr 1973) = Sparse.eval nodeValue1973 (mixedVector B) := by
    change mixedMoment B node1973 node1973Labels = _
    exact sound1973 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1910, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h945, h1825, h1973, h2090, h2107, h2112, h4083, reducedSource1618] using sourceEq1910 B hB

theorem rowSound1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1618 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1618, numericCheck1618, reducedZero1618 B hB hF, mul_zero]

theorem reducedZero1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1619 (mixedVector B) = 0 := by
  have h1121 : mixedVector B (Sum.inr 1121) = Sparse.eval nodeValue1121 (mixedVector B) := by
    change mixedMoment B node1121 node1121Labels = _
    exact sound1121 B hB hF
  have h2327 : mixedVector B (Sum.inr 2327) = Sparse.eval nodeValue2327 (mixedVector B) := by
    change mixedMoment B node2327 node2327Labels = _
    exact sound2327 B hB hF
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h2443 : mixedVector B (Sum.inr 2443) = Sparse.eval nodeValue2443 (mixedVector B) := by
    change mixedMoment B node2443 node2443Labels = _
    exact sound2443 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1911, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1121, h2327, h2423, h2443, h2486, h2488, h4092, reducedSource1619] using sourceEq1911 B hB

theorem rowSound1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1619 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1619, numericCheck1619, reducedZero1619 B hB hF, mul_zero]

theorem reducedZero1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1620 (mixedVector B) = 0 := by
  have h1946 : mixedVector B (Sum.inr 1946) = Sparse.eval nodeValue1946 (mixedVector B) := by
    change mixedMoment B node1946 node1946Labels = _
    exact sound1946 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h3355 : mixedVector B (Sum.inr 3355) = Sparse.eval nodeValue3355 (mixedVector B) := by
    change mixedMoment B node3355 node3355Labels = _
    exact sound3355 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1912, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1946, h2259, h3355, h3434, h3481, h3486, h4081, reducedSource1620] using sourceEq1912 B hB

theorem rowSound1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1620 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1620, numericCheck1620, reducedZero1620 B hB hF, mul_zero]

theorem reducedZero1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1621 (mixedVector B) = 0 := by
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1913, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2259, h2261, h2267, h2287, h3486, h4081, reducedSource1621] using sourceEq1913 B hB

theorem rowSound1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1621 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1621, numericCheck1621, reducedZero1621 B hB hF, mul_zero]

theorem reducedZero1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1622 (mixedVector B) = 0 := by
  have h1923 : mixedVector B (Sum.inr 1923) = Sparse.eval nodeValue1923 (mixedVector B) := by
    change mixedMoment B node1923 node1923Labels = _
    exact sound1923 B hB hF
  have h1927 : mixedVector B (Sum.inr 1927) = Sparse.eval nodeValue1927 (mixedVector B) := by
    change mixedMoment B node1927 node1927Labels = _
    exact sound1927 B hB hF
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h1949 : mixedVector B (Sum.inr 1949) = Sparse.eval nodeValue1949 (mixedVector B) := by
    change mixedMoment B node1949 node1949Labels = _
    exact sound1949 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1914, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1923, h1927, h1928, h1949, h2217, h3480, h4082, reducedSource1622] using sourceEq1914 B hB

theorem rowSound1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1622 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1622, numericCheck1622, reducedZero1622 B hB hF, mul_zero]

theorem reducedZero1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1623 (mixedVector B) = 0 := by
  have h1146 : mixedVector B (Sum.inr 1146) = Sparse.eval nodeValue1146 (mixedVector B) := by
    change mixedMoment B node1146 node1146Labels = _
    exact sound1146 B hB hF
  have h2346 : mixedVector B (Sum.inr 2346) = Sparse.eval nodeValue2346 (mixedVector B) := by
    change mixedMoment B node2346 node2346Labels = _
    exact sound2346 B hB hF
  have h2435 : mixedVector B (Sum.inr 2435) = Sparse.eval nodeValue2435 (mixedVector B) := by
    change mixedMoment B node2435 node2435Labels = _
    exact sound2435 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1915, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1146, h2346, h2435, h2520, h2522, h4084, reducedSource1623] using sourceEq1915 B hB

theorem rowSound1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1623 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1623, numericCheck1623, reducedZero1623 B hB hF, mul_zero]

theorem reducedZero1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1624 (mixedVector B) = 0 := by
  have h1951 : mixedVector B (Sum.inr 1951) = Sparse.eval nodeValue1951 (mixedVector B) := by
    change mixedMoment B node1951 node1951Labels = _
    exact sound1951 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2837 : mixedVector B (Sum.inr 2837) = Sparse.eval nodeValue2837 (mixedVector B) := by
    change mixedMoment B node2837 node2837Labels = _
    exact sound2837 B hB hF
  have h2842 : mixedVector B (Sum.inr 2842) = Sparse.eval nodeValue2842 (mixedVector B) := by
    change mixedMoment B node2842 node2842Labels = _
    exact sound2842 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1916, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1951, h2267, h2837, h2842, h3486, h4081, reducedSource1624] using sourceEq1916 B hB

theorem rowSound1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1624 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1624, numericCheck1624, reducedZero1624 B hB hF, mul_zero]

theorem reducedZero1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1625 (mixedVector B) = 0 := by
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h2335 : mixedVector B (Sum.inr 2335) = Sparse.eval nodeValue2335 (mixedVector B) := by
    change mixedMoment B node2335 node2335Labels = _
    exact sound2335 B hB hF
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1917, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1132, h2335, h2426, h2495, h2512, h2519, h4092, reducedSource1625] using sourceEq1917 B hB

theorem rowSound1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1625 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1625, numericCheck1625, reducedZero1625 B hB hF, mul_zero]

theorem reducedZero1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1626 (mixedVector B) = 0 := by
  have h1917 : mixedVector B (Sum.inr 1917) = Sparse.eval nodeValue1917 (mixedVector B) := by
    change mixedMoment B node1917 node1917Labels = _
    exact sound1917 B hB hF
  have h3343 : mixedVector B (Sum.inr 3343) = Sparse.eval nodeValue3343 (mixedVector B) := by
    change mixedMoment B node3343 node3343Labels = _
    exact sound3343 B hB hF
  have h3368 : mixedVector B (Sum.inr 3368) = Sparse.eval nodeValue3368 (mixedVector B) := by
    change mixedMoment B node3368 node3368Labels = _
    exact sound3368 B hB hF
  have h3385 : mixedVector B (Sum.inr 3385) = Sparse.eval nodeValue3385 (mixedVector B) := by
    change mixedMoment B node3385 node3385Labels = _
    exact sound3385 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1918, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1917, h3343, h3368, h3385, h3468, h3472, h4081, reducedSource1626] using sourceEq1918 B hB

theorem rowSound1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1626 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1626, numericCheck1626, reducedZero1626 B hB hF, mul_zero]

theorem reducedZero1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1627 (mixedVector B) = 0 := by
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1919, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3466, h3468, h3472, h3481, h4081, reducedSource1627] using sourceEq1919 B hB

theorem rowSound1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1627 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1627, numericCheck1627, reducedZero1627 B hB hF, mul_zero]

theorem reducedZero1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1628 (mixedVector B) = 0 := by
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h2320 : mixedVector B (Sum.inr 2320) = Sparse.eval nodeValue2320 (mixedVector B) := by
    change mixedMoment B node2320 node2320Labels = _
    exact sound2320 B hB hF
  have h2437 : mixedVector B (Sum.inr 2437) = Sparse.eval nodeValue2437 (mixedVector B) := by
    change mixedMoment B node2437 node2437Labels = _
    exact sound2437 B hB hF
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1920, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1112, h2320, h2437, h2470, h2480, h2485, h4091, reducedSource1628] using sourceEq1920 B hB

theorem rowSound1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1628 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1628, numericCheck1628, reducedZero1628 B hB hF, mul_zero]

theorem reducedZero1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1629 (mixedVector B) = 0 := by
  have h1907 : mixedVector B (Sum.inr 1907) = Sparse.eval nodeValue1907 (mixedVector B) := by
    change mixedMoment B node1907 node1907Labels = _
    exact sound1907 B hB hF
  have h3339 : mixedVector B (Sum.inr 3339) = Sparse.eval nodeValue3339 (mixedVector B) := by
    change mixedMoment B node3339 node3339Labels = _
    exact sound3339 B hB hF
  have h3443 : mixedVector B (Sum.inr 3443) = Sparse.eval nodeValue3443 (mixedVector B) := by
    change mixedMoment B node3443 node3443Labels = _
    exact sound3443 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1921, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1907, h3339, h3443, h3466, h3468, h4081, reducedSource1629] using sourceEq1921 B hB

theorem rowSound1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1629 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1629, numericCheck1629, reducedZero1629 B hB hF, mul_zero]

theorem reducedZero1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1630 (mixedVector B) = 0 := by
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2434 : mixedVector B (Sum.inr 2434) = Sparse.eval nodeValue2434 (mixedVector B) := by
    change mixedMoment B node2434 node2434Labels = _
    exact sound2434 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1923, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1317, h2426, h2434, h2519, h2558, h2881, h4092, reducedSource1630] using sourceEq1923 B hB

theorem rowSound1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1630 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1630, numericCheck1630, reducedZero1630 B hB hF, mul_zero]

theorem reducedZero1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1631 (mixedVector B) = 0 := by
  have h1155 : mixedVector B (Sum.inr 1155) = Sparse.eval nodeValue1155 (mixedVector B) := by
    change mixedMoment B node1155 node1155Labels = _
    exact sound1155 B hB hF
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2434 : mixedVector B (Sum.inr 2434) = Sparse.eval nodeValue2434 (mixedVector B) := by
    change mixedMoment B node2434 node2434Labels = _
    exact sound2434 B hB hF
  have h2524 : mixedVector B (Sum.inr 2524) = Sparse.eval nodeValue2524 (mixedVector B) := by
    change mixedMoment B node2524 node2524Labels = _
    exact sound2524 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1924, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1155, h2352, h2434, h2524, h2558, h2561, h4092, reducedSource1631] using sourceEq1924 B hB

theorem rowSound1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1631 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1631, numericCheck1631, reducedZero1631 B hB hF, mul_zero]

theorem sourceRowsAt1616 : MixedData.sourceRows (1616 : Fin 2425) =
    MixedData.row1616 := by decide +kernel

theorem sourceRowsAt1617 : MixedData.sourceRows (1617 : Fin 2425) =
    MixedData.row1617 := by decide +kernel

theorem sourceRowsAt1618 : MixedData.sourceRows (1618 : Fin 2425) =
    MixedData.row1618 := by decide +kernel

theorem sourceRowsAt1619 : MixedData.sourceRows (1619 : Fin 2425) =
    MixedData.row1619 := by decide +kernel

theorem sourceRowsAt1620 : MixedData.sourceRows (1620 : Fin 2425) =
    MixedData.row1620 := by decide +kernel

theorem sourceRowsAt1621 : MixedData.sourceRows (1621 : Fin 2425) =
    MixedData.row1621 := by decide +kernel

theorem sourceRowsAt1622 : MixedData.sourceRows (1622 : Fin 2425) =
    MixedData.row1622 := by decide +kernel

theorem sourceRowsAt1623 : MixedData.sourceRows (1623 : Fin 2425) =
    MixedData.row1623 := by decide +kernel

theorem sourceRowsAt1624 : MixedData.sourceRows (1624 : Fin 2425) =
    MixedData.row1624 := by decide +kernel

theorem sourceRowsAt1625 : MixedData.sourceRows (1625 : Fin 2425) =
    MixedData.row1625 := by decide +kernel

theorem sourceRowsAt1626 : MixedData.sourceRows (1626 : Fin 2425) =
    MixedData.row1626 := by decide +kernel

theorem sourceRowsAt1627 : MixedData.sourceRows (1627 : Fin 2425) =
    MixedData.row1627 := by decide +kernel

theorem sourceRowsAt1628 : MixedData.sourceRows (1628 : Fin 2425) =
    MixedData.row1628 := by decide +kernel

theorem sourceRowsAt1629 : MixedData.sourceRows (1629 : Fin 2425) =
    MixedData.row1629 := by decide +kernel

theorem sourceRowsAt1630 : MixedData.sourceRows (1630 : Fin 2425) =
    MixedData.row1630 := by decide +kernel

theorem sourceRowsAt1631 : MixedData.sourceRows (1631 : Fin 2425) =
    MixedData.row1631 := by decide +kernel

theorem chunkSound101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 101) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1616 ∨ k.val = 1617 ∨ k.val = 1618 ∨ k.val = 1619 ∨ k.val = 1620 ∨ k.val = 1621 ∨ k.val = 1622 ∨ k.val = 1623 ∨ k.val = 1624 ∨ k.val = 1625 ∨ k.val = 1626 ∨ k.val = 1627 ∨ k.val = 1628 ∨ k.val = 1629 ∨ k.val = 1630 ∨ k.val = 1631 := by omega
  rcases heq with h1616 | h1617 | h1618 | h1619 | h1620 | h1621 | h1622 | h1623 | h1624 | h1625 | h1626 | h1627 | h1628 | h1629 | h1630 | h1631
  · have he : k = (1616 : Fin 2425) := Fin.ext h1616
    subst k
    rw [sourceRowsAt1616]
    exact rowSound1616 B hB hF
  · have he : k = (1617 : Fin 2425) := Fin.ext h1617
    subst k
    rw [sourceRowsAt1617]
    exact rowSound1617 B hB hF
  · have he : k = (1618 : Fin 2425) := Fin.ext h1618
    subst k
    rw [sourceRowsAt1618]
    exact rowSound1618 B hB hF
  · have he : k = (1619 : Fin 2425) := Fin.ext h1619
    subst k
    rw [sourceRowsAt1619]
    exact rowSound1619 B hB hF
  · have he : k = (1620 : Fin 2425) := Fin.ext h1620
    subst k
    rw [sourceRowsAt1620]
    exact rowSound1620 B hB hF
  · have he : k = (1621 : Fin 2425) := Fin.ext h1621
    subst k
    rw [sourceRowsAt1621]
    exact rowSound1621 B hB hF
  · have he : k = (1622 : Fin 2425) := Fin.ext h1622
    subst k
    rw [sourceRowsAt1622]
    exact rowSound1622 B hB hF
  · have he : k = (1623 : Fin 2425) := Fin.ext h1623
    subst k
    rw [sourceRowsAt1623]
    exact rowSound1623 B hB hF
  · have he : k = (1624 : Fin 2425) := Fin.ext h1624
    subst k
    rw [sourceRowsAt1624]
    exact rowSound1624 B hB hF
  · have he : k = (1625 : Fin 2425) := Fin.ext h1625
    subst k
    rw [sourceRowsAt1625]
    exact rowSound1625 B hB hF
  · have he : k = (1626 : Fin 2425) := Fin.ext h1626
    subst k
    rw [sourceRowsAt1626]
    exact rowSound1626 B hB hF
  · have he : k = (1627 : Fin 2425) := Fin.ext h1627
    subst k
    rw [sourceRowsAt1627]
    exact rowSound1627 B hB hF
  · have he : k = (1628 : Fin 2425) := Fin.ext h1628
    subst k
    rw [sourceRowsAt1628]
    exact rowSound1628 B hB hF
  · have he : k = (1629 : Fin 2425) := Fin.ext h1629
    subst k
    rw [sourceRowsAt1629]
    exact rowSound1629 B hB hF
  · have he : k = (1630 : Fin 2425) := Fin.ext h1630
    subst k
    rw [sourceRowsAt1630]
    exact rowSound1630 B hB hF
  · have he : k = (1631 : Fin 2425) := Fin.ext h1631
    subst k
    rw [sourceRowsAt1631]
    exact rowSound1631 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
