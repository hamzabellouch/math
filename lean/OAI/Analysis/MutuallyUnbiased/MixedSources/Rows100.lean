import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic100
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources59

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1600 (mixedVector B) = 0 := by
  have h4056 : mixedVector B (Sum.inr 4056) = Sparse.eval nodeValue4056 (mixedVector B) := by
    change mixedMoment B node4056 node4056Labels = _
    exact sound4056 B hB hF
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1890, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4056, h4057, h4063, h4068, h4069, h4079, h4083, reducedSource1600] using sourceEq1890 B hB

theorem rowSound1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1600 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1600, numericCheck1600, reducedZero1600 B hB hF, mul_zero]

theorem reducedZero1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1601 (mixedVector B) = 0 := by
  have h940 : mixedVector B (Sum.inr 940) = Sparse.eval nodeValue940 (mixedVector B) := by
    change mixedMoment B node940 node940Labels = _
    exact sound940 B hB hF
  have h1820 : mixedVector B (Sum.inr 1820) = Sparse.eval nodeValue1820 (mixedVector B) := by
    change mixedMoment B node1820 node1820Labels = _
    exact sound1820 B hB hF
  have h1971 : mixedVector B (Sum.inr 1971) = Sparse.eval nodeValue1971 (mixedVector B) := by
    change mixedMoment B node1971 node1971Labels = _
    exact sound1971 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1891, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h940, h1820, h1971, h2063, h2065, h4085, reducedSource1601] using sourceEq1891 B hB

theorem rowSound1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1601 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1601, numericCheck1601, reducedZero1601 B hB hF, mul_zero]

theorem reducedZero1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1602 (mixedVector B) = 0 := by
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2222 : mixedVector B (Sum.inr 2222) = Sparse.eval nodeValue2222 (mixedVector B) := by
    change mixedMoment B node2222 node2222Labels = _
    exact sound2222 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2282 : mixedVector B (Sum.inr 2282) = Sparse.eval nodeValue2282 (mixedVector B) := by
    change mixedMoment B node2282 node2282Labels = _
    exact sound2282 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1892, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2220, h2222, h2230, h2282, h2287, h4081, reducedSource1602] using sourceEq1892 B hB

theorem rowSound1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1602 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1602, numericCheck1602, reducedZero1602 B hB hF, mul_zero]

theorem reducedZero1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1603 (mixedVector B) = 0 := by
  have h931 : mixedVector B (Sum.inr 931) = Sparse.eval nodeValue931 (mixedVector B) := by
    change mixedMoment B node931 node931Labels = _
    exact sound931 B hB hF
  have h1813 : mixedVector B (Sum.inr 1813) = Sparse.eval nodeValue1813 (mixedVector B) := by
    change mixedMoment B node1813 node1813Labels = _
    exact sound1813 B hB hF
  have h1965 : mixedVector B (Sum.inr 1965) = Sparse.eval nodeValue1965 (mixedVector B) := by
    change mixedMoment B node1965 node1965Labels = _
    exact sound1965 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1893, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h931, h1813, h1965, h2026, h2037, h2058, h4084, reducedSource1603] using sourceEq1893 B hB

theorem rowSound1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1603 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1603, numericCheck1603, reducedZero1603 B hB hF, mul_zero]

theorem reducedZero1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1604 (mixedVector B) = 0 := by
  have h914 : mixedVector B (Sum.inr 914) = Sparse.eval nodeValue914 (mixedVector B) := by
    change mixedMoment B node914 node914Labels = _
    exact sound914 B hB hF
  have h1797 : mixedVector B (Sum.inr 1797) = Sparse.eval nodeValue1797 (mixedVector B) := by
    change mixedMoment B node1797 node1797Labels = _
    exact sound1797 B hB hF
  have h1957 : mixedVector B (Sum.inr 1957) = Sparse.eval nodeValue1957 (mixedVector B) := by
    change mixedMoment B node1957 node1957Labels = _
    exact sound1957 B hB hF
  have h1980 : mixedVector B (Sum.inr 1980) = Sparse.eval nodeValue1980 (mixedVector B) := by
    change mixedMoment B node1980 node1980Labels = _
    exact sound1980 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1894, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h914, h1797, h1957, h1980, h2026, h2028, h4084, reducedSource1604] using sourceEq1894 B hB

theorem rowSound1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1604 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1604, numericCheck1604, reducedZero1604 B hB hF, mul_zero]

theorem reducedZero1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1605 (mixedVector B) = 0 := by
  have h949 : mixedVector B (Sum.inr 949) = Sparse.eval nodeValue949 (mixedVector B) := by
    change mixedMoment B node949 node949Labels = _
    exact sound949 B hB hF
  have h1828 : mixedVector B (Sum.inr 1828) = Sparse.eval nodeValue1828 (mixedVector B) := by
    change mixedMoment B node1828 node1828Labels = _
    exact sound1828 B hB hF
  have h1976 : mixedVector B (Sum.inr 1976) = Sparse.eval nodeValue1976 (mixedVector B) := by
    change mixedMoment B node1976 node1976Labels = _
    exact sound1976 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1895, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h949, h1828, h1976, h2092, h2110, h4083, reducedSource1605] using sourceEq1895 B hB

theorem rowSound1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1605 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1605, numericCheck1605, reducedZero1605 B hB hF, mul_zero]

theorem reducedZero1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1606 (mixedVector B) = 0 := by
  have h2219 : mixedVector B (Sum.inr 2219) = Sparse.eval nodeValue2219 (mixedVector B) := by
    change mixedMoment B node2219 node2219Labels = _
    exact sound2219 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2221 : mixedVector B (Sum.inr 2221) = Sparse.eval nodeValue2221 (mixedVector B) := by
    change mixedMoment B node2221 node2221Labels = _
    exact sound2221 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1897, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2219, h2220, h2221, h2224, h4081, reducedSource1606] using sourceEq1897 B hB

theorem rowSound1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1606 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1606, numericCheck1606, reducedZero1606 B hB hF, mul_zero]

theorem reducedZero1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1607 (mixedVector B) = 0 := by
  have h925 : mixedVector B (Sum.inr 925) = Sparse.eval nodeValue925 (mixedVector B) := by
    change mixedMoment B node925 node925Labels = _
    exact sound925 B hB hF
  have h1808 : mixedVector B (Sum.inr 1808) = Sparse.eval nodeValue1808 (mixedVector B) := by
    change mixedMoment B node1808 node1808Labels = _
    exact sound1808 B hB hF
  have h1961 : mixedVector B (Sum.inr 1961) = Sparse.eval nodeValue1961 (mixedVector B) := by
    change mixedMoment B node1961 node1961Labels = _
    exact sound1961 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1898, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h925, h1808, h1961, h2035, h2054, h2062, h4084, reducedSource1607] using sourceEq1898 B hB

theorem rowSound1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1607 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1607, numericCheck1607, reducedZero1607 B hB hF, mul_zero]

theorem reducedZero1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1608 (mixedVector B) = 0 := by
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h2340 : mixedVector B (Sum.inr 2340) = Sparse.eval nodeValue2340 (mixedVector B) := by
    change mixedMoment B node2340 node2340Labels = _
    exact sound2340 B hB hF
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1899, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1137, h2340, h2430, h2486, h2497, h2515, h4092, reducedSource1608] using sourceEq1899 B hB

theorem rowSound1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1608 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1608, numericCheck1608, reducedZero1608 B hB hF, mul_zero]

theorem reducedZero1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1609 (mixedVector B) = 0 := by
  have h1948 : mixedVector B (Sum.inr 1948) = Sparse.eval nodeValue1948 (mixedVector B) := by
    change mixedMoment B node1948 node1948Labels = _
    exact sound1948 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h3358 : mixedVector B (Sum.inr 3358) = Sparse.eval nodeValue3358 (mixedVector B) := by
    change mixedMoment B node3358 node3358Labels = _
    exact sound3358 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1900, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1948, h2207, h3358, h3437, h3472, h3481, h4081, reducedSource1609] using sourceEq1900 B hB

theorem rowSound1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1609 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1609, numericCheck1609, reducedZero1609 B hB hF, mul_zero]

theorem reducedZero1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1610 (mixedVector B) = 0 := by
  have h1910 : mixedVector B (Sum.inr 1910) = Sparse.eval nodeValue1910 (mixedVector B) := by
    change mixedMoment B node1910 node1910Labels = _
    exact sound1910 B hB hF
  have h1916 : mixedVector B (Sum.inr 1916) = Sparse.eval nodeValue1916 (mixedVector B) := by
    change mixedMoment B node1916 node1916Labels = _
    exact sound1916 B hB hF
  have h1917 : mixedVector B (Sum.inr 1917) = Sparse.eval nodeValue1917 (mixedVector B) := by
    change mixedMoment B node1917 node1917Labels = _
    exact sound1917 B hB hF
  have h1948 : mixedVector B (Sum.inr 1948) = Sparse.eval nodeValue1948 (mixedVector B) := by
    change mixedMoment B node1948 node1948Labels = _
    exact sound1948 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1901, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1910, h1916, h1917, h1948, h2207, h3472, h4081, reducedSource1610] using sourceEq1901 B hB

theorem rowSound1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1610 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1610, numericCheck1610, reducedZero1610 B hB hF, mul_zero]

theorem reducedZero1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1611 (mixedVector B) = 0 := by
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1902, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2201, h2203, h2207, h2224, h2259, h3481, h4081, reducedSource1611] using sourceEq1902 B hB

theorem rowSound1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1611 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1611, numericCheck1611, reducedZero1611 B hB hF, mul_zero]

theorem reducedZero1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1612 (mixedVector B) = 0 := by
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h1790 : mixedVector B (Sum.inr 1790) = Sparse.eval nodeValue1790 (mixedVector B) := by
    change mixedMoment B node1790 node1790Labels = _
    exact sound1790 B hB hF
  have h1973 : mixedVector B (Sum.inr 1973) = Sparse.eval nodeValue1973 (mixedVector B) := by
    change mixedMoment B node1973 node1973Labels = _
    exact sound1973 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1903, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h905, h1790, h1973, h2009, h2020, h2025, h4083, reducedSource1612] using sourceEq1903 B hB

theorem rowSound1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1612 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1612, numericCheck1612, reducedZero1612 B hB hF, mul_zero]

theorem reducedZero1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1613 (mixedVector B) = 0 := by
  have h1116 : mixedVector B (Sum.inr 1116) = Sparse.eval nodeValue1116 (mixedVector B) := by
    change mixedMoment B node1116 node1116Labels = _
    exact sound1116 B hB hF
  have h2323 : mixedVector B (Sum.inr 2323) = Sparse.eval nodeValue2323 (mixedVector B) := by
    change mixedMoment B node2323 node2323Labels = _
    exact sound2323 B hB hF
  have h2440 : mixedVector B (Sum.inr 2440) = Sparse.eval nodeValue2440 (mixedVector B) := by
    change mixedMoment B node2440 node2440Labels = _
    exact sound2440 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1904, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1116, h2323, h2440, h2471, h2483, h4091, reducedSource1613] using sourceEq1904 B hB

theorem rowSound1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1613 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1613, numericCheck1613, reducedZero1613 B hB hF, mul_zero]

theorem reducedZero1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1614 (mixedVector B) = 0 := by
  have h1940 : mixedVector B (Sum.inr 1940) = Sparse.eval nodeValue1940 (mixedVector B) := by
    change mixedMoment B node1940 node1940Labels = _
    exact sound1940 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h3350 : mixedVector B (Sum.inr 3350) = Sparse.eval nodeValue3350 (mixedVector B) := by
    change mixedMoment B node3350 node3350Labels = _
    exact sound3350 B hB hF
  have h3466 : mixedVector B (Sum.inr 3466) = Sparse.eval nodeValue3466 (mixedVector B) := by
    change mixedMoment B node3466 node3466Labels = _
    exact sound3466 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1905, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1940, h2201, h3350, h3466, h3481, h4081, reducedSource1614] using sourceEq1905 B hB

theorem rowSound1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1614 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1614, numericCheck1614, reducedZero1614 B hB hF, mul_zero]

theorem reducedZero1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1615 (mixedVector B) = 0 := by
  have h909 : mixedVector B (Sum.inr 909) = Sparse.eval nodeValue909 (mixedVector B) := by
    change mixedMoment B node909 node909Labels = _
    exact sound909 B hB hF
  have h1793 : mixedVector B (Sum.inr 1793) = Sparse.eval nodeValue1793 (mixedVector B) := by
    change mixedMoment B node1793 node1793Labels = _
    exact sound1793 B hB hF
  have h1976 : mixedVector B (Sum.inr 1976) = Sparse.eval nodeValue1976 (mixedVector B) := by
    change mixedMoment B node1976 node1976Labels = _
    exact sound1976 B hB hF
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1907, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h909, h1793, h1976, h2010, h2023, h4083, reducedSource1615] using sourceEq1907 B hB

theorem rowSound1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1615 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1615, numericCheck1615, reducedZero1615 B hB hF, mul_zero]

theorem sourceRowsAt1600 : MixedData.sourceRows (1600 : Fin 2425) =
    MixedData.row1600 := by decide +kernel

theorem sourceRowsAt1601 : MixedData.sourceRows (1601 : Fin 2425) =
    MixedData.row1601 := by decide +kernel

theorem sourceRowsAt1602 : MixedData.sourceRows (1602 : Fin 2425) =
    MixedData.row1602 := by decide +kernel

theorem sourceRowsAt1603 : MixedData.sourceRows (1603 : Fin 2425) =
    MixedData.row1603 := by decide +kernel

theorem sourceRowsAt1604 : MixedData.sourceRows (1604 : Fin 2425) =
    MixedData.row1604 := by decide +kernel

theorem sourceRowsAt1605 : MixedData.sourceRows (1605 : Fin 2425) =
    MixedData.row1605 := by decide +kernel

theorem sourceRowsAt1606 : MixedData.sourceRows (1606 : Fin 2425) =
    MixedData.row1606 := by decide +kernel

theorem sourceRowsAt1607 : MixedData.sourceRows (1607 : Fin 2425) =
    MixedData.row1607 := by decide +kernel

theorem sourceRowsAt1608 : MixedData.sourceRows (1608 : Fin 2425) =
    MixedData.row1608 := by decide +kernel

theorem sourceRowsAt1609 : MixedData.sourceRows (1609 : Fin 2425) =
    MixedData.row1609 := by decide +kernel

theorem sourceRowsAt1610 : MixedData.sourceRows (1610 : Fin 2425) =
    MixedData.row1610 := by decide +kernel

theorem sourceRowsAt1611 : MixedData.sourceRows (1611 : Fin 2425) =
    MixedData.row1611 := by decide +kernel

theorem sourceRowsAt1612 : MixedData.sourceRows (1612 : Fin 2425) =
    MixedData.row1612 := by decide +kernel

theorem sourceRowsAt1613 : MixedData.sourceRows (1613 : Fin 2425) =
    MixedData.row1613 := by decide +kernel

theorem sourceRowsAt1614 : MixedData.sourceRows (1614 : Fin 2425) =
    MixedData.row1614 := by decide +kernel

theorem sourceRowsAt1615 : MixedData.sourceRows (1615 : Fin 2425) =
    MixedData.row1615 := by decide +kernel

theorem chunkSound100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 100) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1600 ∨ k.val = 1601 ∨ k.val = 1602 ∨ k.val = 1603 ∨ k.val = 1604 ∨ k.val = 1605 ∨ k.val = 1606 ∨ k.val = 1607 ∨ k.val = 1608 ∨ k.val = 1609 ∨ k.val = 1610 ∨ k.val = 1611 ∨ k.val = 1612 ∨ k.val = 1613 ∨ k.val = 1614 ∨ k.val = 1615 := by omega
  rcases heq with h1600 | h1601 | h1602 | h1603 | h1604 | h1605 | h1606 | h1607 | h1608 | h1609 | h1610 | h1611 | h1612 | h1613 | h1614 | h1615
  · have he : k = (1600 : Fin 2425) := Fin.ext h1600
    subst k
    rw [sourceRowsAt1600]
    exact rowSound1600 B hB hF
  · have he : k = (1601 : Fin 2425) := Fin.ext h1601
    subst k
    rw [sourceRowsAt1601]
    exact rowSound1601 B hB hF
  · have he : k = (1602 : Fin 2425) := Fin.ext h1602
    subst k
    rw [sourceRowsAt1602]
    exact rowSound1602 B hB hF
  · have he : k = (1603 : Fin 2425) := Fin.ext h1603
    subst k
    rw [sourceRowsAt1603]
    exact rowSound1603 B hB hF
  · have he : k = (1604 : Fin 2425) := Fin.ext h1604
    subst k
    rw [sourceRowsAt1604]
    exact rowSound1604 B hB hF
  · have he : k = (1605 : Fin 2425) := Fin.ext h1605
    subst k
    rw [sourceRowsAt1605]
    exact rowSound1605 B hB hF
  · have he : k = (1606 : Fin 2425) := Fin.ext h1606
    subst k
    rw [sourceRowsAt1606]
    exact rowSound1606 B hB hF
  · have he : k = (1607 : Fin 2425) := Fin.ext h1607
    subst k
    rw [sourceRowsAt1607]
    exact rowSound1607 B hB hF
  · have he : k = (1608 : Fin 2425) := Fin.ext h1608
    subst k
    rw [sourceRowsAt1608]
    exact rowSound1608 B hB hF
  · have he : k = (1609 : Fin 2425) := Fin.ext h1609
    subst k
    rw [sourceRowsAt1609]
    exact rowSound1609 B hB hF
  · have he : k = (1610 : Fin 2425) := Fin.ext h1610
    subst k
    rw [sourceRowsAt1610]
    exact rowSound1610 B hB hF
  · have he : k = (1611 : Fin 2425) := Fin.ext h1611
    subst k
    rw [sourceRowsAt1611]
    exact rowSound1611 B hB hF
  · have he : k = (1612 : Fin 2425) := Fin.ext h1612
    subst k
    rw [sourceRowsAt1612]
    exact rowSound1612 B hB hF
  · have he : k = (1613 : Fin 2425) := Fin.ext h1613
    subst k
    rw [sourceRowsAt1613]
    exact rowSound1613 B hB hF
  · have he : k = (1614 : Fin 2425) := Fin.ext h1614
    subst k
    rw [sourceRowsAt1614]
    exact rowSound1614 B hB hF
  · have he : k = (1615 : Fin 2425) := Fin.ext h1615
    subst k
    rw [sourceRowsAt1615]
    exact rowSound1615 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
