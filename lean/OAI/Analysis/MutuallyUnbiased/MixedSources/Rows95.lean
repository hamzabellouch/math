import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources56

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1520 (mixedVector B) = 0 := by
  have h598 : mixedVector B (Sum.inr 598) = Sparse.eval nodeValue598 (mixedVector B) := by
    change mixedMoment B node598 node598Labels = _
    exact sound598 B hB hF
  have h918 : mixedVector B (Sum.inr 918) = Sparse.eval nodeValue918 (mixedVector B) := by
    change mixedMoment B node918 node918Labels = _
    exact sound918 B hB hF
  have h1078 : mixedVector B (Sum.inr 1078) = Sparse.eval nodeValue1078 (mixedVector B) := by
    change mixedMoment B node1078 node1078Labels = _
    exact sound1078 B hB hF
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1788, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h598, h918, h1078, h1080, h4085, reducedSource1520] using sourceEq1788 B hB

theorem rowSound1520 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1520 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1520, numericCheck1520, reducedZero1520 B hB hF, mul_zero]

theorem reducedZero1521 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1521 (mixedVector B) = 0 := by
  have h1252 : mixedVector B (Sum.inr 1252) = Sparse.eval nodeValue1252 (mixedVector B) := by
    change mixedMoment B node1252 node1252Labels = _
    exact sound1252 B hB hF
  have h1255 : mixedVector B (Sum.inr 1255) = Sparse.eval nodeValue1255 (mixedVector B) := by
    change mixedMoment B node1255 node1255Labels = _
    exact sound1255 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1272 : mixedVector B (Sum.inr 1272) = Sparse.eval nodeValue1272 (mixedVector B) := by
    change mixedMoment B node1272 node1272Labels = _
    exact sound1272 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h1398 : mixedVector B (Sum.inr 1398) = Sparse.eval nodeValue1398 (mixedVector B) := by
    change mixedMoment B node1398 node1398Labels = _
    exact sound1398 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h1415 : mixedVector B (Sum.inr 1415) = Sparse.eval nodeValue1415 (mixedVector B) := by
    change mixedMoment B node1415 node1415Labels = _
    exact sound1415 B hB hF
  have h1427 : mixedVector B (Sum.inr 1427) = Sparse.eval nodeValue1427 (mixedVector B) := by
    change mixedMoment B node1427 node1427Labels = _
    exact sound1427 B hB hF
  have h1448 : mixedVector B (Sum.inr 1448) = Sparse.eval nodeValue1448 (mixedVector B) := by
    change mixedMoment B node1448 node1448Labels = _
    exact sound1448 B hB hF
  have h1449 : mixedVector B (Sum.inr 1449) = Sparse.eval nodeValue1449 (mixedVector B) := by
    change mixedMoment B node1449 node1449Labels = _
    exact sound1449 B hB hF
  have h1478 : mixedVector B (Sum.inr 1478) = Sparse.eval nodeValue1478 (mixedVector B) := by
    change mixedMoment B node1478 node1478Labels = _
    exact sound1478 B hB hF
  have h1484 : mixedVector B (Sum.inr 1484) = Sparse.eval nodeValue1484 (mixedVector B) := by
    change mixedMoment B node1484 node1484Labels = _
    exact sound1484 B hB hF
  simpa only [sourceForm1792, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1252, h1255, h1270, h1272, h1305, h1306, h1398, h1414, h1415, h1427, h1448, h1449, h1478, h1484, reducedSource1521] using sourceEq1792 B hB

theorem rowSound1521 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1521 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1521, numericCheck1521, reducedZero1521 B hB hF, mul_zero]

theorem reducedZero1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1522 (mixedVector B) = 0 := by
  have h1006 : mixedVector B (Sum.inr 1006) = Sparse.eval nodeValue1006 (mixedVector B) := by
    change mixedMoment B node1006 node1006Labels = _
    exact sound1006 B hB hF
  have h1948 : mixedVector B (Sum.inr 1948) = Sparse.eval nodeValue1948 (mixedVector B) := by
    change mixedMoment B node1948 node1948Labels = _
    exact sound1948 B hB hF
  have h2001 : mixedVector B (Sum.inr 2001) = Sparse.eval nodeValue2001 (mixedVector B) := by
    change mixedMoment B node2001 node2001Labels = _
    exact sound2001 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2221 : mixedVector B (Sum.inr 2221) = Sparse.eval nodeValue2221 (mixedVector B) := by
    change mixedMoment B node2221 node2221Labels = _
    exact sound2221 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1793, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1006, h1948, h2001, h2207, h2221, h2224, h4081, reducedSource1522] using sourceEq1793 B hB

theorem rowSound1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1522 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1522, numericCheck1522, reducedZero1522 B hB hF, mul_zero]

theorem reducedZero1523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1523 (mixedVector B) = 0 := by
  have h1001 : mixedVector B (Sum.inr 1001) = Sparse.eval nodeValue1001 (mixedVector B) := by
    change mixedMoment B node1001 node1001Labels = _
    exact sound1001 B hB hF
  have h1946 : mixedVector B (Sum.inr 1946) = Sparse.eval nodeValue1946 (mixedVector B) := by
    change mixedMoment B node1946 node1946Labels = _
    exact sound1946 B hB hF
  have h1998 : mixedVector B (Sum.inr 1998) = Sparse.eval nodeValue1998 (mixedVector B) := by
    change mixedMoment B node1998 node1998Labels = _
    exact sound1998 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1795, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1001, h1946, h1998, h2220, h2224, h2230, h4081, reducedSource1523] using sourceEq1795 B hB

theorem rowSound1523 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1523 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1523, numericCheck1523, reducedZero1523 B hB hF, mul_zero]

theorem reducedZero1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1524 (mixedVector B) = 0 := by
  have h1008 : mixedVector B (Sum.inr 1008) = Sparse.eval nodeValue1008 (mixedVector B) := by
    change mixedMoment B node1008 node1008Labels = _
    exact sound1008 B hB hF
  have h1949 : mixedVector B (Sum.inr 1949) = Sparse.eval nodeValue1949 (mixedVector B) := by
    change mixedMoment B node1949 node1949Labels = _
    exact sound1949 B hB hF
  have h2002 : mixedVector B (Sum.inr 2002) = Sparse.eval nodeValue2002 (mixedVector B) := by
    change mixedMoment B node2002 node2002Labels = _
    exact sound2002 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1796, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1008, h1949, h2002, h2217, h2225, h4082, reducedSource1524] using sourceEq1796 B hB

theorem rowSound1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1524 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1524, numericCheck1524, reducedZero1524 B hB hF, mul_zero]

theorem reducedZero1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1525 (mixedVector B) = 0 := by
  have h996 : mixedVector B (Sum.inr 996) = Sparse.eval nodeValue996 (mixedVector B) := by
    change mixedMoment B node996 node996Labels = _
    exact sound996 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1008 : mixedVector B (Sum.inr 1008) = Sparse.eval nodeValue1008 (mixedVector B) := by
    change mixedMoment B node1008 node1008Labels = _
    exact sound1008 B hB hF
  have h1071 : mixedVector B (Sum.inr 1071) = Sparse.eval nodeValue1071 (mixedVector B) := by
    change mixedMoment B node1071 node1071Labels = _
    exact sound1071 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1797, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h996, h1000, h1008, h1071, h2225, h4082, reducedSource1525] using sourceEq1797 B hB

theorem rowSound1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1525 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1525, numericCheck1525, reducedZero1525 B hB hF, mul_zero]

theorem reducedZero1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1526 (mixedVector B) = 0 := by
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1947 : mixedVector B (Sum.inr 1947) = Sparse.eval nodeValue1947 (mixedVector B) := by
    change mixedMoment B node1947 node1947Labels = _
    exact sound1947 B hB hF
  have h2000 : mixedVector B (Sum.inr 2000) = Sparse.eval nodeValue2000 (mixedVector B) := by
    change mixedMoment B node2000 node2000Labels = _
    exact sound2000 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1798, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1005, h1947, h2000, h2206, h2216, h2227, h4080, reducedSource1526] using sourceEq1798 B hB

theorem rowSound1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1526 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1526, numericCheck1526, reducedZero1526 B hB hF, mul_zero]

theorem reducedZero1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1527 (mixedVector B) = 0 := by
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1004 : mixedVector B (Sum.inr 1004) = Sparse.eval nodeValue1004 (mixedVector B) := by
    change mixedMoment B node1004 node1004Labels = _
    exact sound1004 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1800, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h998, h1004, h1005, h1073, h2227, h4080, reducedSource1527] using sourceEq1800 B hB

theorem rowSound1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1527 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1527, numericCheck1527, reducedZero1527 B hB hF, mul_zero]

theorem reducedZero1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1528 (mixedVector B) = 0 := by
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1945 : mixedVector B (Sum.inr 1945) = Sparse.eval nodeValue1945 (mixedVector B) := by
    change mixedMoment B node1945 node1945Labels = _
    exact sound1945 B hB hF
  have h1997 : mixedVector B (Sum.inr 1997) = Sparse.eval nodeValue1997 (mixedVector B) := by
    change mixedMoment B node1997 node1997Labels = _
    exact sound1997 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1803, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1000, h1945, h1997, h2215, h2225, h2229, h4082, reducedSource1528] using sourceEq1803 B hB

theorem rowSound1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1528 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1528, numericCheck1528, reducedZero1528 B hB hF, mul_zero]

theorem reducedZero1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1529 (mixedVector B) = 0 := by
  have h876 : mixedVector B (Sum.inr 876) = Sparse.eval nodeValue876 (mixedVector B) := by
    change mixedMoment B node876 node876Labels = _
    exact sound876 B hB hF
  have h881 : mixedVector B (Sum.inr 881) = Sparse.eval nodeValue881 (mixedVector B) := by
    change mixedMoment B node881 node881Labels = _
    exact sound881 B hB hF
  have h883 : mixedVector B (Sum.inr 883) = Sparse.eval nodeValue883 (mixedVector B) := by
    change mixedMoment B node883 node883Labels = _
    exact sound883 B hB hF
  have h891 : mixedVector B (Sum.inr 891) = Sparse.eval nodeValue891 (mixedVector B) := by
    change mixedMoment B node891 node891Labels = _
    exact sound891 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1945 : mixedVector B (Sum.inr 1945) = Sparse.eval nodeValue1945 (mixedVector B) := by
    change mixedMoment B node1945 node1945Labels = _
    exact sound1945 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1804, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h876, h881, h883, h891, h1000, h1945, h4082, reducedSource1529] using sourceEq1804 B hB

theorem rowSound1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1529 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1529, numericCheck1529, reducedZero1529 B hB hF, mul_zero]

theorem reducedZero1530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1530 (mixedVector B) = 0 := by
  have h999 : mixedVector B (Sum.inr 999) = Sparse.eval nodeValue999 (mixedVector B) := by
    change mixedMoment B node999 node999Labels = _
    exact sound999 B hB hF
  have h1944 : mixedVector B (Sum.inr 1944) = Sparse.eval nodeValue1944 (mixedVector B) := by
    change mixedMoment B node1944 node1944Labels = _
    exact sound1944 B hB hF
  have h1996 : mixedVector B (Sum.inr 1996) = Sparse.eval nodeValue1996 (mixedVector B) := by
    change mixedMoment B node1996 node1996Labels = _
    exact sound1996 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1807, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h999, h1944, h1996, h2203, h2224, h2228, h4081, reducedSource1530] using sourceEq1807 B hB

theorem rowSound1530 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1530 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1530, numericCheck1530, reducedZero1530 B hB hF, mul_zero]

theorem reducedZero1531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1531 (mixedVector B) = 0 := by
  have h786 : mixedVector B (Sum.inr 786) = Sparse.eval nodeValue786 (mixedVector B) := by
    change mixedMoment B node786 node786Labels = _
    exact sound786 B hB hF
  have h1638 : mixedVector B (Sum.inr 1638) = Sparse.eval nodeValue1638 (mixedVector B) := by
    change mixedMoment B node1638 node1638Labels = _
    exact sound1638 B hB hF
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1809, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h786, h1638, h1699, h1706, h4068, reducedSource1531] using sourceEq1809 B hB

theorem rowSound1531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1531 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1531, numericCheck1531, reducedZero1531 B hB hF, mul_zero]

theorem reducedZero1532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1532 (mixedVector B) = 0 := by
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h786 : mixedVector B (Sum.inr 786) = Sparse.eval nodeValue786 (mixedVector B) := by
    change mixedMoment B node786 node786Labels = _
    exact sound786 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1811, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h783, h786, h805, h1706, h4068, reducedSource1532] using sourceEq1811 B hB

theorem rowSound1532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1532 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1532, numericCheck1532, reducedZero1532 B hB hF, mul_zero]

theorem reducedZero1533 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1533 (mixedVector B) = 0 := by
  have h550 : mixedVector B (Sum.inr 550) = Sparse.eval nodeValue550 (mixedVector B) := by
    change mixedMoment B node550 node550Labels = _
    exact sound550 B hB hF
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h822 : mixedVector B (Sum.inr 822) = Sparse.eval nodeValue822 (mixedVector B) := by
    change mixedMoment B node822 node822Labels = _
    exact sound822 B hB hF
  have h850 : mixedVector B (Sum.inr 850) = Sparse.eval nodeValue850 (mixedVector B) := by
    change mixedMoment B node850 node850Labels = _
    exact sound850 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1812, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h550, h803, h822, h850, h4069, reducedSource1533] using sourceEq1812 B hB

theorem rowSound1533 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1533 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1533, numericCheck1533, reducedZero1533 B hB hF, mul_zero]

theorem reducedZero1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1534 (mixedVector B) = 0 := by
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1813, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h783, h1636, h1698, h1706, h1708, h4068, reducedSource1534] using sourceEq1813 B hB

theorem rowSound1534 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1534 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1534, numericCheck1534, reducedZero1534 B hB hF, mul_zero]

theorem reducedZero1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1535 (mixedVector B) = 0 := by
  have h537 : mixedVector B (Sum.inr 537) = Sparse.eval nodeValue537 (mixedVector B) := by
    change mixedMoment B node537 node537Labels = _
    exact sound537 B hB hF
  have h732 : mixedVector B (Sum.inr 732) = Sparse.eval nodeValue732 (mixedVector B) := by
    change mixedMoment B node732 node732Labels = _
    exact sound732 B hB hF
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1814, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h537, h732, h783, h805, h810, h4068, reducedSource1535] using sourceEq1814 B hB

theorem rowSound1535 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1535 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1535, numericCheck1535, reducedZero1535 B hB hF, mul_zero]

theorem sourceRowsAt1520 : MixedData.sourceRows (1520 : Fin 2425) =
    MixedData.row1520 := by decide +kernel

theorem sourceRowsAt1521 : MixedData.sourceRows (1521 : Fin 2425) =
    MixedData.row1521 := by decide +kernel

theorem sourceRowsAt1522 : MixedData.sourceRows (1522 : Fin 2425) =
    MixedData.row1522 := by decide +kernel

theorem sourceRowsAt1523 : MixedData.sourceRows (1523 : Fin 2425) =
    MixedData.row1523 := by decide +kernel

theorem sourceRowsAt1524 : MixedData.sourceRows (1524 : Fin 2425) =
    MixedData.row1524 := by decide +kernel

theorem sourceRowsAt1525 : MixedData.sourceRows (1525 : Fin 2425) =
    MixedData.row1525 := by decide +kernel

theorem sourceRowsAt1526 : MixedData.sourceRows (1526 : Fin 2425) =
    MixedData.row1526 := by decide +kernel

theorem sourceRowsAt1527 : MixedData.sourceRows (1527 : Fin 2425) =
    MixedData.row1527 := by decide +kernel

theorem sourceRowsAt1528 : MixedData.sourceRows (1528 : Fin 2425) =
    MixedData.row1528 := by decide +kernel

theorem sourceRowsAt1529 : MixedData.sourceRows (1529 : Fin 2425) =
    MixedData.row1529 := by decide +kernel

theorem sourceRowsAt1530 : MixedData.sourceRows (1530 : Fin 2425) =
    MixedData.row1530 := by decide +kernel

theorem sourceRowsAt1531 : MixedData.sourceRows (1531 : Fin 2425) =
    MixedData.row1531 := by decide +kernel

theorem sourceRowsAt1532 : MixedData.sourceRows (1532 : Fin 2425) =
    MixedData.row1532 := by decide +kernel

theorem sourceRowsAt1533 : MixedData.sourceRows (1533 : Fin 2425) =
    MixedData.row1533 := by decide +kernel

theorem sourceRowsAt1534 : MixedData.sourceRows (1534 : Fin 2425) =
    MixedData.row1534 := by decide +kernel

theorem sourceRowsAt1535 : MixedData.sourceRows (1535 : Fin 2425) =
    MixedData.row1535 := by decide +kernel

theorem chunkSound95 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 95) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1520 ∨ k.val = 1521 ∨ k.val = 1522 ∨ k.val = 1523 ∨ k.val = 1524 ∨ k.val = 1525 ∨ k.val = 1526 ∨ k.val = 1527 ∨ k.val = 1528 ∨ k.val = 1529 ∨ k.val = 1530 ∨ k.val = 1531 ∨ k.val = 1532 ∨ k.val = 1533 ∨ k.val = 1534 ∨ k.val = 1535 := by omega
  rcases heq with h1520 | h1521 | h1522 | h1523 | h1524 | h1525 | h1526 | h1527 | h1528 | h1529 | h1530 | h1531 | h1532 | h1533 | h1534 | h1535
  · have he : k = (1520 : Fin 2425) := Fin.ext h1520
    subst k
    rw [sourceRowsAt1520]
    exact rowSound1520 B hB hF
  · have he : k = (1521 : Fin 2425) := Fin.ext h1521
    subst k
    rw [sourceRowsAt1521]
    exact rowSound1521 B hB hF
  · have he : k = (1522 : Fin 2425) := Fin.ext h1522
    subst k
    rw [sourceRowsAt1522]
    exact rowSound1522 B hB hF
  · have he : k = (1523 : Fin 2425) := Fin.ext h1523
    subst k
    rw [sourceRowsAt1523]
    exact rowSound1523 B hB hF
  · have he : k = (1524 : Fin 2425) := Fin.ext h1524
    subst k
    rw [sourceRowsAt1524]
    exact rowSound1524 B hB hF
  · have he : k = (1525 : Fin 2425) := Fin.ext h1525
    subst k
    rw [sourceRowsAt1525]
    exact rowSound1525 B hB hF
  · have he : k = (1526 : Fin 2425) := Fin.ext h1526
    subst k
    rw [sourceRowsAt1526]
    exact rowSound1526 B hB hF
  · have he : k = (1527 : Fin 2425) := Fin.ext h1527
    subst k
    rw [sourceRowsAt1527]
    exact rowSound1527 B hB hF
  · have he : k = (1528 : Fin 2425) := Fin.ext h1528
    subst k
    rw [sourceRowsAt1528]
    exact rowSound1528 B hB hF
  · have he : k = (1529 : Fin 2425) := Fin.ext h1529
    subst k
    rw [sourceRowsAt1529]
    exact rowSound1529 B hB hF
  · have he : k = (1530 : Fin 2425) := Fin.ext h1530
    subst k
    rw [sourceRowsAt1530]
    exact rowSound1530 B hB hF
  · have he : k = (1531 : Fin 2425) := Fin.ext h1531
    subst k
    rw [sourceRowsAt1531]
    exact rowSound1531 B hB hF
  · have he : k = (1532 : Fin 2425) := Fin.ext h1532
    subst k
    rw [sourceRowsAt1532]
    exact rowSound1532 B hB hF
  · have he : k = (1533 : Fin 2425) := Fin.ext h1533
    subst k
    rw [sourceRowsAt1533]
    exact rowSound1533 B hB hF
  · have he : k = (1534 : Fin 2425) := Fin.ext h1534
    subst k
    rw [sourceRowsAt1534]
    exact rowSound1534 B hB hF
  · have he : k = (1535 : Fin 2425) := Fin.ext h1535
    subst k
    rw [sourceRowsAt1535]
    exact rowSound1535 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
