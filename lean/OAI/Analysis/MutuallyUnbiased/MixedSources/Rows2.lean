import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources1

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero32 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource32 (mixedVector B) = 0 := by
  have h1067 : mixedVector B (Sum.inr 1067) = Sparse.eval nodeValue1067 (mixedVector B) := by
    change mixedMoment B node1067 node1067Labels = _
    exact sound1067 B hB hF
  have h2041 : mixedVector B (Sum.inr 2041) = Sparse.eval nodeValue2041 (mixedVector B) := by
    change mixedMoment B node2041 node2041Labels = _
    exact sound2041 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm34, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1067, h2041, h2284, h2285, h4085, reducedSource32] using sourceEq34 B hB

theorem rowSound32 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row32 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck32, numericCheck32, reducedZero32 B hB hF, mul_zero]

theorem reducedZero33 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource33 (mixedVector B) = 0 := by
  have h1459 : mixedVector B (Sum.inr 1459) = Sparse.eval nodeValue1459 (mixedVector B) := by
    change mixedMoment B node1459 node1459Labels = _
    exact sound1459 B hB hF
  have h2041 : mixedVector B (Sum.inr 2041) = Sparse.eval nodeValue2041 (mixedVector B) := by
    change mixedMoment B node2041 node2041Labels = _
    exact sound2041 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm35, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1459, h2041, h2063, h2285, h4085, reducedSource33] using sourceEq35 B hB

theorem rowSound33 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row33 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck33, numericCheck33, reducedZero33 B hB hF, mul_zero]

theorem reducedZero34 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource34 (mixedVector B) = 0 := by
  have h1069 : mixedVector B (Sum.inr 1069) = Sparse.eval nodeValue1069 (mixedVector B) := by
    change mixedMoment B node1069 node1069Labels = _
    exact sound1069 B hB hF
  have h1459 : mixedVector B (Sum.inr 1459) = Sparse.eval nodeValue1459 (mixedVector B) := by
    change mixedMoment B node1459 node1459Labels = _
    exact sound1459 B hB hF
  have h2285 : mixedVector B (Sum.inr 2285) = Sparse.eval nodeValue2285 (mixedVector B) := by
    change mixedMoment B node2285 node2285Labels = _
    exact sound2285 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm36, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1069, h1459, h2285, h4085, reducedSource34] using sourceEq36 B hB

theorem rowSound34 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row34 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck34, numericCheck34, reducedZero34 B hB hF, mul_zero]

theorem reducedZero35 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource35 (mixedVector B) = 0 := by
  have h795 : mixedVector B (Sum.inr 795) = Sparse.eval nodeValue795 (mixedVector B) := by
    change mixedMoment B node795 node795Labels = _
    exact sound795 B hB hF
  have h797 : mixedVector B (Sum.inr 797) = Sparse.eval nodeValue797 (mixedVector B) := by
    change mixedMoment B node797 node797Labels = _
    exact sound797 B hB hF
  have h814 : mixedVector B (Sum.inr 814) = Sparse.eval nodeValue814 (mixedVector B) := by
    change mixedMoment B node814 node814Labels = _
    exact sound814 B hB hF
  have h829 : mixedVector B (Sum.inr 829) = Sparse.eval nodeValue829 (mixedVector B) := by
    change mixedMoment B node829 node829Labels = _
    exact sound829 B hB hF
  have h1355 : mixedVector B (Sum.inr 1355) = Sparse.eval nodeValue1355 (mixedVector B) := by
    change mixedMoment B node1355 node1355Labels = _
    exact sound1355 B hB hF
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h1903 : mixedVector B (Sum.inr 1903) = Sparse.eval nodeValue1903 (mixedVector B) := by
    change mixedMoment B node1903 node1903Labels = _
    exact sound1903 B hB hF
  have h1916 : mixedVector B (Sum.inr 1916) = Sparse.eval nodeValue1916 (mixedVector B) := by
    change mixedMoment B node1916 node1916Labels = _
    exact sound1916 B hB hF
  have h1927 : mixedVector B (Sum.inr 1927) = Sparse.eval nodeValue1927 (mixedVector B) := by
    change mixedMoment B node1927 node1927Labels = _
    exact sound1927 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3224 : mixedVector B (Sum.inr 3224) = Sparse.eval nodeValue3224 (mixedVector B) := by
    change mixedMoment B node3224 node3224Labels = _
    exact sound3224 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  simpa only [sourceForm38, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h795, h797, h814, h829, h1355, h1369, h1408, h1903, h1916, h1927, h2037, h2063, h2092, h2113, h2254, h2267, h2280, h3054, h3222, h3224, h3225, reducedSource35] using sourceEq38 B hB

theorem rowSound35 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row35 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck35, numericCheck35, reducedZero35 B hB hF, mul_zero]

theorem reducedZero36 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource36 (mixedVector B) = 0 := by
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm40, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2255, h2520, h3156, h3161, h3626, h4084, reducedSource36] using sourceEq40 B hB

theorem rowSound36 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row36 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck36, numericCheck36, reducedZero36 B hB hF, mul_zero]

theorem reducedZero37 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource37 (mixedVector B) = 0 := by
  have h1029 : mixedVector B (Sum.inr 1029) = Sparse.eval nodeValue1029 (mixedVector B) := by
    change mixedMoment B node1029 node1029Labels = _
    exact sound1029 B hB hF
  have h1031 : mixedVector B (Sum.inr 1031) = Sparse.eval nodeValue1031 (mixedVector B) := by
    change mixedMoment B node1031 node1031Labels = _
    exact sound1031 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm41, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1029, h1031, h1047, h1061, h2255, h4084, reducedSource37] using sourceEq41 B hB

theorem rowSound37 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row37 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck37, numericCheck37, reducedZero37 B hB hF, mul_zero]

theorem reducedZero38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource38 (mixedVector B) = 0 := by
  have h1029 : mixedVector B (Sum.inr 1029) = Sparse.eval nodeValue1029 (mixedVector B) := by
    change mixedMoment B node1029 node1029Labels = _
    exact sound1029 B hB hF
  have h2013 : mixedVector B (Sum.inr 2013) = Sparse.eval nodeValue2013 (mixedVector B) := by
    change mixedMoment B node2013 node2013Labels = _
    exact sound2013 B hB hF
  have h2096 : mixedVector B (Sum.inr 2096) = Sparse.eval nodeValue2096 (mixedVector B) := by
    change mixedMoment B node2096 node2096Labels = _
    exact sound2096 B hB hF
  have h2125 : mixedVector B (Sum.inr 2125) = Sparse.eval nodeValue2125 (mixedVector B) := by
    change mixedMoment B node2125 node2125Labels = _
    exact sound2125 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm42, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1029, h2013, h2096, h2125, h2253, h2255, h4084, reducedSource38] using sourceEq42 B hB

theorem rowSound38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row38 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck38, numericCheck38, reducedZero38 B hB hF, mul_zero]

theorem reducedZero39 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource39 (mixedVector B) = 0 := by
  have h1458 : mixedVector B (Sum.inr 1458) = Sparse.eval nodeValue1458 (mixedVector B) := by
    change mixedMoment B node1458 node1458Labels = _
    exact sound1458 B hB hF
  have h2013 : mixedVector B (Sum.inr 2013) = Sparse.eval nodeValue2013 (mixedVector B) := by
    change mixedMoment B node2013 node2013Labels = _
    exact sound2013 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm43, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1458, h2013, h2026, h2037, h2255, h3156, h4084, reducedSource39] using sourceEq43 B hB

theorem rowSound39 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row39 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck39, numericCheck39, reducedZero39 B hB hF, mul_zero]

theorem reducedZero40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource40 (mixedVector B) = 0 := by
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm44, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1061, h2037, h2136, h2255, h2279, h4084, reducedSource40] using sourceEq44 B hB

theorem rowSound40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row40 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck40, numericCheck40, reducedZero40 B hB hF, mul_zero]

theorem reducedZero41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource41 (mixedVector B) = 0 := by
  have h1462 : mixedVector B (Sum.inr 1462) = Sparse.eval nodeValue1462 (mixedVector B) := by
    change mixedMoment B node1462 node1462Labels = _
    exact sound1462 B hB hF
  have h2096 : mixedVector B (Sum.inr 2096) = Sparse.eval nodeValue2096 (mixedVector B) := by
    change mixedMoment B node2096 node2096Labels = _
    exact sound2096 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h3161 : mixedVector B (Sum.inr 3161) = Sparse.eval nodeValue3161 (mixedVector B) := by
    change mixedMoment B node3161 node3161Labels = _
    exact sound3161 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm45, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1462, h2096, h2113, h2255, h3161, h4084, reducedSource41] using sourceEq45 B hB

theorem rowSound41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row41 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck41, numericCheck41, reducedZero41 B hB hF, mul_zero]

theorem reducedZero42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource42 (mixedVector B) = 0 := by
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h2113 : mixedVector B (Sum.inr 2113) = Sparse.eval nodeValue2113 (mixedVector B) := by
    change mixedMoment B node2113 node2113Labels = _
    exact sound2113 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm46, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1047, h2026, h2113, h2255, h2266, h4084, reducedSource42] using sourceEq46 B hB

theorem rowSound42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row42 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck42, numericCheck42, reducedZero42 B hB hF, mul_zero]

theorem reducedZero43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource43 (mixedVector B) = 0 := by
  have h1461 : mixedVector B (Sum.inr 1461) = Sparse.eval nodeValue1461 (mixedVector B) := by
    change mixedMoment B node1461 node1461Labels = _
    exact sound1461 B hB hF
  have h2125 : mixedVector B (Sum.inr 2125) = Sparse.eval nodeValue2125 (mixedVector B) := by
    change mixedMoment B node2125 node2125Labels = _
    exact sound2125 B hB hF
  have h2136 : mixedVector B (Sum.inr 2136) = Sparse.eval nodeValue2136 (mixedVector B) := by
    change mixedMoment B node2136 node2136Labels = _
    exact sound2136 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2520 : mixedVector B (Sum.inr 2520) = Sparse.eval nodeValue2520 (mixedVector B) := by
    change mixedMoment B node2520 node2520Labels = _
    exact sound2520 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm47, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1461, h2125, h2136, h2255, h2520, h4084, reducedSource43] using sourceEq47 B hB

theorem rowSound43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row43 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck43, numericCheck43, reducedZero43 B hB hF, mul_zero]

theorem reducedZero44 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource44 (mixedVector B) = 0 := by
  have h1031 : mixedVector B (Sum.inr 1031) = Sparse.eval nodeValue1031 (mixedVector B) := by
    change mixedMoment B node1031 node1031Labels = _
    exact sound1031 B hB hF
  have h1458 : mixedVector B (Sum.inr 1458) = Sparse.eval nodeValue1458 (mixedVector B) := by
    change mixedMoment B node1458 node1458Labels = _
    exact sound1458 B hB hF
  have h1461 : mixedVector B (Sum.inr 1461) = Sparse.eval nodeValue1461 (mixedVector B) := by
    change mixedMoment B node1461 node1461Labels = _
    exact sound1461 B hB hF
  have h1462 : mixedVector B (Sum.inr 1462) = Sparse.eval nodeValue1462 (mixedVector B) := by
    change mixedMoment B node1462 node1462Labels = _
    exact sound1462 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm48, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1031, h1458, h1461, h1462, h2255, h4084, reducedSource44] using sourceEq48 B hB

theorem rowSound44 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row44 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck44, numericCheck44, reducedZero44 B hB hF, mul_zero]

theorem reducedZero45 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource45 (mixedVector B) = 0 := by
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm51, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1084, h2055, h2284, h2290, h2294, h4085, reducedSource45] using sourceEq51 B hB

theorem rowSound45 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row45 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck45, numericCheck45, reducedZero45 B hB hF, mul_zero]

theorem reducedZero46 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource46 (mixedVector B) = 0 := by
  have h1066 : mixedVector B (Sum.inr 1066) = Sparse.eval nodeValue1066 (mixedVector B) := by
    change mixedMoment B node1066 node1066Labels = _
    exact sound1066 B hB hF
  have h1067 : mixedVector B (Sum.inr 1067) = Sparse.eval nodeValue1067 (mixedVector B) := by
    change mixedMoment B node1067 node1067Labels = _
    exact sound1067 B hB hF
  have h1068 : mixedVector B (Sum.inr 1068) = Sparse.eval nodeValue1068 (mixedVector B) := by
    change mixedMoment B node1068 node1068Labels = _
    exact sound1068 B hB hF
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm52, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1066, h1067, h1068, h1084, h2284, h4085, reducedSource46] using sourceEq52 B hB

theorem rowSound46 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row46 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck46, numericCheck46, reducedZero46 B hB hF, mul_zero]

theorem reducedZero47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource47 (mixedVector B) = 0 := by
  have h1066 : mixedVector B (Sum.inr 1066) = Sparse.eval nodeValue1066 (mixedVector B) := by
    change mixedMoment B node1066 node1066Labels = _
    exact sound1066 B hB hF
  have h2040 : mixedVector B (Sum.inr 2040) = Sparse.eval nodeValue2040 (mixedVector B) := by
    change mixedMoment B node2040 node2040Labels = _
    exact sound2040 B hB hF
  have h2283 : mixedVector B (Sum.inr 2283) = Sparse.eval nodeValue2283 (mixedVector B) := by
    change mixedMoment B node2283 node2283Labels = _
    exact sound2283 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm53, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1066, h2040, h2283, h2284, h4085, reducedSource47] using sourceEq53 B hB

theorem rowSound47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row47 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck47, numericCheck47, reducedZero47 B hB hF, mul_zero]

theorem sourceRowsAt32 : MixedData.sourceRows (32 : Fin 2425) =
    MixedData.row32 := by decide +kernel

theorem sourceRowsAt33 : MixedData.sourceRows (33 : Fin 2425) =
    MixedData.row33 := by decide +kernel

theorem sourceRowsAt34 : MixedData.sourceRows (34 : Fin 2425) =
    MixedData.row34 := by decide +kernel

theorem sourceRowsAt35 : MixedData.sourceRows (35 : Fin 2425) =
    MixedData.row35 := by decide +kernel

theorem sourceRowsAt36 : MixedData.sourceRows (36 : Fin 2425) =
    MixedData.row36 := by decide +kernel

theorem sourceRowsAt37 : MixedData.sourceRows (37 : Fin 2425) =
    MixedData.row37 := by decide +kernel

theorem sourceRowsAt38 : MixedData.sourceRows (38 : Fin 2425) =
    MixedData.row38 := by decide +kernel

theorem sourceRowsAt39 : MixedData.sourceRows (39 : Fin 2425) =
    MixedData.row39 := by decide +kernel

theorem sourceRowsAt40 : MixedData.sourceRows (40 : Fin 2425) =
    MixedData.row40 := by decide +kernel

theorem sourceRowsAt41 : MixedData.sourceRows (41 : Fin 2425) =
    MixedData.row41 := by decide +kernel

theorem sourceRowsAt42 : MixedData.sourceRows (42 : Fin 2425) =
    MixedData.row42 := by decide +kernel

theorem sourceRowsAt43 : MixedData.sourceRows (43 : Fin 2425) =
    MixedData.row43 := by decide +kernel

theorem sourceRowsAt44 : MixedData.sourceRows (44 : Fin 2425) =
    MixedData.row44 := by decide +kernel

theorem sourceRowsAt45 : MixedData.sourceRows (45 : Fin 2425) =
    MixedData.row45 := by decide +kernel

theorem sourceRowsAt46 : MixedData.sourceRows (46 : Fin 2425) =
    MixedData.row46 := by decide +kernel

theorem sourceRowsAt47 : MixedData.sourceRows (47 : Fin 2425) =
    MixedData.row47 := by decide +kernel

theorem chunkSound2 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 2) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 32 ∨ k.val = 33 ∨ k.val = 34 ∨ k.val = 35 ∨ k.val = 36 ∨ k.val = 37 ∨ k.val = 38 ∨ k.val = 39 ∨ k.val = 40 ∨ k.val = 41 ∨ k.val = 42 ∨ k.val = 43 ∨ k.val = 44 ∨ k.val = 45 ∨ k.val = 46 ∨ k.val = 47 := by omega
  rcases heq with h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47
  · have he : k = (32 : Fin 2425) := Fin.ext h32
    subst k
    rw [sourceRowsAt32]
    exact rowSound32 B hB hF
  · have he : k = (33 : Fin 2425) := Fin.ext h33
    subst k
    rw [sourceRowsAt33]
    exact rowSound33 B hB hF
  · have he : k = (34 : Fin 2425) := Fin.ext h34
    subst k
    rw [sourceRowsAt34]
    exact rowSound34 B hB hF
  · have he : k = (35 : Fin 2425) := Fin.ext h35
    subst k
    rw [sourceRowsAt35]
    exact rowSound35 B hB hF
  · have he : k = (36 : Fin 2425) := Fin.ext h36
    subst k
    rw [sourceRowsAt36]
    exact rowSound36 B hB hF
  · have he : k = (37 : Fin 2425) := Fin.ext h37
    subst k
    rw [sourceRowsAt37]
    exact rowSound37 B hB hF
  · have he : k = (38 : Fin 2425) := Fin.ext h38
    subst k
    rw [sourceRowsAt38]
    exact rowSound38 B hB hF
  · have he : k = (39 : Fin 2425) := Fin.ext h39
    subst k
    rw [sourceRowsAt39]
    exact rowSound39 B hB hF
  · have he : k = (40 : Fin 2425) := Fin.ext h40
    subst k
    rw [sourceRowsAt40]
    exact rowSound40 B hB hF
  · have he : k = (41 : Fin 2425) := Fin.ext h41
    subst k
    rw [sourceRowsAt41]
    exact rowSound41 B hB hF
  · have he : k = (42 : Fin 2425) := Fin.ext h42
    subst k
    rw [sourceRowsAt42]
    exact rowSound42 B hB hF
  · have he : k = (43 : Fin 2425) := Fin.ext h43
    subst k
    rw [sourceRowsAt43]
    exact rowSound43 B hB hF
  · have he : k = (44 : Fin 2425) := Fin.ext h44
    subst k
    rw [sourceRowsAt44]
    exact rowSound44 B hB hF
  · have he : k = (45 : Fin 2425) := Fin.ext h45
    subst k
    rw [sourceRowsAt45]
    exact rowSound45 B hB hF
  · have he : k = (46 : Fin 2425) := Fin.ext h46
    subst k
    rw [sourceRowsAt46]
    exact rowSound46 B hB hF
  · have he : k = (47 : Fin 2425) := Fin.ext h47
    subst k
    rw [sourceRowsAt47]
    exact rowSound47 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
