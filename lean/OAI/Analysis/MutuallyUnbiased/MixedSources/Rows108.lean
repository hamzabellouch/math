import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic108
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources65

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1728 (mixedVector B) = 0 := by
  have h2377 : mixedVector B (Sum.inr 2377) = Sparse.eval nodeValue2377 (mixedVector B) := by
    change mixedMoment B node2377 node2377Labels = _
    exact sound2377 B hB hF
  have h2541 : mixedVector B (Sum.inr 2541) = Sparse.eval nodeValue2541 (mixedVector B) := by
    change mixedMoment B node2541 node2541Labels = _
    exact sound2541 B hB hF
  have h2551 : mixedVector B (Sum.inr 2551) = Sparse.eval nodeValue2551 (mixedVector B) := by
    change mixedMoment B node2551 node2551Labels = _
    exact sound2551 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2057, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2377, h2541, h2551, h2705, h3757, h4088, reducedSource1728] using sourceEq2057 B hB

theorem rowSound1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1728 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1728, numericCheck1728, reducedZero1728 B hB hF, mul_zero]

theorem reducedZero1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1729 (mixedVector B) = 0 := by
  have h1897 : mixedVector B (Sum.inr 1897) = Sparse.eval nodeValue1897 (mixedVector B) := by
    change mixedMoment B node1897 node1897Labels = _
    exact sound1897 B hB hF
  have h2540 : mixedVector B (Sum.inr 2540) = Sparse.eval nodeValue2540 (mixedVector B) := by
    change mixedMoment B node2540 node2540Labels = _
    exact sound2540 B hB hF
  have h2550 : mixedVector B (Sum.inr 2550) = Sparse.eval nodeValue2550 (mixedVector B) := by
    change mixedMoment B node2550 node2550Labels = _
    exact sound2550 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2059, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1897, h2540, h2550, h2704, h3459, h4080, reducedSource1729] using sourceEq2059 B hB

theorem rowSound1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1729 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1729, numericCheck1729, reducedZero1729 B hB hF, mul_zero]

theorem reducedZero1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1730 (mixedVector B) = 0 := by
  have h2075 : mixedVector B (Sum.inr 2075) = Sparse.eval nodeValue2075 (mixedVector B) := by
    change mixedMoment B node2075 node2075Labels = _
    exact sound2075 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h2101 : mixedVector B (Sum.inr 2101) = Sparse.eval nodeValue2101 (mixedVector B) := by
    change mixedMoment B node2101 node2101Labels = _
    exact sound2101 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2061, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2075, h2079, h2082, h2101, h2205, h3564, h4080, reducedSource1730] using sourceEq2061 B hB

theorem rowSound1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1730 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1730, numericCheck1730, reducedZero1730 B hB hF, mul_zero]

theorem reducedZero1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1731 (mixedVector B) = 0 := by
  have h1123 : mixedVector B (Sum.inr 1123) = Sparse.eval nodeValue1123 (mixedVector B) := by
    change mixedMoment B node1123 node1123Labels = _
    exact sound1123 B hB hF
  have h1875 : mixedVector B (Sum.inr 1875) = Sparse.eval nodeValue1875 (mixedVector B) := by
    change mixedMoment B node1875 node1875Labels = _
    exact sound1875 B hB hF
  have h1880 : mixedVector B (Sum.inr 1880) = Sparse.eval nodeValue1880 (mixedVector B) := by
    change mixedMoment B node1880 node1880Labels = _
    exact sound1880 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2504 : mixedVector B (Sum.inr 2504) = Sparse.eval nodeValue2504 (mixedVector B) := by
    change mixedMoment B node2504 node2504Labels = _
    exact sound2504 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2062, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1123, h1875, h1880, h1914, h2079, h2504, h4080, reducedSource1731] using sourceEq2062 B hB

theorem rowSound1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1731 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1731, numericCheck1731, reducedZero1731 B hB hF, mul_zero]

theorem reducedZero1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1732 (mixedVector B) = 0 := by
  have h916 : mixedVector B (Sum.inr 916) = Sparse.eval nodeValue916 (mixedVector B) := by
    change mixedMoment B node916 node916Labels = _
    exact sound916 B hB hF
  have h1799 : mixedVector B (Sum.inr 1799) = Sparse.eval nodeValue1799 (mixedVector B) := by
    change mixedMoment B node1799 node1799Labels = _
    exact sound1799 B hB hF
  have h1874 : mixedVector B (Sum.inr 1874) = Sparse.eval nodeValue1874 (mixedVector B) := by
    change mixedMoment B node1874 node1874Labels = _
    exact sound1874 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2047 : mixedVector B (Sum.inr 2047) = Sparse.eval nodeValue2047 (mixedVector B) := by
    change mixedMoment B node2047 node2047Labels = _
    exact sound2047 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm2064, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h916, h1799, h1874, h1911, h2018, h2047, h4081, reducedSource1732] using sourceEq2064 B hB

theorem rowSound1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1732 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1732, numericCheck1732, reducedZero1732 B hB hF, mul_zero]

theorem reducedZero1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1733 (mixedVector B) = 0 := by
  have h2449 : mixedVector B (Sum.inr 2449) = Sparse.eval nodeValue2449 (mixedVector B) := by
    change mixedMoment B node2449 node2449Labels = _
    exact sound2449 B hB hF
  have h2452 : mixedVector B (Sum.inr 2452) = Sparse.eval nodeValue2452 (mixedVector B) := by
    change mixedMoment B node2452 node2452Labels = _
    exact sound2452 B hB hF
  have h2461 : mixedVector B (Sum.inr 2461) = Sparse.eval nodeValue2461 (mixedVector B) := by
    change mixedMoment B node2461 node2461Labels = _
    exact sound2461 B hB hF
  have h2477 : mixedVector B (Sum.inr 2477) = Sparse.eval nodeValue2477 (mixedVector B) := by
    change mixedMoment B node2477 node2477Labels = _
    exact sound2477 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h3793 : mixedVector B (Sum.inr 3793) = Sparse.eval nodeValue3793 (mixedVector B) := by
    change mixedMoment B node3793 node3793Labels = _
    exact sound3793 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm2065, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2449, h2452, h2461, h2477, h2694, h3793, h4090, reducedSource1733] using sourceEq2065 B hB

theorem rowSound1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1733 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1733, numericCheck1733, reducedZero1733 B hB hF, mul_zero]

theorem reducedZero1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1734 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  simpa only [sourceForm2072, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4346, h4356, h4360, h4505, h4543, h4557, h4605, h4681, h4692, h4760, h4769, h4804, h4834, h4841, h4846, h4897, h5099, h5110, h5272, h5274, reducedSource1734] using sourceEq2072 B hB

theorem rowSound1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1734 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1734, numericCheck1734, reducedZero1734 B hB hF, mul_zero]

theorem reducedZero1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1735 (mixedVector B) = 0 := by
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2173 : mixedVector B (Sum.inr 2173) = Sparse.eval nodeValue2173 (mixedVector B) := by
    change mixedMoment B node2173 node2173Labels = _
    exact sound2173 B hB hF
  have h2184 : mixedVector B (Sum.inr 2184) = Sparse.eval nodeValue2184 (mixedVector B) := by
    change mixedMoment B node2184 node2184Labels = _
    exact sound2184 B hB hF
  have h2185 : mixedVector B (Sum.inr 2185) = Sparse.eval nodeValue2185 (mixedVector B) := by
    change mixedMoment B node2185 node2185Labels = _
    exact sound2185 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2073, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1674, h1692, h1693, h1754, h2151, h2167, h2168, h2173, h2184, h2185, h2203, h2205, h2226, h2228, h2229, h2292, h2685, h2704, h2740, h2742, h4084, reducedSource1735] using sourceEq2073 B hB

theorem rowSound1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1735 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1735, numericCheck1735, reducedZero1735 B hB hF, mul_zero]

theorem reducedZero1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1736 (mixedVector B) = 0 := by
  have h2382 : mixedVector B (Sum.inr 2382) = Sparse.eval nodeValue2382 (mixedVector B) := by
    change mixedMoment B node2382 node2382Labels = _
    exact sound2382 B hB hF
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2388 : mixedVector B (Sum.inr 2388) = Sparse.eval nodeValue2388 (mixedVector B) := by
    change mixedMoment B node2388 node2388Labels = _
    exact sound2388 B hB hF
  have h2403 : mixedVector B (Sum.inr 2403) = Sparse.eval nodeValue2403 (mixedVector B) := by
    change mixedMoment B node2403 node2403Labels = _
    exact sound2403 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2074, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2382, h2385, h2388, h2403, h2672, h3766, h4088, reducedSource1736] using sourceEq2074 B hB

theorem rowSound1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1736 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1736, numericCheck1736, reducedZero1736 B hB hF, mul_zero]

theorem reducedZero1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1737 (mixedVector B) = 0 := by
  have h2385 : mixedVector B (Sum.inr 2385) = Sparse.eval nodeValue2385 (mixedVector B) := by
    change mixedMoment B node2385 node2385Labels = _
    exact sound2385 B hB hF
  have h2459 : mixedVector B (Sum.inr 2459) = Sparse.eval nodeValue2459 (mixedVector B) := by
    change mixedMoment B node2459 node2459Labels = _
    exact sound2459 B hB hF
  have h2468 : mixedVector B (Sum.inr 2468) = Sparse.eval nodeValue2468 (mixedVector B) := by
    change mixedMoment B node2468 node2468Labels = _
    exact sound2468 B hB hF
  have h2505 : mixedVector B (Sum.inr 2505) = Sparse.eval nodeValue2505 (mixedVector B) := by
    change mixedMoment B node2505 node2505Labels = _
    exact sound2505 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2077, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2385, h2459, h2468, h2505, h2705, h3766, h4088, reducedSource1737] using sourceEq2077 B hB

theorem rowSound1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1737 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1737, numericCheck1737, reducedZero1737 B hB hF, mul_zero]

theorem reducedZero1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1738 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4287 : mixedVector B (Sum.inr 4287) = Sparse.eval nodeValue4287 (mixedVector B) := by
    change mixedMoment B node4287 node4287Labels = _
    exact sound4287 B hB hF
  have h4293 : mixedVector B (Sum.inr 4293) = Sparse.eval nodeValue4293 (mixedVector B) := by
    change mixedMoment B node4293 node4293Labels = _
    exact sound4293 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4308 : mixedVector B (Sum.inr 4308) = Sparse.eval nodeValue4308 (mixedVector B) := by
    change mixedMoment B node4308 node4308Labels = _
    exact sound4308 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4525 : mixedVector B (Sum.inr 4525) = Sparse.eval nodeValue4525 (mixedVector B) := by
    change mixedMoment B node4525 node4525Labels = _
    exact sound4525 B hB hF
  have h4538 : mixedVector B (Sum.inr 4538) = Sparse.eval nodeValue4538 (mixedVector B) := by
    change mixedMoment B node4538 node4538Labels = _
    exact sound4538 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4649 : mixedVector B (Sum.inr 4649) = Sparse.eval nodeValue4649 (mixedVector B) := by
    change mixedMoment B node4649 node4649Labels = _
    exact sound4649 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4712 : mixedVector B (Sum.inr 4712) = Sparse.eval nodeValue4712 (mixedVector B) := by
    change mixedMoment B node4712 node4712Labels = _
    exact sound4712 B hB hF
  have h4721 : mixedVector B (Sum.inr 4721) = Sparse.eval nodeValue4721 (mixedVector B) := by
    change mixedMoment B node4721 node4721Labels = _
    exact sound4721 B hB hF
  have h4726 : mixedVector B (Sum.inr 4726) = Sparse.eval nodeValue4726 (mixedVector B) := by
    change mixedMoment B node4726 node4726Labels = _
    exact sound4726 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4745 : mixedVector B (Sum.inr 4745) = Sparse.eval nodeValue4745 (mixedVector B) := by
    change mixedMoment B node4745 node4745Labels = _
    exact sound4745 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4827 : mixedVector B (Sum.inr 4827) = Sparse.eval nodeValue4827 (mixedVector B) := by
    change mixedMoment B node4827 node4827Labels = _
    exact sound4827 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h5014 : mixedVector B (Sum.inr 5014) = Sparse.eval nodeValue5014 (mixedVector B) := by
    change mixedMoment B node5014 node5014Labels = _
    exact sound5014 B hB hF
  have h5055 : mixedVector B (Sum.inr 5055) = Sparse.eval nodeValue5055 (mixedVector B) := by
    change mixedMoment B node5055 node5055Labels = _
    exact sound5055 B hB hF
  have h5094 : mixedVector B (Sum.inr 5094) = Sparse.eval nodeValue5094 (mixedVector B) := by
    change mixedMoment B node5094 node5094Labels = _
    exact sound5094 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  simpa only [sourceForm2079, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4287, h4293, h4295, h4308, h4401, h4521, h4525, h4538, h4583, h4631, h4637, h4649, h4706, h4712, h4721, h4726, h4728, h4736, h4741, h4745, h4779, h4827, h4832, h4834, h5014, h5055, h5094, h5099, h5101, reducedSource1738] using sourceEq2079 B hB

theorem rowSound1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1738 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1738, numericCheck1738, reducedZero1738 B hB hF, mul_zero]

theorem reducedZero1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1739 (mixedVector B) = 0 := by
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4304 : mixedVector B (Sum.inr 4304) = Sparse.eval nodeValue4304 (mixedVector B) := by
    change mixedMoment B node4304 node4304Labels = _
    exact sound4304 B hB hF
  have h4317 : mixedVector B (Sum.inr 4317) = Sparse.eval nodeValue4317 (mixedVector B) := by
    change mixedMoment B node4317 node4317Labels = _
    exact sound4317 B hB hF
  have h4319 : mixedVector B (Sum.inr 4319) = Sparse.eval nodeValue4319 (mixedVector B) := by
    change mixedMoment B node4319 node4319Labels = _
    exact sound4319 B hB hF
  have h4431 : mixedVector B (Sum.inr 4431) = Sparse.eval nodeValue4431 (mixedVector B) := by
    change mixedMoment B node4431 node4431Labels = _
    exact sound4431 B hB hF
  have h4643 : mixedVector B (Sum.inr 4643) = Sparse.eval nodeValue4643 (mixedVector B) := by
    change mixedMoment B node4643 node4643Labels = _
    exact sound4643 B hB hF
  have h4645 : mixedVector B (Sum.inr 4645) = Sparse.eval nodeValue4645 (mixedVector B) := by
    change mixedMoment B node4645 node4645Labels = _
    exact sound4645 B hB hF
  have h4655 : mixedVector B (Sum.inr 4655) = Sparse.eval nodeValue4655 (mixedVector B) := by
    change mixedMoment B node4655 node4655Labels = _
    exact sound4655 B hB hF
  have h4657 : mixedVector B (Sum.inr 4657) = Sparse.eval nodeValue4657 (mixedVector B) := by
    change mixedMoment B node4657 node4657Labels = _
    exact sound4657 B hB hF
  have h4710 : mixedVector B (Sum.inr 4710) = Sparse.eval nodeValue4710 (mixedVector B) := by
    change mixedMoment B node4710 node4710Labels = _
    exact sound4710 B hB hF
  have h4719 : mixedVector B (Sum.inr 4719) = Sparse.eval nodeValue4719 (mixedVector B) := by
    change mixedMoment B node4719 node4719Labels = _
    exact sound4719 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4754 : mixedVector B (Sum.inr 4754) = Sparse.eval nodeValue4754 (mixedVector B) := by
    change mixedMoment B node4754 node4754Labels = _
    exact sound4754 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5021 : mixedVector B (Sum.inr 5021) = Sparse.eval nodeValue5021 (mixedVector B) := by
    change mixedMoment B node5021 node5021Labels = _
    exact sound5021 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  simpa only [sourceForm2084, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4081, h4304, h4317, h4319, h4431, h4643, h4645, h4655, h4657, h4710, h4719, h4741, h4742, h4754, h4788, h4841, h4843, h5000, h5021, h5107, h5109, reducedSource1739] using sourceEq2084 B hB

theorem rowSound1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1739 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1739, numericCheck1739, reducedZero1739 B hB hF, mul_zero]

theorem reducedZero1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1740 (mixedVector B) = 0 := by
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4350 : mixedVector B (Sum.inr 4350) = Sparse.eval nodeValue4350 (mixedVector B) := by
    change mixedMoment B node4350 node4350Labels = _
    exact sound4350 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4691 : mixedVector B (Sum.inr 4691) = Sparse.eval nodeValue4691 (mixedVector B) := by
    change mixedMoment B node4691 node4691Labels = _
    exact sound4691 B hB hF
  have h4759 : mixedVector B (Sum.inr 4759) = Sparse.eval nodeValue4759 (mixedVector B) := by
    change mixedMoment B node4759 node4759Labels = _
    exact sound4759 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  simpa only [sourceForm2085, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4085, h4343, h4350, h4359, h4501, h4678, h4691, h4759, h4832, h4837, h4845, h4897, h5261, reducedSource1740] using sourceEq2085 B hB

theorem rowSound1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1740 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1740, numericCheck1740, reducedZero1740 B hB hF, mul_zero]

theorem reducedZero1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1741 (mixedVector B) = 0 := by
  have h1666 : mixedVector B (Sum.inr 1666) = Sparse.eval nodeValue1666 (mixedVector B) := by
    change mixedMoment B node1666 node1666Labels = _
    exact sound1666 B hB hF
  have h1677 : mixedVector B (Sum.inr 1677) = Sparse.eval nodeValue1677 (mixedVector B) := by
    change mixedMoment B node1677 node1677Labels = _
    exact sound1677 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h2143 : mixedVector B (Sum.inr 2143) = Sparse.eval nodeValue2143 (mixedVector B) := by
    change mixedMoment B node2143 node2143Labels = _
    exact sound2143 B hB hF
  have h2159 : mixedVector B (Sum.inr 2159) = Sparse.eval nodeValue2159 (mixedVector B) := by
    change mixedMoment B node2159 node2159Labels = _
    exact sound2159 B hB hF
  have h2170 : mixedVector B (Sum.inr 2170) = Sparse.eval nodeValue2170 (mixedVector B) := by
    change mixedMoment B node2170 node2170Labels = _
    exact sound2170 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2086, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1666, h1677, h1683, h1730, h2143, h2159, h2170, h2193, h2208, h2218, h2268, h2726, h4085, reducedSource1741] using sourceEq2086 B hB

theorem rowSound1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1741 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1741, numericCheck1741, reducedZero1741 B hB hF, mul_zero]

theorem reducedZero1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1742 (mixedVector B) = 0 := by
  have h937 : mixedVector B (Sum.inr 937) = Sparse.eval nodeValue937 (mixedVector B) := by
    change mixedMoment B node937 node937Labels = _
    exact sound937 B hB hF
  have h1804 : mixedVector B (Sum.inr 1804) = Sparse.eval nodeValue1804 (mixedVector B) := by
    change mixedMoment B node1804 node1804Labels = _
    exact sound1804 B hB hF
  have h1817 : mixedVector B (Sum.inr 1817) = Sparse.eval nodeValue1817 (mixedVector B) := by
    change mixedMoment B node1817 node1817Labels = _
    exact sound1817 B hB hF
  have h2056 : mixedVector B (Sum.inr 2056) = Sparse.eval nodeValue2056 (mixedVector B) := by
    change mixedMoment B node2056 node2056Labels = _
    exact sound2056 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm2087, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h937, h1804, h1817, h2056, h2065, h4085, reducedSource1742] using sourceEq2087 B hB

theorem rowSound1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1742 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1742, numericCheck1742, reducedZero1742 B hB hF, mul_zero]

theorem reducedZero1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1743 (mixedVector B) = 0 := by
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4286 : mixedVector B (Sum.inr 4286) = Sparse.eval nodeValue4286 (mixedVector B) := by
    change mixedMoment B node4286 node4286Labels = _
    exact sound4286 B hB hF
  have h4289 : mixedVector B (Sum.inr 4289) = Sparse.eval nodeValue4289 (mixedVector B) := by
    change mixedMoment B node4289 node4289Labels = _
    exact sound4289 B hB hF
  have h4294 : mixedVector B (Sum.inr 4294) = Sparse.eval nodeValue4294 (mixedVector B) := by
    change mixedMoment B node4294 node4294Labels = _
    exact sound4294 B hB hF
  have h4302 : mixedVector B (Sum.inr 4302) = Sparse.eval nodeValue4302 (mixedVector B) := by
    change mixedMoment B node4302 node4302Labels = _
    exact sound4302 B hB hF
  have h4320 : mixedVector B (Sum.inr 4320) = Sparse.eval nodeValue4320 (mixedVector B) := by
    change mixedMoment B node4320 node4320Labels = _
    exact sound4320 B hB hF
  have h4324 : mixedVector B (Sum.inr 4324) = Sparse.eval nodeValue4324 (mixedVector B) := by
    change mixedMoment B node4324 node4324Labels = _
    exact sound4324 B hB hF
  have h4338 : mixedVector B (Sum.inr 4338) = Sparse.eval nodeValue4338 (mixedVector B) := by
    change mixedMoment B node4338 node4338Labels = _
    exact sound4338 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4426 : mixedVector B (Sum.inr 4426) = Sparse.eval nodeValue4426 (mixedVector B) := by
    change mixedMoment B node4426 node4426Labels = _
    exact sound4426 B hB hF
  have h4630 : mixedVector B (Sum.inr 4630) = Sparse.eval nodeValue4630 (mixedVector B) := by
    change mixedMoment B node4630 node4630Labels = _
    exact sound4630 B hB hF
  have h4636 : mixedVector B (Sum.inr 4636) = Sparse.eval nodeValue4636 (mixedVector B) := by
    change mixedMoment B node4636 node4636Labels = _
    exact sound4636 B hB hF
  have h4643 : mixedVector B (Sum.inr 4643) = Sparse.eval nodeValue4643 (mixedVector B) := by
    change mixedMoment B node4643 node4643Labels = _
    exact sound4643 B hB hF
  have h4658 : mixedVector B (Sum.inr 4658) = Sparse.eval nodeValue4658 (mixedVector B) := by
    change mixedMoment B node4658 node4658Labels = _
    exact sound4658 B hB hF
  have h4673 : mixedVector B (Sum.inr 4673) = Sparse.eval nodeValue4673 (mixedVector B) := by
    change mixedMoment B node4673 node4673Labels = _
    exact sound4673 B hB hF
  have h4708 : mixedVector B (Sum.inr 4708) = Sparse.eval nodeValue4708 (mixedVector B) := by
    change mixedMoment B node4708 node4708Labels = _
    exact sound4708 B hB hF
  have h4720 : mixedVector B (Sum.inr 4720) = Sparse.eval nodeValue4720 (mixedVector B) := by
    change mixedMoment B node4720 node4720Labels = _
    exact sound4720 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4738 : mixedVector B (Sum.inr 4738) = Sparse.eval nodeValue4738 (mixedVector B) := by
    change mixedMoment B node4738 node4738Labels = _
    exact sound4738 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4744 : mixedVector B (Sum.inr 4744) = Sparse.eval nodeValue4744 (mixedVector B) := by
    change mixedMoment B node4744 node4744Labels = _
    exact sound4744 B hB hF
  have h4778 : mixedVector B (Sum.inr 4778) = Sparse.eval nodeValue4778 (mixedVector B) := by
    change mixedMoment B node4778 node4778Labels = _
    exact sound4778 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4800 : mixedVector B (Sum.inr 4800) = Sparse.eval nodeValue4800 (mixedVector B) := by
    change mixedMoment B node4800 node4800Labels = _
    exact sound4800 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4827 : mixedVector B (Sum.inr 4827) = Sparse.eval nodeValue4827 (mixedVector B) := by
    change mixedMoment B node4827 node4827Labels = _
    exact sound4827 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  simpa only [sourceForm2088, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4081, h4286, h4289, h4294, h4302, h4320, h4324, h4338, h4398, h4426, h4630, h4636, h4643, h4658, h4673, h4708, h4720, h4728, h4738, h4741, h4744, h4778, h4779, h4788, h4800, h4804, h4827, h4837, h4841, h5075, reducedSource1743] using sourceEq2088 B hB

theorem rowSound1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1743 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1743, numericCheck1743, reducedZero1743 B hB hF, mul_zero]

theorem sourceRowsAt1728 : MixedData.sourceRows (1728 : Fin 2425) =
    MixedData.row1728 := by decide +kernel

theorem sourceRowsAt1729 : MixedData.sourceRows (1729 : Fin 2425) =
    MixedData.row1729 := by decide +kernel

theorem sourceRowsAt1730 : MixedData.sourceRows (1730 : Fin 2425) =
    MixedData.row1730 := by decide +kernel

theorem sourceRowsAt1731 : MixedData.sourceRows (1731 : Fin 2425) =
    MixedData.row1731 := by decide +kernel

theorem sourceRowsAt1732 : MixedData.sourceRows (1732 : Fin 2425) =
    MixedData.row1732 := by decide +kernel

theorem sourceRowsAt1733 : MixedData.sourceRows (1733 : Fin 2425) =
    MixedData.row1733 := by decide +kernel

theorem sourceRowsAt1734 : MixedData.sourceRows (1734 : Fin 2425) =
    MixedData.row1734 := by decide +kernel

theorem sourceRowsAt1735 : MixedData.sourceRows (1735 : Fin 2425) =
    MixedData.row1735 := by decide +kernel

theorem sourceRowsAt1736 : MixedData.sourceRows (1736 : Fin 2425) =
    MixedData.row1736 := by decide +kernel

theorem sourceRowsAt1737 : MixedData.sourceRows (1737 : Fin 2425) =
    MixedData.row1737 := by decide +kernel

theorem sourceRowsAt1738 : MixedData.sourceRows (1738 : Fin 2425) =
    MixedData.row1738 := by decide +kernel

theorem sourceRowsAt1739 : MixedData.sourceRows (1739 : Fin 2425) =
    MixedData.row1739 := by decide +kernel

theorem sourceRowsAt1740 : MixedData.sourceRows (1740 : Fin 2425) =
    MixedData.row1740 := by decide +kernel

theorem sourceRowsAt1741 : MixedData.sourceRows (1741 : Fin 2425) =
    MixedData.row1741 := by decide +kernel

theorem sourceRowsAt1742 : MixedData.sourceRows (1742 : Fin 2425) =
    MixedData.row1742 := by decide +kernel

theorem sourceRowsAt1743 : MixedData.sourceRows (1743 : Fin 2425) =
    MixedData.row1743 := by decide +kernel

theorem chunkSound108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 108) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1728 ∨ k.val = 1729 ∨ k.val = 1730 ∨ k.val = 1731 ∨ k.val = 1732 ∨ k.val = 1733 ∨ k.val = 1734 ∨ k.val = 1735 ∨ k.val = 1736 ∨ k.val = 1737 ∨ k.val = 1738 ∨ k.val = 1739 ∨ k.val = 1740 ∨ k.val = 1741 ∨ k.val = 1742 ∨ k.val = 1743 := by omega
  rcases heq with h1728 | h1729 | h1730 | h1731 | h1732 | h1733 | h1734 | h1735 | h1736 | h1737 | h1738 | h1739 | h1740 | h1741 | h1742 | h1743
  · have he : k = (1728 : Fin 2425) := Fin.ext h1728
    subst k
    rw [sourceRowsAt1728]
    exact rowSound1728 B hB hF
  · have he : k = (1729 : Fin 2425) := Fin.ext h1729
    subst k
    rw [sourceRowsAt1729]
    exact rowSound1729 B hB hF
  · have he : k = (1730 : Fin 2425) := Fin.ext h1730
    subst k
    rw [sourceRowsAt1730]
    exact rowSound1730 B hB hF
  · have he : k = (1731 : Fin 2425) := Fin.ext h1731
    subst k
    rw [sourceRowsAt1731]
    exact rowSound1731 B hB hF
  · have he : k = (1732 : Fin 2425) := Fin.ext h1732
    subst k
    rw [sourceRowsAt1732]
    exact rowSound1732 B hB hF
  · have he : k = (1733 : Fin 2425) := Fin.ext h1733
    subst k
    rw [sourceRowsAt1733]
    exact rowSound1733 B hB hF
  · have he : k = (1734 : Fin 2425) := Fin.ext h1734
    subst k
    rw [sourceRowsAt1734]
    exact rowSound1734 B hB hF
  · have he : k = (1735 : Fin 2425) := Fin.ext h1735
    subst k
    rw [sourceRowsAt1735]
    exact rowSound1735 B hB hF
  · have he : k = (1736 : Fin 2425) := Fin.ext h1736
    subst k
    rw [sourceRowsAt1736]
    exact rowSound1736 B hB hF
  · have he : k = (1737 : Fin 2425) := Fin.ext h1737
    subst k
    rw [sourceRowsAt1737]
    exact rowSound1737 B hB hF
  · have he : k = (1738 : Fin 2425) := Fin.ext h1738
    subst k
    rw [sourceRowsAt1738]
    exact rowSound1738 B hB hF
  · have he : k = (1739 : Fin 2425) := Fin.ext h1739
    subst k
    rw [sourceRowsAt1739]
    exact rowSound1739 B hB hF
  · have he : k = (1740 : Fin 2425) := Fin.ext h1740
    subst k
    rw [sourceRowsAt1740]
    exact rowSound1740 B hB hF
  · have he : k = (1741 : Fin 2425) := Fin.ext h1741
    subst k
    rw [sourceRowsAt1741]
    exact rowSound1741 B hB hF
  · have he : k = (1742 : Fin 2425) := Fin.ext h1742
    subst k
    rw [sourceRowsAt1742]
    exact rowSound1742 B hB hF
  · have he : k = (1743 : Fin 2425) := Fin.ext h1743
    subst k
    rw [sourceRowsAt1743]
    exact rowSound1743 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
