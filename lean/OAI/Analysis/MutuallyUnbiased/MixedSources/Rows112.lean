import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources67

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1792 (mixedVector B) = 0 := by
  have h1171 : mixedVector B (Sum.inr 1171) = Sparse.eval nodeValue1171 (mixedVector B) := by
    change mixedMoment B node1171 node1171Labels = _
    exact sound1171 B hB hF
  have h2362 : mixedVector B (Sum.inr 2362) = Sparse.eval nodeValue2362 (mixedVector B) := by
    change mixedMoment B node2362 node2362Labels = _
    exact sound2362 B hB hF
  have h2529 : mixedVector B (Sum.inr 2529) = Sparse.eval nodeValue2529 (mixedVector B) := by
    change mixedMoment B node2529 node2529Labels = _
    exact sound2529 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2147, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1171, h2362, h2529, h2575, h2590, h2600, h4092, reducedSource1792] using sourceEq2147 B hB

theorem rowSound1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1792 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1792, numericCheck1792, reducedZero1792 B hB hF, mul_zero]

theorem reducedZero1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1793 (mixedVector B) = 0 := by
  have h1812 : mixedVector B (Sum.inr 1812) = Sparse.eval nodeValue1812 (mixedVector B) := by
    change mixedMoment B node1812 node1812Labels = _
    exact sound1812 B hB hF
  have h2892 : mixedVector B (Sum.inr 2892) = Sparse.eval nodeValue2892 (mixedVector B) := by
    change mixedMoment B node2892 node2892Labels = _
    exact sound2892 B hB hF
  have h2899 : mixedVector B (Sum.inr 2899) = Sparse.eval nodeValue2899 (mixedVector B) := by
    change mixedMoment B node2899 node2899Labels = _
    exact sound2899 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h3394 : mixedVector B (Sum.inr 3394) = Sparse.eval nodeValue3394 (mixedVector B) := by
    change mixedMoment B node3394 node3394Labels = _
    exact sound3394 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2148, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1812, h2892, h2899, h2930, h3394, h4083, reducedSource1793] using sourceEq2148 B hB

theorem rowSound1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1793 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1793, numericCheck1793, reducedZero1793 B hB hF, mul_zero]

theorem reducedZero1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1794 (mixedVector B) = 0 := by
  have h2396 : mixedVector B (Sum.inr 2396) = Sparse.eval nodeValue2396 (mixedVector B) := by
    change mixedMoment B node2396 node2396Labels = _
    exact sound2396 B hB hF
  have h2399 : mixedVector B (Sum.inr 2399) = Sparse.eval nodeValue2399 (mixedVector B) := by
    change mixedMoment B node2399 node2399Labels = _
    exact sound2399 B hB hF
  have h2401 : mixedVector B (Sum.inr 2401) = Sparse.eval nodeValue2401 (mixedVector B) := by
    change mixedMoment B node2401 node2401Labels = _
    exact sound2401 B hB hF
  have h2405 : mixedVector B (Sum.inr 2405) = Sparse.eval nodeValue2405 (mixedVector B) := by
    change mixedMoment B node2405 node2405Labels = _
    exact sound2405 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2149, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2396, h2399, h2401, h2405, h2681, h3612, h4082, reducedSource1794] using sourceEq2149 B hB

theorem rowSound1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1794 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1794, numericCheck1794, reducedZero1794 B hB hF, mul_zero]

theorem reducedZero1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1795 (mixedVector B) = 0 := by
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4357 : mixedVector B (Sum.inr 4357) = Sparse.eval nodeValue4357 (mixedVector B) := by
    change mixedMoment B node4357 node4357Labels = _
    exact sound4357 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4930 : mixedVector B (Sum.inr 4930) = Sparse.eval nodeValue4930 (mixedVector B) := by
    change mixedMoment B node4930 node4930Labels = _
    exact sound4930 B hB hF
  have h4933 : mixedVector B (Sum.inr 4933) = Sparse.eval nodeValue4933 (mixedVector B) := by
    change mixedMoment B node4933 node4933Labels = _
    exact sound4933 B hB hF
  have h4934 : mixedVector B (Sum.inr 4934) = Sparse.eval nodeValue4934 (mixedVector B) := by
    change mixedMoment B node4934 node4934Labels = _
    exact sound4934 B hB hF
  have h4935 : mixedVector B (Sum.inr 4935) = Sparse.eval nodeValue4935 (mixedVector B) := by
    change mixedMoment B node4935 node4935Labels = _
    exact sound4935 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h4954 : mixedVector B (Sum.inr 4954) = Sparse.eval nodeValue4954 (mixedVector B) := by
    change mixedMoment B node4954 node4954Labels = _
    exact sound4954 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h5040 : mixedVector B (Sum.inr 5040) = Sparse.eval nodeValue5040 (mixedVector B) := by
    change mixedMoment B node5040 node5040Labels = _
    exact sound5040 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5117 : mixedVector B (Sum.inr 5117) = Sparse.eval nodeValue5117 (mixedVector B) := by
    change mixedMoment B node5117 node5117Labels = _
    exact sound5117 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm2152, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4332, h4334, h4335, h4357, h4444, h4930, h4933, h4934, h4935, h4948, h4951, h4954, h4970, h5040, h5067, h5078, h5117, h5145, h5147, h5149, h5152, h5164, h5170, h5282, h5284, h5352, h5356, h5369, h5410, h5473, reducedSource1795] using sourceEq2152 B hB

theorem rowSound1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1795 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1795, numericCheck1795, reducedZero1795 B hB hF, mul_zero]

theorem reducedZero1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1796 (mixedVector B) = 0 := by
  have h910 : mixedVector B (Sum.inr 910) = Sparse.eval nodeValue910 (mixedVector B) := by
    change mixedMoment B node910 node910Labels = _
    exact sound910 B hB hF
  have h912 : mixedVector B (Sum.inr 912) = Sparse.eval nodeValue912 (mixedVector B) := by
    change mixedMoment B node912 node912Labels = _
    exact sound912 B hB hF
  have h913 : mixedVector B (Sum.inr 913) = Sparse.eval nodeValue913 (mixedVector B) := by
    change mixedMoment B node913 node913Labels = _
    exact sound913 B hB hF
  have h935 : mixedVector B (Sum.inr 935) = Sparse.eval nodeValue935 (mixedVector B) := by
    change mixedMoment B node935 node935Labels = _
    exact sound935 B hB hF
  have h1026 : mixedVector B (Sum.inr 1026) = Sparse.eval nodeValue1026 (mixedVector B) := by
    change mixedMoment B node1026 node1026Labels = _
    exact sound1026 B hB hF
  have h2324 : mixedVector B (Sum.inr 2324) = Sparse.eval nodeValue2324 (mixedVector B) := by
    change mixedMoment B node2324 node2324Labels = _
    exact sound2324 B hB hF
  have h2325 : mixedVector B (Sum.inr 2325) = Sparse.eval nodeValue2325 (mixedVector B) := by
    change mixedMoment B node2325 node2325Labels = _
    exact sound2325 B hB hF
  have h2326 : mixedVector B (Sum.inr 2326) = Sparse.eval nodeValue2326 (mixedVector B) := by
    change mixedMoment B node2326 node2326Labels = _
    exact sound2326 B hB hF
  have h2343 : mixedVector B (Sum.inr 2343) = Sparse.eval nodeValue2343 (mixedVector B) := by
    change mixedMoment B node2343 node2343Labels = _
    exact sound2343 B hB hF
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2357 : mixedVector B (Sum.inr 2357) = Sparse.eval nodeValue2357 (mixedVector B) := by
    change mixedMoment B node2357 node2357Labels = _
    exact sound2357 B hB hF
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2433 : mixedVector B (Sum.inr 2433) = Sparse.eval nodeValue2433 (mixedVector B) := by
    change mixedMoment B node2433 node2433Labels = _
    exact sound2433 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2530 : mixedVector B (Sum.inr 2530) = Sparse.eval nodeValue2530 (mixedVector B) := by
    change mixedMoment B node2530 node2530Labels = _
    exact sound2530 B hB hF
  have h2531 : mixedVector B (Sum.inr 2531) = Sparse.eval nodeValue2531 (mixedVector B) := by
    change mixedMoment B node2531 node2531Labels = _
    exact sound2531 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2570 : mixedVector B (Sum.inr 2570) = Sparse.eval nodeValue2570 (mixedVector B) := by
    change mixedMoment B node2570 node2570Labels = _
    exact sound2570 B hB hF
  have h2572 : mixedVector B (Sum.inr 2572) = Sparse.eval nodeValue2572 (mixedVector B) := by
    change mixedMoment B node2572 node2572Labels = _
    exact sound2572 B hB hF
  have h2576 : mixedVector B (Sum.inr 2576) = Sparse.eval nodeValue2576 (mixedVector B) := by
    change mixedMoment B node2576 node2576Labels = _
    exact sound2576 B hB hF
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h2596 : mixedVector B (Sum.inr 2596) = Sparse.eval nodeValue2596 (mixedVector B) := by
    change mixedMoment B node2596 node2596Labels = _
    exact sound2596 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h3926 : mixedVector B (Sum.inr 3926) = Sparse.eval nodeValue3926 (mixedVector B) := by
    change mixedMoment B node3926 node3926Labels = _
    exact sound3926 B hB hF
  have h3936 : mixedVector B (Sum.inr 3936) = Sparse.eval nodeValue3936 (mixedVector B) := by
    change mixedMoment B node3936 node3936Labels = _
    exact sound3936 B hB hF
  have h3940 : mixedVector B (Sum.inr 3940) = Sparse.eval nodeValue3940 (mixedVector B) := by
    change mixedMoment B node3940 node3940Labels = _
    exact sound3940 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995 B hB hF
  have h3996 : mixedVector B (Sum.inr 3996) = Sparse.eval nodeValue3996 (mixedVector B) := by
    change mixedMoment B node3996 node3996Labels = _
    exact sound3996 B hB hF
  simpa only [sourceForm2153, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h910, h912, h913, h935, h1026, h2324, h2325, h2326, h2343, h2347, h2357, h2422, h2433, h2473, h2530, h2531, h2567, h2569, h2570, h2572, h2576, h2591, h2596, h2751, h2753, h3926, h3936, h3940, h3995, h3996, reducedSource1796] using sourceEq2153 B hB

theorem rowSound1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1796 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1796, numericCheck1796, reducedZero1796 B hB hF, mul_zero]

theorem reducedZero1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1797 (mixedVector B) = 0 := by
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h3408 : mixedVector B (Sum.inr 3408) = Sparse.eval nodeValue3408 (mixedVector B) := by
    change mixedMoment B node3408 node3408Labels = _
    exact sound3408 B hB hF
  have h3414 : mixedVector B (Sum.inr 3414) = Sparse.eval nodeValue3414 (mixedVector B) := by
    change mixedMoment B node3414 node3414Labels = _
    exact sound3414 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3419 : mixedVector B (Sum.inr 3419) = Sparse.eval nodeValue3419 (mixedVector B) := by
    change mixedMoment B node3419 node3419Labels = _
    exact sound3419 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3452 : mixedVector B (Sum.inr 3452) = Sparse.eval nodeValue3452 (mixedVector B) := by
    change mixedMoment B node3452 node3452Labels = _
    exact sound3452 B hB hF
  have h3454 : mixedVector B (Sum.inr 3454) = Sparse.eval nodeValue3454 (mixedVector B) := by
    change mixedMoment B node3454 node3454Labels = _
    exact sound3454 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3588 : mixedVector B (Sum.inr 3588) = Sparse.eval nodeValue3588 (mixedVector B) := by
    change mixedMoment B node3588 node3588Labels = _
    exact sound3588 B hB hF
  have h3599 : mixedVector B (Sum.inr 3599) = Sparse.eval nodeValue3599 (mixedVector B) := by
    change mixedMoment B node3599 node3599Labels = _
    exact sound3599 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3606 : mixedVector B (Sum.inr 3606) = Sparse.eval nodeValue3606 (mixedVector B) := by
    change mixedMoment B node3606 node3606Labels = _
    exact sound3606 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3764 : mixedVector B (Sum.inr 3764) = Sparse.eval nodeValue3764 (mixedVector B) := by
    change mixedMoment B node3764 node3764Labels = _
    exact sound3764 B hB hF
  have h3773 : mixedVector B (Sum.inr 3773) = Sparse.eval nodeValue3773 (mixedVector B) := by
    change mixedMoment B node3773 node3773Labels = _
    exact sound3773 B hB hF
  have h3774 : mixedVector B (Sum.inr 3774) = Sparse.eval nodeValue3774 (mixedVector B) := by
    change mixedMoment B node3774 node3774Labels = _
    exact sound3774 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  simpa only [sourceForm2154, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1678, h1679, h1682, h1689, h1736, h3408, h3414, h3415, h3418, h3419, h3420, h3452, h3454, h3476, h3481, h3530, h3562, h3565, h3580, h3588, h3599, h3605, h3606, h3612, h3625, h3764, h3773, h3774, h3816, h3961, reducedSource1797] using sourceEq2154 B hB

theorem rowSound1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1797 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1797, numericCheck1797, reducedZero1797 B hB hF, mul_zero]

theorem reducedZero1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1798 (mixedVector B) = 0 := by
  have h2326 : mixedVector B (Sum.inr 2326) = Sparse.eval nodeValue2326 (mixedVector B) := by
    change mixedMoment B node2326 node2326Labels = _
    exact sound2326 B hB hF
  have h2802 : mixedVector B (Sum.inr 2802) = Sparse.eval nodeValue2802 (mixedVector B) := by
    change mixedMoment B node2802 node2802Labels = _
    exact sound2802 B hB hF
  have h2822 : mixedVector B (Sum.inr 2822) = Sparse.eval nodeValue2822 (mixedVector B) := by
    change mixedMoment B node2822 node2822Labels = _
    exact sound2822 B hB hF
  have h2827 : mixedVector B (Sum.inr 2827) = Sparse.eval nodeValue2827 (mixedVector B) := by
    change mixedMoment B node2827 node2827Labels = _
    exact sound2827 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h3694 : mixedVector B (Sum.inr 3694) = Sparse.eval nodeValue3694 (mixedVector B) := by
    change mixedMoment B node3694 node3694Labels = _
    exact sound3694 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2155, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2326, h2802, h2822, h2827, h2931, h3694, h4091, reducedSource1798] using sourceEq2155 B hB

theorem rowSound1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1798 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1798, numericCheck1798, reducedZero1798 B hB hF, mul_zero]

theorem reducedZero1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1799 (mixedVector B) = 0 := by
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h2822 : mixedVector B (Sum.inr 2822) = Sparse.eval nodeValue2822 (mixedVector B) := by
    change mixedMoment B node2822 node2822Labels = _
    exact sound2822 B hB hF
  have h2893 : mixedVector B (Sum.inr 2893) = Sparse.eval nodeValue2893 (mixedVector B) := by
    change mixedMoment B node2893 node2893Labels = _
    exact sound2893 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2156, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1328, h2822, h2893, h2924, h2925, h2931, h4091, reducedSource1799] using sourceEq2156 B hB

theorem rowSound1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1799 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1799, numericCheck1799, reducedZero1799 B hB hF, mul_zero]

theorem reducedZero1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1800 (mixedVector B) = 0 := by
  have h1338 : mixedVector B (Sum.inr 1338) = Sparse.eval nodeValue1338 (mixedVector B) := by
    change mixedMoment B node1338 node1338Labels = _
    exact sound1338 B hB hF
  have h2827 : mixedVector B (Sum.inr 2827) = Sparse.eval nodeValue2827 (mixedVector B) := by
    change mixedMoment B node2827 node2827Labels = _
    exact sound2827 B hB hF
  have h2900 : mixedVector B (Sum.inr 2900) = Sparse.eval nodeValue2900 (mixedVector B) := by
    change mixedMoment B node2900 node2900Labels = _
    exact sound2900 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2157, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1338, h2827, h2900, h2931, h2954, h2955, h4091, reducedSource1800] using sourceEq2157 B hB

theorem rowSound1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1800 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1800, numericCheck1800, reducedZero1800 B hB hF, mul_zero]

theorem reducedZero1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1801 (mixedVector B) = 0 := by
  have h2399 : mixedVector B (Sum.inr 2399) = Sparse.eval nodeValue2399 (mixedVector B) := by
    change mixedMoment B node2399 node2399Labels = _
    exact sound2399 B hB hF
  have h3433 : mixedVector B (Sum.inr 3433) = Sparse.eval nodeValue3433 (mixedVector B) := by
    change mixedMoment B node3433 node3433Labels = _
    exact sound3433 B hB hF
  have h3439 : mixedVector B (Sum.inr 3439) = Sparse.eval nodeValue3439 (mixedVector B) := by
    change mixedMoment B node3439 node3439Labels = _
    exact sound3439 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2160, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2399, h3433, h3439, h3485, h3522, h3612, h4082, reducedSource1801] using sourceEq2160 B hB

theorem rowSound1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1801 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1801, numericCheck1801, reducedZero1801 B hB hF, mul_zero]

theorem reducedZero1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1802 (mixedVector B) = 0 := by
  have h2910 : mixedVector B (Sum.inr 2910) = Sparse.eval nodeValue2910 (mixedVector B) := by
    change mixedMoment B node2910 node2910Labels = _
    exact sound2910 B hB hF
  have h3346 : mixedVector B (Sum.inr 3346) = Sparse.eval nodeValue3346 (mixedVector B) := by
    change mixedMoment B node3346 node3346Labels = _
    exact sound3346 B hB hF
  have h3349 : mixedVector B (Sum.inr 3349) = Sparse.eval nodeValue3349 (mixedVector B) := by
    change mixedMoment B node3349 node3349Labels = _
    exact sound3349 B hB hF
  have h3357 : mixedVector B (Sum.inr 3357) = Sparse.eval nodeValue3357 (mixedVector B) := by
    change mixedMoment B node3357 node3357Labels = _
    exact sound3357 B hB hF
  have h3479 : mixedVector B (Sum.inr 3479) = Sparse.eval nodeValue3479 (mixedVector B) := by
    change mixedMoment B node3479 node3479Labels = _
    exact sound3479 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2161, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2910, h3346, h3349, h3357, h3479, h3570, h4080, reducedSource1802] using sourceEq2161 B hB

theorem rowSound1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1802 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1802, numericCheck1802, reducedZero1802 B hB hF, mul_zero]

theorem reducedZero1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1803 (mixedVector B) = 0 := by
  have h2355 : mixedVector B (Sum.inr 2355) = Sparse.eval nodeValue2355 (mixedVector B) := by
    change mixedMoment B node2355 node2355Labels = _
    exact sound2355 B hB hF
  have h2438 : mixedVector B (Sum.inr 2438) = Sparse.eval nodeValue2438 (mixedVector B) := by
    change mixedMoment B node2438 node2438Labels = _
    exact sound2438 B hB hF
  have h2443 : mixedVector B (Sum.inr 2443) = Sparse.eval nodeValue2443 (mixedVector B) := by
    change mixedMoment B node2443 node2443Labels = _
    exact sound2443 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2168, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2355, h2438, h2443, h2488, h2620, h3732, h4092, reducedSource1803] using sourceEq2168 B hB

theorem rowSound1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1803 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1803, numericCheck1803, reducedZero1803 B hB hF, mul_zero]

theorem reducedZero1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1804 (mixedVector B) = 0 := by
  have h2352 : mixedVector B (Sum.inr 2352) = Sparse.eval nodeValue2352 (mixedVector B) := by
    change mixedMoment B node2352 node2352Labels = _
    exact sound2352 B hB hF
  have h2798 : mixedVector B (Sum.inr 2798) = Sparse.eval nodeValue2798 (mixedVector B) := by
    change mixedMoment B node2798 node2798Labels = _
    exact sound2798 B hB hF
  have h2803 : mixedVector B (Sum.inr 2803) = Sparse.eval nodeValue2803 (mixedVector B) := by
    change mixedMoment B node2803 node2803Labels = _
    exact sound2803 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2169, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2352, h2798, h2803, h2817, h2867, h3693, h4092, reducedSource1804] using sourceEq2169 B hB

theorem rowSound1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1804 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1804, numericCheck1804, reducedZero1804 B hB hF, mul_zero]

theorem reducedZero1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1805 (mixedVector B) = 0 := by
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2848 : mixedVector B (Sum.inr 2848) = Sparse.eval nodeValue2848 (mixedVector B) := by
    change mixedMoment B node2848 node2848Labels = _
    exact sound2848 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2170, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1321, h2817, h2848, h2867, h2881, h2885, h4092, reducedSource1805] using sourceEq2170 B hB

theorem rowSound1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1805 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1805, numericCheck1805, reducedZero1805 B hB hF, mul_zero]

theorem reducedZero1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1806 (mixedVector B) = 0 := by
  have h2538 : mixedVector B (Sum.inr 2538) = Sparse.eval nodeValue2538 (mixedVector B) := by
    change mixedMoment B node2538 node2538Labels = _
    exact sound2538 B hB hF
  have h3345 : mixedVector B (Sum.inr 3345) = Sparse.eval nodeValue3345 (mixedVector B) := by
    change mixedMoment B node3345 node3345Labels = _
    exact sound3345 B hB hF
  have h3348 : mixedVector B (Sum.inr 3348) = Sparse.eval nodeValue3348 (mixedVector B) := by
    change mixedMoment B node3348 node3348Labels = _
    exact sound3348 B hB hF
  have h3354 : mixedVector B (Sum.inr 3354) = Sparse.eval nodeValue3354 (mixedVector B) := by
    change mixedMoment B node3354 node3354Labels = _
    exact sound3354 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2171, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2538, h3345, h3348, h3354, h3478, h3538, h4082, reducedSource1806] using sourceEq2171 B hB

theorem rowSound1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1806 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1806, numericCheck1806, reducedZero1806 B hB hF, mul_zero]

theorem reducedZero1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1807 (mixedVector B) = 0 := by
  have h2048 : mixedVector B (Sum.inr 2048) = Sparse.eval nodeValue2048 (mixedVector B) := by
    change mixedMoment B node2048 node2048Labels = _
    exact sound2048 B hB hF
  have h3386 : mixedVector B (Sum.inr 3386) = Sparse.eval nodeValue3386 (mixedVector B) := by
    change mixedMoment B node3386 node3386Labels = _
    exact sound3386 B hB hF
  have h3491 : mixedVector B (Sum.inr 3491) = Sparse.eval nodeValue3491 (mixedVector B) := by
    change mixedMoment B node3491 node3491Labels = _
    exact sound3491 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2172, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2048, h3386, h3491, h3522, h3538, h3542, h4082, reducedSource1807] using sourceEq2172 B hB

theorem rowSound1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1807 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1807, numericCheck1807, reducedZero1807 B hB hF, mul_zero]

theorem sourceRowsAt1792 : MixedData.sourceRows (1792 : Fin 2425) =
    MixedData.row1792 := by decide +kernel

theorem sourceRowsAt1793 : MixedData.sourceRows (1793 : Fin 2425) =
    MixedData.row1793 := by decide +kernel

theorem sourceRowsAt1794 : MixedData.sourceRows (1794 : Fin 2425) =
    MixedData.row1794 := by decide +kernel

theorem sourceRowsAt1795 : MixedData.sourceRows (1795 : Fin 2425) =
    MixedData.row1795 := by decide +kernel

theorem sourceRowsAt1796 : MixedData.sourceRows (1796 : Fin 2425) =
    MixedData.row1796 := by decide +kernel

theorem sourceRowsAt1797 : MixedData.sourceRows (1797 : Fin 2425) =
    MixedData.row1797 := by decide +kernel

theorem sourceRowsAt1798 : MixedData.sourceRows (1798 : Fin 2425) =
    MixedData.row1798 := by decide +kernel

theorem sourceRowsAt1799 : MixedData.sourceRows (1799 : Fin 2425) =
    MixedData.row1799 := by decide +kernel

theorem sourceRowsAt1800 : MixedData.sourceRows (1800 : Fin 2425) =
    MixedData.row1800 := by decide +kernel

theorem sourceRowsAt1801 : MixedData.sourceRows (1801 : Fin 2425) =
    MixedData.row1801 := by decide +kernel

theorem sourceRowsAt1802 : MixedData.sourceRows (1802 : Fin 2425) =
    MixedData.row1802 := by decide +kernel

theorem sourceRowsAt1803 : MixedData.sourceRows (1803 : Fin 2425) =
    MixedData.row1803 := by decide +kernel

theorem sourceRowsAt1804 : MixedData.sourceRows (1804 : Fin 2425) =
    MixedData.row1804 := by decide +kernel

theorem sourceRowsAt1805 : MixedData.sourceRows (1805 : Fin 2425) =
    MixedData.row1805 := by decide +kernel

theorem sourceRowsAt1806 : MixedData.sourceRows (1806 : Fin 2425) =
    MixedData.row1806 := by decide +kernel

theorem sourceRowsAt1807 : MixedData.sourceRows (1807 : Fin 2425) =
    MixedData.row1807 := by decide +kernel

theorem chunkSound112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 112) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1792 ∨ k.val = 1793 ∨ k.val = 1794 ∨ k.val = 1795 ∨ k.val = 1796 ∨ k.val = 1797 ∨ k.val = 1798 ∨ k.val = 1799 ∨ k.val = 1800 ∨ k.val = 1801 ∨ k.val = 1802 ∨ k.val = 1803 ∨ k.val = 1804 ∨ k.val = 1805 ∨ k.val = 1806 ∨ k.val = 1807 := by omega
  rcases heq with h1792 | h1793 | h1794 | h1795 | h1796 | h1797 | h1798 | h1799 | h1800 | h1801 | h1802 | h1803 | h1804 | h1805 | h1806 | h1807
  · have he : k = (1792 : Fin 2425) := Fin.ext h1792
    subst k
    rw [sourceRowsAt1792]
    exact rowSound1792 B hB hF
  · have he : k = (1793 : Fin 2425) := Fin.ext h1793
    subst k
    rw [sourceRowsAt1793]
    exact rowSound1793 B hB hF
  · have he : k = (1794 : Fin 2425) := Fin.ext h1794
    subst k
    rw [sourceRowsAt1794]
    exact rowSound1794 B hB hF
  · have he : k = (1795 : Fin 2425) := Fin.ext h1795
    subst k
    rw [sourceRowsAt1795]
    exact rowSound1795 B hB hF
  · have he : k = (1796 : Fin 2425) := Fin.ext h1796
    subst k
    rw [sourceRowsAt1796]
    exact rowSound1796 B hB hF
  · have he : k = (1797 : Fin 2425) := Fin.ext h1797
    subst k
    rw [sourceRowsAt1797]
    exact rowSound1797 B hB hF
  · have he : k = (1798 : Fin 2425) := Fin.ext h1798
    subst k
    rw [sourceRowsAt1798]
    exact rowSound1798 B hB hF
  · have he : k = (1799 : Fin 2425) := Fin.ext h1799
    subst k
    rw [sourceRowsAt1799]
    exact rowSound1799 B hB hF
  · have he : k = (1800 : Fin 2425) := Fin.ext h1800
    subst k
    rw [sourceRowsAt1800]
    exact rowSound1800 B hB hF
  · have he : k = (1801 : Fin 2425) := Fin.ext h1801
    subst k
    rw [sourceRowsAt1801]
    exact rowSound1801 B hB hF
  · have he : k = (1802 : Fin 2425) := Fin.ext h1802
    subst k
    rw [sourceRowsAt1802]
    exact rowSound1802 B hB hF
  · have he : k = (1803 : Fin 2425) := Fin.ext h1803
    subst k
    rw [sourceRowsAt1803]
    exact rowSound1803 B hB hF
  · have he : k = (1804 : Fin 2425) := Fin.ext h1804
    subst k
    rw [sourceRowsAt1804]
    exact rowSound1804 B hB hF
  · have he : k = (1805 : Fin 2425) := Fin.ext h1805
    subst k
    rw [sourceRowsAt1805]
    exact rowSound1805 B hB hF
  · have he : k = (1806 : Fin 2425) := Fin.ext h1806
    subst k
    rw [sourceRowsAt1806]
    exact rowSound1806 B hB hF
  · have he : k = (1807 : Fin 2425) := Fin.ext h1807
    subst k
    rw [sourceRowsAt1807]
    exact rowSound1807 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
