import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources73

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1888 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1888 (mixedVector B) = 0 := by
  have h2443 : mixedVector B (Sum.inr 2443) = Sparse.eval nodeValue2443 (mixedVector B) := by
    change mixedMoment B node2443 node2443Labels = _
    exact sound2443 B hB hF
  have h3033 : mixedVector B (Sum.inr 3033) = Sparse.eval nodeValue3033 (mixedVector B) := by
    change mixedMoment B node3033 node3033Labels = _
    exact sound3033 B hB hF
  have h3136 : mixedVector B (Sum.inr 3136) = Sparse.eval nodeValue3136 (mixedVector B) := by
    change mixedMoment B node3136 node3136Labels = _
    exact sound3136 B hB hF
  have h3138 : mixedVector B (Sum.inr 3138) = Sparse.eval nodeValue3138 (mixedVector B) := by
    change mixedMoment B node3138 node3138Labels = _
    exact sound3138 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2319, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2443, h3033, h3136, h3138, h3180, h3732, h4092, reducedSource1888] using sourceEq2319 B hB

theorem rowSound1888 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1888 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1888, numericCheck1888, reducedZero1888 B hB hF, mul_zero]

theorem reducedZero1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1889 (mixedVector B) = 0 := by
  have h942 : mixedVector B (Sum.inr 942) = Sparse.eval nodeValue942 (mixedVector B) := by
    change mixedMoment B node942 node942Labels = _
    exact sound942 B hB hF
  have h1822 : mixedVector B (Sum.inr 1822) = Sparse.eval nodeValue1822 (mixedVector B) := by
    change mixedMoment B node1822 node1822Labels = _
    exact sound1822 B hB hF
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2320, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h942, h1822, h2088, h2105, h2107, h4083, reducedSource1889] using sourceEq2320 B hB

theorem rowSound1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1889 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1889, numericCheck1889, reducedZero1889 B hB hF, mul_zero]

theorem reducedZero1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1890 (mixedVector B) = 0 := by
  have h2890 : mixedVector B (Sum.inr 2890) = Sparse.eval nodeValue2890 (mixedVector B) := by
    change mixedMoment B node2890 node2890Labels = _
    exact sound2890 B hB hF
  have h3135 : mixedVector B (Sum.inr 3135) = Sparse.eval nodeValue3135 (mixedVector B) := by
    change mixedMoment B node3135 node3135Labels = _
    exact sound3135 B hB hF
  have h3137 : mixedVector B (Sum.inr 3137) = Sparse.eval nodeValue3137 (mixedVector B) := by
    change mixedMoment B node3137 node3137Labels = _
    exact sound3137 B hB hF
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2321, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2890, h3135, h3137, h3172, h3721, h4091, reducedSource1890] using sourceEq2321 B hB

theorem rowSound1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1890 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1890, numericCheck1890, reducedZero1890 B hB hF, mul_zero]

theorem reducedZero1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1891 (mixedVector B) = 0 := by
  have h944 : mixedVector B (Sum.inr 944) = Sparse.eval nodeValue944 (mixedVector B) := by
    change mixedMoment B node944 node944Labels = _
    exact sound944 B hB hF
  have h1824 : mixedVector B (Sum.inr 1824) = Sparse.eval nodeValue1824 (mixedVector B) := by
    change mixedMoment B node1824 node1824Labels = _
    exact sound1824 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2322, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h944, h1824, h2089, h2105, h2110, h4083, reducedSource1891] using sourceEq2322 B hB

theorem rowSound1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1891 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1891, numericCheck1891, reducedZero1891 B hB hF, mul_zero]

theorem reducedZero1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1892 (mixedVector B) = 0 := by
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h3133 : mixedVector B (Sum.inr 3133) = Sparse.eval nodeValue3133 (mixedVector B) := by
    change mixedMoment B node3133 node3133Labels = _
    exact sound3133 B hB hF
  have h3134 : mixedVector B (Sum.inr 3134) = Sparse.eval nodeValue3134 (mixedVector B) := by
    change mixedMoment B node3134 node3134Labels = _
    exact sound3134 B hB hF
  have h3136 : mixedVector B (Sum.inr 3136) = Sparse.eval nodeValue3136 (mixedVector B) := by
    change mixedMoment B node3136 node3136Labels = _
    exact sound3136 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2323, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2423, h3133, h3134, h3136, h3170, h3719, h4092, reducedSource1892] using sourceEq2323 B hB

theorem rowSound1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1892 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1892, numericCheck1892, reducedZero1892 B hB hF, mul_zero]

theorem reducedZero1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1893 (mixedVector B) = 0 := by
  have h2899 : mixedVector B (Sum.inr 2899) = Sparse.eval nodeValue2899 (mixedVector B) := by
    change mixedMoment B node2899 node2899Labels = _
    exact sound2899 B hB hF
  have h3128 : mixedVector B (Sum.inr 3128) = Sparse.eval nodeValue3128 (mixedVector B) := by
    change mixedMoment B node3128 node3128Labels = _
    exact sound3128 B hB hF
  have h3132 : mixedVector B (Sum.inr 3132) = Sparse.eval nodeValue3132 (mixedVector B) := by
    change mixedMoment B node3132 node3132Labels = _
    exact sound3132 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3394 : mixedVector B (Sum.inr 3394) = Sparse.eval nodeValue3394 (mixedVector B) := by
    change mixedMoment B node3394 node3394Labels = _
    exact sound3394 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2325, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2899, h3128, h3132, h3158, h3394, h4083, reducedSource1893] using sourceEq2325 B hB

theorem rowSound1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1893 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1893, numericCheck1893, reducedZero1893 B hB hF, mul_zero]

theorem reducedZero1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1894 (mixedVector B) = 0 := by
  have h2435 : mixedVector B (Sum.inr 2435) = Sparse.eval nodeValue2435 (mixedVector B) := by
    change mixedMoment B node2435 node2435Labels = _
    exact sound2435 B hB hF
  have h3127 : mixedVector B (Sum.inr 3127) = Sparse.eval nodeValue3127 (mixedVector B) := by
    change mixedMoment B node3127 node3127Labels = _
    exact sound3127 B hB hF
  have h3129 : mixedVector B (Sum.inr 3129) = Sparse.eval nodeValue3129 (mixedVector B) := by
    change mixedMoment B node3129 node3129Labels = _
    exact sound3129 B hB hF
  have h3131 : mixedVector B (Sum.inr 3131) = Sparse.eval nodeValue3131 (mixedVector B) := by
    change mixedMoment B node3131 node3131Labels = _
    exact sound3131 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2326, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2435, h3127, h3129, h3131, h3156, h3391, h4084, reducedSource1894] using sourceEq2326 B hB

theorem rowSound1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1894 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1894, numericCheck1894, reducedZero1894 B hB hF, mul_zero]

theorem reducedZero1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1895 (mixedVector B) = 0 := by
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h2333 : mixedVector B (Sum.inr 2333) = Sparse.eval nodeValue2333 (mixedVector B) := by
    change mixedMoment B node2333 node2333Labels = _
    exact sound2333 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2327, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1130, h2333, h2481, h2494, h2508, h2515, h4092, reducedSource1895] using sourceEq2327 B hB

theorem rowSound1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1895 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1895, numericCheck1895, reducedZero1895 B hB hF, mul_zero]

theorem reducedZero1896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1896 (mixedVector B) = 0 := by
  have h2437 : mixedVector B (Sum.inr 2437) = Sparse.eval nodeValue2437 (mixedVector B) := by
    change mixedMoment B node2437 node2437Labels = _
    exact sound2437 B hB hF
  have h2900 : mixedVector B (Sum.inr 2900) = Sparse.eval nodeValue2900 (mixedVector B) := by
    change mixedMoment B node2900 node2900Labels = _
    exact sound2900 B hB hF
  have h2902 : mixedVector B (Sum.inr 2902) = Sparse.eval nodeValue2902 (mixedVector B) := by
    change mixedMoment B node2902 node2902Labels = _
    exact sound2902 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3787 : mixedVector B (Sum.inr 3787) = Sparse.eval nodeValue3787 (mixedVector B) := by
    change mixedMoment B node3787 node3787Labels = _
    exact sound3787 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2328, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2437, h2900, h2902, h2954, h2984, h3787, h4091, reducedSource1896] using sourceEq2328 B hB

theorem rowSound1896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1896 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1896, numericCheck1896, reducedZero1896 B hB hF, mul_zero]

theorem reducedZero1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1897 (mixedVector B) = 0 := by
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h2331 : mixedVector B (Sum.inr 2331) = Sparse.eval nodeValue2331 (mixedVector B) := by
    change mixedMoment B node2331 node2331Labels = _
    exact sound2331 B hB hF
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2330, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1127, h2331, h2493, h2508, h2512, h4092, reducedSource1897] using sourceEq2330 B hB

theorem rowSound1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1897 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1897, numericCheck1897, reducedZero1897 B hB hF, mul_zero]

theorem reducedZero1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1898 (mixedVector B) = 0 := by
  have h2847 : mixedVector B (Sum.inr 2847) = Sparse.eval nodeValue2847 (mixedVector B) := by
    change mixedMoment B node2847 node2847Labels = _
    exact sound2847 B hB hF
  have h2849 : mixedVector B (Sum.inr 2849) = Sparse.eval nodeValue2849 (mixedVector B) := by
    change mixedMoment B node2849 node2849Labels = _
    exact sound2849 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3945 : mixedVector B (Sum.inr 3945) = Sparse.eval nodeValue3945 (mixedVector B) := by
    change mixedMoment B node3945 node3945Labels = _
    exact sound3945 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2331, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2847, h2849, h2884, h2976, h3945, h4091, reducedSource1898] using sourceEq2331 B hB

theorem rowSound1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1898 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1898, numericCheck1898, reducedZero1898 B hB hF, mul_zero]

theorem reducedZero1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1899 (mixedVector B) = 0 := by
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2846 : mixedVector B (Sum.inr 2846) = Sparse.eval nodeValue2846 (mixedVector B) := by
    change mixedMoment B node2846 node2846Labels = _
    exact sound2846 B hB hF
  have h2848 : mixedVector B (Sum.inr 2848) = Sparse.eval nodeValue2848 (mixedVector B) := by
    change mixedMoment B node2848 node2848Labels = _
    exact sound2848 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2333, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2426, h2846, h2848, h2881, h2974, h3781, h4092, reducedSource1899] using sourceEq2333 B hB

theorem rowSound1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1899 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1899, numericCheck1899, reducedZero1899 B hB hF, mul_zero]

theorem reducedZero1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1900 (mixedVector B) = 0 := by
  have h1960 : mixedVector B (Sum.inr 1960) = Sparse.eval nodeValue1960 (mixedVector B) := by
    change mixedMoment B node1960 node1960Labels = _
    exact sound1960 B hB hF
  have h2427 : mixedVector B (Sum.inr 2427) = Sparse.eval nodeValue2427 (mixedVector B) := by
    change mixedMoment B node2427 node2427Labels = _
    exact sound2427 B hB hF
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h3493 : mixedVector B (Sum.inr 3493) = Sparse.eval nodeValue3493 (mixedVector B) := by
    change mixedMoment B node3493 node3493Labels = _
    exact sound3493 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2334, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1960, h2427, h2509, h2552, h3493, h4084, reducedSource1900] using sourceEq2334 B hB

theorem rowSound1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1900 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1900, numericCheck1900, reducedZero1900 B hB hF, mul_zero]

theorem reducedZero1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1901 (mixedVector B) = 0 := by
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2428 : mixedVector B (Sum.inr 2428) = Sparse.eval nodeValue2428 (mixedVector B) := by
    change mixedMoment B node2428 node2428Labels = _
    exact sound2428 B hB hF
  have h2433 : mixedVector B (Sum.inr 2433) = Sparse.eval nodeValue2433 (mixedVector B) := by
    change mixedMoment B node2433 node2433Labels = _
    exact sound2433 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2335, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2426, h2428, h2433, h2512, h2554, h3781, h4092, reducedSource1901] using sourceEq2335 B hB

theorem rowSound1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1901 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1901, numericCheck1901, reducedZero1901 B hB hF, mul_zero]

theorem reducedZero1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1902 (mixedVector B) = 0 := by
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2433 : mixedVector B (Sum.inr 2433) = Sparse.eval nodeValue2433 (mixedVector B) := by
    change mixedMoment B node2433 node2433Labels = _
    exact sound2433 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2336, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2430, h2431, h2433, h2515, h2557, h3782, h4092, reducedSource1902] using sourceEq2336 B hB

theorem rowSound1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1902 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1902, numericCheck1902, reducedZero1902 B hB hF, mul_zero]

theorem reducedZero1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1903 (mixedVector B) = 0 := by
  have h1335 : mixedVector B (Sum.inr 1335) = Sparse.eval nodeValue1335 (mixedVector B) := by
    change mixedMoment B node1335 node1335Labels = _
    exact sound1335 B hB hF
  have h2826 : mixedVector B (Sum.inr 2826) = Sparse.eval nodeValue2826 (mixedVector B) := by
    change mixedMoment B node2826 node2826Labels = _
    exact sound2826 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2337, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1335, h2826, h2924, h2933, h2951, h2954, h4091, reducedSource1903] using sourceEq2337 B hB

theorem rowSound1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1903 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1903, numericCheck1903, reducedZero1903 B hB hF, mul_zero]

theorem sourceRowsAt1888 : MixedData.sourceRows (1888 : Fin 2425) =
    MixedData.row1888 := by decide +kernel

theorem sourceRowsAt1889 : MixedData.sourceRows (1889 : Fin 2425) =
    MixedData.row1889 := by decide +kernel

theorem sourceRowsAt1890 : MixedData.sourceRows (1890 : Fin 2425) =
    MixedData.row1890 := by decide +kernel

theorem sourceRowsAt1891 : MixedData.sourceRows (1891 : Fin 2425) =
    MixedData.row1891 := by decide +kernel

theorem sourceRowsAt1892 : MixedData.sourceRows (1892 : Fin 2425) =
    MixedData.row1892 := by decide +kernel

theorem sourceRowsAt1893 : MixedData.sourceRows (1893 : Fin 2425) =
    MixedData.row1893 := by decide +kernel

theorem sourceRowsAt1894 : MixedData.sourceRows (1894 : Fin 2425) =
    MixedData.row1894 := by decide +kernel

theorem sourceRowsAt1895 : MixedData.sourceRows (1895 : Fin 2425) =
    MixedData.row1895 := by decide +kernel

theorem sourceRowsAt1896 : MixedData.sourceRows (1896 : Fin 2425) =
    MixedData.row1896 := by decide +kernel

theorem sourceRowsAt1897 : MixedData.sourceRows (1897 : Fin 2425) =
    MixedData.row1897 := by decide +kernel

theorem sourceRowsAt1898 : MixedData.sourceRows (1898 : Fin 2425) =
    MixedData.row1898 := by decide +kernel

theorem sourceRowsAt1899 : MixedData.sourceRows (1899 : Fin 2425) =
    MixedData.row1899 := by decide +kernel

theorem sourceRowsAt1900 : MixedData.sourceRows (1900 : Fin 2425) =
    MixedData.row1900 := by decide +kernel

theorem sourceRowsAt1901 : MixedData.sourceRows (1901 : Fin 2425) =
    MixedData.row1901 := by decide +kernel

theorem sourceRowsAt1902 : MixedData.sourceRows (1902 : Fin 2425) =
    MixedData.row1902 := by decide +kernel

theorem sourceRowsAt1903 : MixedData.sourceRows (1903 : Fin 2425) =
    MixedData.row1903 := by decide +kernel

theorem chunkSound118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 118) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1888 ∨ k.val = 1889 ∨ k.val = 1890 ∨ k.val = 1891 ∨ k.val = 1892 ∨ k.val = 1893 ∨ k.val = 1894 ∨ k.val = 1895 ∨ k.val = 1896 ∨ k.val = 1897 ∨ k.val = 1898 ∨ k.val = 1899 ∨ k.val = 1900 ∨ k.val = 1901 ∨ k.val = 1902 ∨ k.val = 1903 := by omega
  rcases heq with h1888 | h1889 | h1890 | h1891 | h1892 | h1893 | h1894 | h1895 | h1896 | h1897 | h1898 | h1899 | h1900 | h1901 | h1902 | h1903
  · have he : k = (1888 : Fin 2425) := Fin.ext h1888
    subst k
    rw [sourceRowsAt1888]
    exact rowSound1888 B hB hF
  · have he : k = (1889 : Fin 2425) := Fin.ext h1889
    subst k
    rw [sourceRowsAt1889]
    exact rowSound1889 B hB hF
  · have he : k = (1890 : Fin 2425) := Fin.ext h1890
    subst k
    rw [sourceRowsAt1890]
    exact rowSound1890 B hB hF
  · have he : k = (1891 : Fin 2425) := Fin.ext h1891
    subst k
    rw [sourceRowsAt1891]
    exact rowSound1891 B hB hF
  · have he : k = (1892 : Fin 2425) := Fin.ext h1892
    subst k
    rw [sourceRowsAt1892]
    exact rowSound1892 B hB hF
  · have he : k = (1893 : Fin 2425) := Fin.ext h1893
    subst k
    rw [sourceRowsAt1893]
    exact rowSound1893 B hB hF
  · have he : k = (1894 : Fin 2425) := Fin.ext h1894
    subst k
    rw [sourceRowsAt1894]
    exact rowSound1894 B hB hF
  · have he : k = (1895 : Fin 2425) := Fin.ext h1895
    subst k
    rw [sourceRowsAt1895]
    exact rowSound1895 B hB hF
  · have he : k = (1896 : Fin 2425) := Fin.ext h1896
    subst k
    rw [sourceRowsAt1896]
    exact rowSound1896 B hB hF
  · have he : k = (1897 : Fin 2425) := Fin.ext h1897
    subst k
    rw [sourceRowsAt1897]
    exact rowSound1897 B hB hF
  · have he : k = (1898 : Fin 2425) := Fin.ext h1898
    subst k
    rw [sourceRowsAt1898]
    exact rowSound1898 B hB hF
  · have he : k = (1899 : Fin 2425) := Fin.ext h1899
    subst k
    rw [sourceRowsAt1899]
    exact rowSound1899 B hB hF
  · have he : k = (1900 : Fin 2425) := Fin.ext h1900
    subst k
    rw [sourceRowsAt1900]
    exact rowSound1900 B hB hF
  · have he : k = (1901 : Fin 2425) := Fin.ext h1901
    subst k
    rw [sourceRowsAt1901]
    exact rowSound1901 B hB hF
  · have he : k = (1902 : Fin 2425) := Fin.ext h1902
    subst k
    rw [sourceRowsAt1902]
    exact rowSound1902 B hB hF
  · have he : k = (1903 : Fin 2425) := Fin.ext h1903
    subst k
    rw [sourceRowsAt1903]
    exact rowSound1903 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
