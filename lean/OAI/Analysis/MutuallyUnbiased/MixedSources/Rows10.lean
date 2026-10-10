import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources6

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource160 (mixedVector B) = 0 := by
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm182, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1042, h2021, h2108, h2253, h2262, h2266, h4084, reducedSource160] using sourceEq182 B hB

theorem rowSound160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row160 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck160, numericCheck160, reducedZero160 B hB hF, mul_zero]

theorem reducedZero161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource161 (mixedVector B) = 0 := by
  have h2124 : mixedVector B (Sum.inr 2124) = Sparse.eval nodeValue2124 (mixedVector B) := by
    change mixedMoment B node2124 node2124Labels = _
    exact sound2124 B hB hF
  have h2125 : mixedVector B (Sum.inr 2125) = Sparse.eval nodeValue2125 (mixedVector B) := by
    change mixedMoment B node2125 node2125Labels = _
    exact sound2125 B hB hF
  have h2126 : mixedVector B (Sum.inr 2126) = Sparse.eval nodeValue2126 (mixedVector B) := by
    change mixedMoment B node2126 node2126Labels = _
    exact sound2126 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm183, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2124, h2125, h2126, h2133, h2253, h2513, h4084, reducedSource161] using sourceEq183 B hB

theorem rowSound161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row161 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck161, numericCheck161, reducedZero161 B hB hF, mul_zero]

theorem reducedZero162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource162 (mixedVector B) = 0 := by
  have h1030 : mixedVector B (Sum.inr 1030) = Sparse.eval nodeValue1030 (mixedVector B) := by
    change mixedMoment B node1030 node1030Labels = _
    exact sound1030 B hB hF
  have h2014 : mixedVector B (Sum.inr 2014) = Sparse.eval nodeValue2014 (mixedVector B) := by
    change mixedMoment B node2014 node2014Labels = _
    exact sound2014 B hB hF
  have h2097 : mixedVector B (Sum.inr 2097) = Sparse.eval nodeValue2097 (mixedVector B) := by
    change mixedMoment B node2097 node2097Labels = _
    exact sound2097 B hB hF
  have h2126 : mixedVector B (Sum.inr 2126) = Sparse.eval nodeValue2126 (mixedVector B) := by
    change mixedMoment B node2126 node2126Labels = _
    exact sound2126 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm184, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1030, h2014, h2097, h2126, h2253, h4084, reducedSource162] using sourceEq184 B hB

theorem rowSound162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row162 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck162, numericCheck162, reducedZero162 B hB hF, mul_zero]

theorem reducedZero163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource163 (mixedVector B) = 0 := by
  have h793 : mixedVector B (Sum.inr 793) = Sparse.eval nodeValue793 (mixedVector B) := by
    change mixedMoment B node793 node793Labels = _
    exact sound793 B hB hF
  have h794 : mixedVector B (Sum.inr 794) = Sparse.eval nodeValue794 (mixedVector B) := by
    change mixedMoment B node794 node794Labels = _
    exact sound794 B hB hF
  have h796 : mixedVector B (Sum.inr 796) = Sparse.eval nodeValue796 (mixedVector B) := by
    change mixedMoment B node796 node796Labels = _
    exact sound796 B hB hF
  have h808 : mixedVector B (Sum.inr 808) = Sparse.eval nodeValue808 (mixedVector B) := by
    change mixedMoment B node808 node808Labels = _
    exact sound808 B hB hF
  have h825 : mixedVector B (Sum.inr 825) = Sparse.eval nodeValue825 (mixedVector B) := by
    change mixedMoment B node825 node825Labels = _
    exact sound825 B hB hF
  have h1902 : mixedVector B (Sum.inr 1902) = Sparse.eval nodeValue1902 (mixedVector B) := by
    change mixedMoment B node1902 node1902Labels = _
    exact sound1902 B hB hF
  have h1904 : mixedVector B (Sum.inr 1904) = Sparse.eval nodeValue1904 (mixedVector B) := by
    change mixedMoment B node1904 node1904Labels = _
    exact sound1904 B hB hF
  have h1910 : mixedVector B (Sum.inr 1910) = Sparse.eval nodeValue1910 (mixedVector B) := by
    change mixedMoment B node1910 node1910Labels = _
    exact sound1910 B hB hF
  have h1923 : mixedVector B (Sum.inr 1923) = Sparse.eval nodeValue1923 (mixedVector B) := by
    change mixedMoment B node1923 node1923Labels = _
    exact sound1923 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3856 : mixedVector B (Sum.inr 3856) = Sparse.eval nodeValue3856 (mixedVector B) := by
    change mixedMoment B node3856 node3856Labels = _
    exact sound3856 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  simpa only [sourceForm186, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h793, h794, h796, h808, h825, h1902, h1904, h1910, h1923, h2034, h2035, h2039, h2055, h2089, h2090, h2094, h2108, h2196, h2197, h2207, h2217, h2250, h2251, h2259, h2274, h3803, h3813, h3814, h3856, h3883, reducedSource163] using sourceEq186 B hB

theorem rowSound163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row163 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck163, numericCheck163, reducedZero163 B hB hF, mul_zero]

theorem reducedZero164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource164 (mixedVector B) = 0 := by
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm187, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3222, h3803, h3809, h3814, h4092, reducedSource164] using sourceEq187 B hB

theorem rowSound164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row164 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck164, numericCheck164, reducedZero164 B hB hF, mul_zero]

theorem reducedZero165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource165 (mixedVector B) = 0 := by
  have h1463 : mixedVector B (Sum.inr 1463) = Sparse.eval nodeValue1463 (mixedVector B) := by
    change mixedMoment B node1463 node1463Labels = _
    exact sound1463 B hB hF
  have h1465 : mixedVector B (Sum.inr 1465) = Sparse.eval nodeValue1465 (mixedVector B) := by
    change mixedMoment B node1465 node1465Labels = _
    exact sound1465 B hB hF
  have h1466 : mixedVector B (Sum.inr 1466) = Sparse.eval nodeValue1466 (mixedVector B) := by
    change mixedMoment B node1466 node1466Labels = _
    exact sound1466 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm188, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1463, h1465, h1466, h3222, h4092, reducedSource165] using sourceEq188 B hB

theorem rowSound165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row165 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck165, numericCheck165, reducedZero165 B hB hF, mul_zero]

theorem reducedZero166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource166 (mixedVector B) = 0 := by
  have h1463 : mixedVector B (Sum.inr 1463) = Sparse.eval nodeValue1463 (mixedVector B) := by
    change mixedMoment B node1463 node1463Labels = _
    exact sound1463 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm189, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1463, h3170, h3196, h3222, h4092, reducedSource166] using sourceEq189 B hB

theorem rowSound166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row166 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck166, numericCheck166, reducedZero166 B hB hF, mul_zero]

theorem reducedZero167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource167 (mixedVector B) = 0 := by
  have h2474 : mixedVector B (Sum.inr 2474) = Sparse.eval nodeValue2474 (mixedVector B) := by
    change mixedMoment B node2474 node2474Labels = _
    exact sound2474 B hB hF
  have h3217 : mixedVector B (Sum.inr 3217) = Sparse.eval nodeValue3217 (mixedVector B) := by
    change mixedMoment B node3217 node3217Labels = _
    exact sound3217 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm190, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2474, h3217, h3222, h3803, h4092, reducedSource167] using sourceEq190 B hB

theorem rowSound167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row167 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck167, numericCheck167, reducedZero167 B hB hF, mul_zero]

theorem reducedZero168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource168 (mixedVector B) = 0 := by
  have h1466 : mixedVector B (Sum.inr 1466) = Sparse.eval nodeValue1466 (mixedVector B) := by
    change mixedMoment B node1466 node1466Labels = _
    exact sound1466 B hB hF
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3217 : mixedVector B (Sum.inr 3217) = Sparse.eval nodeValue3217 (mixedVector B) := by
    change mixedMoment B node3217 node3217Labels = _
    exact sound3217 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm191, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1466, h3174, h3180, h3198, h3217, h3222, h4092, reducedSource168] using sourceEq191 B hB

theorem rowSound168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row168 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck168, numericCheck168, reducedZero168 B hB hF, mul_zero]

theorem reducedZero169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource169 (mixedVector B) = 0 := by
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm192, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2497, h2716, h3196, h3198, h3222, h3814, h4092, reducedSource169] using sourceEq192 B hB

theorem rowSound169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row169 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck169, numericCheck169, reducedZero169 B hB hF, mul_zero]

theorem reducedZero170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource170 (mixedVector B) = 0 := by
  have h1465 : mixedVector B (Sum.inr 1465) = Sparse.eval nodeValue1465 (mixedVector B) := by
    change mixedMoment B node1465 node1465Labels = _
    exact sound1465 B hB hF
  have h2474 : mixedVector B (Sum.inr 2474) = Sparse.eval nodeValue2474 (mixedVector B) := by
    change mixedMoment B node2474 node2474Labels = _
    exact sound2474 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm193, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1465, h2474, h2486, h2497, h2716, h3222, h4092, reducedSource170] using sourceEq193 B hB

theorem rowSound170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row170 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck170, numericCheck170, reducedZero170 B hB hF, mul_zero]

theorem reducedZero171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource171 (mixedVector B) = 0 := by
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3618 : mixedVector B (Sum.inr 3618) = Sparse.eval nodeValue3618 (mixedVector B) := by
    change mixedMoment B node3618 node3618Labels = _
    exact sound3618 B hB hF
  have h3619 : mixedVector B (Sum.inr 3619) = Sparse.eval nodeValue3619 (mixedVector B) := by
    change mixedMoment B node3619 node3619Labels = _
    exact sound3619 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm197, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2233, h3567, h3618, h3619, h4083, reducedSource171] using sourceEq197 B hB

theorem rowSound171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row171 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck171, numericCheck171, reducedZero171 B hB hF, mul_zero]

theorem reducedZero172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource172 (mixedVector B) = 0 := by
  have h1014 : mixedVector B (Sum.inr 1014) = Sparse.eval nodeValue1014 (mixedVector B) := by
    change mixedMoment B node1014 node1014Labels = _
    exact sound1014 B hB hF
  have h1015 : mixedVector B (Sum.inr 1015) = Sparse.eval nodeValue1015 (mixedVector B) := by
    change mixedMoment B node1015 node1015Labels = _
    exact sound1015 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm198, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1014, h1015, h1021, h2233, h4083, reducedSource172] using sourceEq198 B hB

theorem rowSound172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row172 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck172, numericCheck172, reducedZero172 B hB hF, mul_zero]

theorem reducedZero173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource173 (mixedVector B) = 0 := by
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm199, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1021, h2089, h2233, h2243, h2245, h4083, reducedSource173] using sourceEq199 B hB

theorem rowSound173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row173 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck173, numericCheck173, reducedZero173 B hB hF, mul_zero]

theorem reducedZero174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource174 (mixedVector B) = 0 := by
  have h2083 : mixedVector B (Sum.inr 2083) = Sparse.eval nodeValue2083 (mixedVector B) := by
    change mixedMoment B node2083 node2083Labels = _
    exact sound2083 B hB hF
  have h2084 : mixedVector B (Sum.inr 2084) = Sparse.eval nodeValue2084 (mixedVector B) := by
    change mixedMoment B node2084 node2084Labels = _
    exact sound2084 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm200, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2083, h2084, h2089, h2233, h3567, h4083, reducedSource174] using sourceEq200 B hB

theorem rowSound174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row174 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck174, numericCheck174, reducedZero174 B hB hF, mul_zero]

theorem reducedZero175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource175 (mixedVector B) = 0 := by
  have h1015 : mixedVector B (Sum.inr 1015) = Sparse.eval nodeValue1015 (mixedVector B) := by
    change mixedMoment B node1015 node1015Labels = _
    exact sound1015 B hB hF
  have h2084 : mixedVector B (Sum.inr 2084) = Sparse.eval nodeValue2084 (mixedVector B) := by
    change mixedMoment B node2084 node2084Labels = _
    exact sound2084 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm201, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1015, h2084, h2233, h4083, reducedSource175] using sourceEq201 B hB

theorem rowSound175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row175 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck175, numericCheck175, reducedZero175 B hB hF, mul_zero]

theorem sourceRowsAt160 : MixedData.sourceRows (160 : Fin 2425) =
    MixedData.row160 := by decide +kernel

theorem sourceRowsAt161 : MixedData.sourceRows (161 : Fin 2425) =
    MixedData.row161 := by decide +kernel

theorem sourceRowsAt162 : MixedData.sourceRows (162 : Fin 2425) =
    MixedData.row162 := by decide +kernel

theorem sourceRowsAt163 : MixedData.sourceRows (163 : Fin 2425) =
    MixedData.row163 := by decide +kernel

theorem sourceRowsAt164 : MixedData.sourceRows (164 : Fin 2425) =
    MixedData.row164 := by decide +kernel

theorem sourceRowsAt165 : MixedData.sourceRows (165 : Fin 2425) =
    MixedData.row165 := by decide +kernel

theorem sourceRowsAt166 : MixedData.sourceRows (166 : Fin 2425) =
    MixedData.row166 := by decide +kernel

theorem sourceRowsAt167 : MixedData.sourceRows (167 : Fin 2425) =
    MixedData.row167 := by decide +kernel

theorem sourceRowsAt168 : MixedData.sourceRows (168 : Fin 2425) =
    MixedData.row168 := by decide +kernel

theorem sourceRowsAt169 : MixedData.sourceRows (169 : Fin 2425) =
    MixedData.row169 := by decide +kernel

theorem sourceRowsAt170 : MixedData.sourceRows (170 : Fin 2425) =
    MixedData.row170 := by decide +kernel

theorem sourceRowsAt171 : MixedData.sourceRows (171 : Fin 2425) =
    MixedData.row171 := by decide +kernel

theorem sourceRowsAt172 : MixedData.sourceRows (172 : Fin 2425) =
    MixedData.row172 := by decide +kernel

theorem sourceRowsAt173 : MixedData.sourceRows (173 : Fin 2425) =
    MixedData.row173 := by decide +kernel

theorem sourceRowsAt174 : MixedData.sourceRows (174 : Fin 2425) =
    MixedData.row174 := by decide +kernel

theorem sourceRowsAt175 : MixedData.sourceRows (175 : Fin 2425) =
    MixedData.row175 := by decide +kernel

theorem chunkSound10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 10) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 160 ∨ k.val = 161 ∨ k.val = 162 ∨ k.val = 163 ∨ k.val = 164 ∨ k.val = 165 ∨ k.val = 166 ∨ k.val = 167 ∨ k.val = 168 ∨ k.val = 169 ∨ k.val = 170 ∨ k.val = 171 ∨ k.val = 172 ∨ k.val = 173 ∨ k.val = 174 ∨ k.val = 175 := by omega
  rcases heq with h160 | h161 | h162 | h163 | h164 | h165 | h166 | h167 | h168 | h169 | h170 | h171 | h172 | h173 | h174 | h175
  · have he : k = (160 : Fin 2425) := Fin.ext h160
    subst k
    rw [sourceRowsAt160]
    exact rowSound160 B hB hF
  · have he : k = (161 : Fin 2425) := Fin.ext h161
    subst k
    rw [sourceRowsAt161]
    exact rowSound161 B hB hF
  · have he : k = (162 : Fin 2425) := Fin.ext h162
    subst k
    rw [sourceRowsAt162]
    exact rowSound162 B hB hF
  · have he : k = (163 : Fin 2425) := Fin.ext h163
    subst k
    rw [sourceRowsAt163]
    exact rowSound163 B hB hF
  · have he : k = (164 : Fin 2425) := Fin.ext h164
    subst k
    rw [sourceRowsAt164]
    exact rowSound164 B hB hF
  · have he : k = (165 : Fin 2425) := Fin.ext h165
    subst k
    rw [sourceRowsAt165]
    exact rowSound165 B hB hF
  · have he : k = (166 : Fin 2425) := Fin.ext h166
    subst k
    rw [sourceRowsAt166]
    exact rowSound166 B hB hF
  · have he : k = (167 : Fin 2425) := Fin.ext h167
    subst k
    rw [sourceRowsAt167]
    exact rowSound167 B hB hF
  · have he : k = (168 : Fin 2425) := Fin.ext h168
    subst k
    rw [sourceRowsAt168]
    exact rowSound168 B hB hF
  · have he : k = (169 : Fin 2425) := Fin.ext h169
    subst k
    rw [sourceRowsAt169]
    exact rowSound169 B hB hF
  · have he : k = (170 : Fin 2425) := Fin.ext h170
    subst k
    rw [sourceRowsAt170]
    exact rowSound170 B hB hF
  · have he : k = (171 : Fin 2425) := Fin.ext h171
    subst k
    rw [sourceRowsAt171]
    exact rowSound171 B hB hF
  · have he : k = (172 : Fin 2425) := Fin.ext h172
    subst k
    rw [sourceRowsAt172]
    exact rowSound172 B hB hF
  · have he : k = (173 : Fin 2425) := Fin.ext h173
    subst k
    rw [sourceRowsAt173]
    exact rowSound173 B hB hF
  · have he : k = (174 : Fin 2425) := Fin.ext h174
    subst k
    rw [sourceRowsAt174]
    exact rowSound174 B hB hF
  · have he : k = (175 : Fin 2425) := Fin.ext h175
    subst k
    rw [sourceRowsAt175]
    exact rowSound175 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
