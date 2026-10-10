import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources4

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource112 (mixedVector B) = 0 := by
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm132, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1094, h2065, h2292, h2294, h4085, reducedSource112] using sourceEq132 B hB

theorem rowSound112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row112 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck112, numericCheck112, reducedZero112 B hB hF, mul_zero]

theorem reducedZero113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource113 (mixedVector B) = 0 := by
  have h4253 : mixedVector B (Sum.inr 4253) = Sparse.eval nodeValue4253 (mixedVector B) := by
    change mixedMoment B node4253 node4253Labels = _
    exact sound4253 B hB hF
  have h4257 : mixedVector B (Sum.inr 4257) = Sparse.eval nodeValue4257 (mixedVector B) := by
    change mixedMoment B node4257 node4257Labels = _
    exact sound4257 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4729 : mixedVector B (Sum.inr 4729) = Sparse.eval nodeValue4729 (mixedVector B) := by
    change mixedMoment B node4729 node4729Labels = _
    exact sound4729 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  simpa only [sourceForm133, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4253, h4257, h4270, h4583, h4605, h4729, h4742, h4807, h4843, h4889, h4896, h5284, h5294, h5453, reducedSource113] using sourceEq133 B hB

theorem rowSound113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row113 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck113, numericCheck113, reducedZero113 B hB hF, mul_zero]

theorem reducedZero114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource114 (mixedVector B) = 0 := by
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h791 : mixedVector B (Sum.inr 791) = Sparse.eval nodeValue791 (mixedVector B) := by
    change mixedMoment B node791 node791Labels = _
    exact sound791 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h1202 : mixedVector B (Sum.inr 1202) = Sparse.eval nodeValue1202 (mixedVector B) := by
    change mixedMoment B node1202 node1202Labels = _
    exact sound1202 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1898 : mixedVector B (Sum.inr 1898) = Sparse.eval nodeValue1898 (mixedVector B) := by
    change mixedMoment B node1898 node1898Labels = _
    exact sound1898 B hB hF
  have h1915 : mixedVector B (Sum.inr 1915) = Sparse.eval nodeValue1915 (mixedVector B) := by
    change mixedMoment B node1915 node1915Labels = _
    exact sound1915 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3912 : mixedVector B (Sum.inr 3912) = Sparse.eval nodeValue3912 (mixedVector B) := by
    change mixedMoment B node3912 node3912Labels = _
    exact sound3912 B hB hF
  simpa only [sourceForm134, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h787, h791, h813, h1202, h1239, h1898, h1915, h2025, h2062, h2245, h2266, h3077, h3101, h3912, reducedSource114] using sourceEq134 B hB

theorem rowSound114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row114 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck114, numericCheck114, reducedZero114 B hB hF, mul_zero]

theorem reducedZero115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource115 (mixedVector B) = 0 := by
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4445 : mixedVector B (Sum.inr 4445) = Sparse.eval nodeValue4445 (mixedVector B) := by
    change mixedMoment B node4445 node4445Labels = _
    exact sound4445 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4464 : mixedVector B (Sum.inr 4464) = Sparse.eval nodeValue4464 (mixedVector B) := by
    change mixedMoment B node4464 node4464Labels = _
    exact sound4464 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4853 : mixedVector B (Sum.inr 4853) = Sparse.eval nodeValue4853 (mixedVector B) := by
    change mixedMoment B node4853 node4853Labels = _
    exact sound4853 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  simpa only [sourceForm135, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4440, h4442, h4445, h4463, h4464, h4792, h4807, h4853, h4871, h4888, h4895, h5270, h5295, h5306, reducedSource115] using sourceEq135 B hB

theorem rowSound115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row115 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck115, numericCheck115, reducedZero115 B hB hF, mul_zero]

theorem reducedZero116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource116 (mixedVector B) = 0 := by
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1413 : mixedVector B (Sum.inr 1413) = Sparse.eval nodeValue1413 (mixedVector B) := by
    change mixedMoment B node1413 node1413Labels = _
    exact sound1413 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2574 : mixedVector B (Sum.inr 2574) = Sparse.eval nodeValue2574 (mixedVector B) := by
    change mixedMoment B node2574 node2574Labels = _
    exact sound2574 B hB hF
  have h2602 : mixedVector B (Sum.inr 2602) = Sparse.eval nodeValue2602 (mixedVector B) := by
    change mixedMoment B node2602 node2602Labels = _
    exact sound2602 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  have h3229 : mixedVector B (Sum.inr 3229) = Sparse.eval nodeValue3229 (mixedVector B) := by
    change mixedMoment B node3229 node3229Labels = _
    exact sound3229 B hB hF
  simpa only [sourceForm136, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1024, h1027, h1047, h1388, h1413, h2471, h2486, h2574, h2602, h2754, h2769, h3120, h3227, h3229, reducedSource116] using sourceEq136 B hB

theorem rowSound116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row116 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck116, numericCheck116, reducedZero116 B hB hF, mul_zero]

theorem reducedZero117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource117 (mixedVector B) = 0 := by
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2784 : mixedVector B (Sum.inr 2784) = Sparse.eval nodeValue2784 (mixedVector B) := by
    change mixedMoment B node2784 node2784Labels = _
    exact sound2784 B hB hF
  simpa only [sourceForm137, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1723, h1744, h1745, h1749, h1750, h2201, h2224, h2259, h2262, h2287, h2291, h2738, h2781, h2784, reducedSource117] using sourceEq137 B hB

theorem rowSound117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row117 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck117, numericCheck117, reducedZero117 B hB hF, mul_zero]

theorem reducedZero118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource118 (mixedVector B) = 0 := by
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm138, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2244, h2247, h2265, h3623, h4083, reducedSource118] using sourceEq138 B hB

theorem rowSound118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row118 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck118, numericCheck118, reducedZero118 B hB hF, mul_zero]

theorem reducedZero119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource119 (mixedVector B) = 0 := by
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm139, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1027, h1385, h1408, h2247, h4083, reducedSource119] using sourceEq139 B hB

theorem rowSound119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row119 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck119, numericCheck119, reducedZero119 B hB hF, mul_zero]

theorem reducedZero120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource120 (mixedVector B) = 0 := by
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm140, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1385, h2009, h2025, h2247, h3075, h4083, reducedSource120] using sourceEq140 B hB

theorem rowSound120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row120 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck120, numericCheck120, reducedZero120 B hB hF, mul_zero]

theorem reducedZero121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource121 (mixedVector B) = 0 := by
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm141, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1022, h2009, h2090, h2244, h2247, h4083, reducedSource121] using sourceEq141 B hB

theorem rowSound121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row121 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck121, numericCheck121, reducedZero121 B hB hF, mul_zero]

theorem reducedZero122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource122 (mixedVector B) = 0 := by
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm142, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1408, h2090, h2112, h2247, h3098, h4083, reducedSource122] using sourceEq142 B hB

theorem rowSound122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row122 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck122, numericCheck122, reducedZero122 B hB hF, mul_zero]

theorem reducedZero123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource123 (mixedVector B) = 0 := by
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm143, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1046, h2025, h2112, h2247, h2265, h4083, reducedSource123] using sourceEq143 B hB

theorem rowSound123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row123 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck123, numericCheck123, reducedZero123 B hB hF, mul_zero]

theorem reducedZero124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource124 (mixedVector B) = 0 := by
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm144, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1022, h1027, h1046, h2247, h4083, reducedSource124] using sourceEq144 B hB

theorem rowSound124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row124 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck124, numericCheck124, reducedZero124 B hB hF, mul_zero]

theorem reducedZero125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource125 (mixedVector B) = 0 := by
  have h4494 : mixedVector B (Sum.inr 4494) = Sparse.eval nodeValue4494 (mixedVector B) := by
    change mixedMoment B node4494 node4494Labels = _
    exact sound4494 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4500 : mixedVector B (Sum.inr 4500) = Sparse.eval nodeValue4500 (mixedVector B) := by
    change mixedMoment B node4500 node4500Labels = _
    exact sound4500 B hB hF
  have h4830 : mixedVector B (Sum.inr 4830) = Sparse.eval nodeValue4830 (mixedVector B) := by
    change mixedMoment B node4830 node4830Labels = _
    exact sound4830 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4886 : mixedVector B (Sum.inr 4886) = Sparse.eval nodeValue4886 (mixedVector B) := by
    change mixedMoment B node4886 node4886Labels = _
    exact sound4886 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4892 : mixedVector B (Sum.inr 4892) = Sparse.eval nodeValue4892 (mixedVector B) := by
    change mixedMoment B node4892 node4892Labels = _
    exact sound4892 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  simpa only [sourceForm145, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4494, h4496, h4500, h4830, h4832, h4836, h4886, h4890, h4892, h4897, h4899, h5252, h5296, reducedSource125] using sourceEq145 B hB

theorem rowSound125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row125 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck125, numericCheck125, reducedZero125 B hB hF, mul_zero]

theorem reducedZero126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource126 (mixedVector B) = 0 := by
  have h1435 : mixedVector B (Sum.inr 1435) = Sparse.eval nodeValue1435 (mixedVector B) := by
    change mixedMoment B node1435 node1435Labels = _
    exact sound1435 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h1451 : mixedVector B (Sum.inr 1451) = Sparse.eval nodeValue1451 (mixedVector B) := by
    change mixedMoment B node1451 node1451Labels = _
    exact sound1451 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2707 : mixedVector B (Sum.inr 2707) = Sparse.eval nodeValue2707 (mixedVector B) := by
    change mixedMoment B node2707 node2707Labels = _
    exact sound2707 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h2755 : mixedVector B (Sum.inr 2755) = Sparse.eval nodeValue2755 (mixedVector B) := by
    change mixedMoment B node2755 node2755Labels = _
    exact sound2755 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h2778 : mixedVector B (Sum.inr 2778) = Sparse.eval nodeValue2778 (mixedVector B) := by
    change mixedMoment B node2778 node2778Labels = _
    exact sound2778 B hB hF
  have h3082 : mixedVector B (Sum.inr 3082) = Sparse.eval nodeValue3082 (mixedVector B) := by
    change mixedMoment B node3082 node3082Labels = _
    exact sound3082 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  simpa only [sourceForm146, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1435, h1436, h1451, h2235, h2247, h2255, h2707, h2712, h2716, h2755, h2770, h2778, h3082, h3114, reducedSource126] using sourceEq146 B hB

theorem rowSound126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row126 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck126, numericCheck126, reducedZero126 B hB hF, mul_zero]

theorem reducedZero127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource127 (mixedVector B) = 0 := by
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h2187 : mixedVector B (Sum.inr 2187) = Sparse.eval nodeValue2187 (mixedVector B) := by
    change mixedMoment B node2187 node2187Labels = _
    exact sound2187 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2755 : mixedVector B (Sum.inr 2755) = Sparse.eval nodeValue2755 (mixedVector B) := by
    change mixedMoment B node2755 node2755Labels = _
    exact sound2755 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  simpa only [sourceForm147, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1700, h1710, h1716, h2187, h2193, h2197, h2235, h2247, h2255, h2268, h2281, h2712, h2755, h2770, reducedSource127] using sourceEq147 B hB

theorem rowSound127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row127 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck127, numericCheck127, reducedZero127 B hB hF, mul_zero]

theorem sourceRowsAt112 : MixedData.sourceRows (112 : Fin 2425) =
    MixedData.row112 := by decide +kernel

theorem sourceRowsAt113 : MixedData.sourceRows (113 : Fin 2425) =
    MixedData.row113 := by decide +kernel

theorem sourceRowsAt114 : MixedData.sourceRows (114 : Fin 2425) =
    MixedData.row114 := by decide +kernel

theorem sourceRowsAt115 : MixedData.sourceRows (115 : Fin 2425) =
    MixedData.row115 := by decide +kernel

theorem sourceRowsAt116 : MixedData.sourceRows (116 : Fin 2425) =
    MixedData.row116 := by decide +kernel

theorem sourceRowsAt117 : MixedData.sourceRows (117 : Fin 2425) =
    MixedData.row117 := by decide +kernel

theorem sourceRowsAt118 : MixedData.sourceRows (118 : Fin 2425) =
    MixedData.row118 := by decide +kernel

theorem sourceRowsAt119 : MixedData.sourceRows (119 : Fin 2425) =
    MixedData.row119 := by decide +kernel

theorem sourceRowsAt120 : MixedData.sourceRows (120 : Fin 2425) =
    MixedData.row120 := by decide +kernel

theorem sourceRowsAt121 : MixedData.sourceRows (121 : Fin 2425) =
    MixedData.row121 := by decide +kernel

theorem sourceRowsAt122 : MixedData.sourceRows (122 : Fin 2425) =
    MixedData.row122 := by decide +kernel

theorem sourceRowsAt123 : MixedData.sourceRows (123 : Fin 2425) =
    MixedData.row123 := by decide +kernel

theorem sourceRowsAt124 : MixedData.sourceRows (124 : Fin 2425) =
    MixedData.row124 := by decide +kernel

theorem sourceRowsAt125 : MixedData.sourceRows (125 : Fin 2425) =
    MixedData.row125 := by decide +kernel

theorem sourceRowsAt126 : MixedData.sourceRows (126 : Fin 2425) =
    MixedData.row126 := by decide +kernel

theorem sourceRowsAt127 : MixedData.sourceRows (127 : Fin 2425) =
    MixedData.row127 := by decide +kernel

theorem chunkSound7 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 7) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 112 ∨ k.val = 113 ∨ k.val = 114 ∨ k.val = 115 ∨ k.val = 116 ∨ k.val = 117 ∨ k.val = 118 ∨ k.val = 119 ∨ k.val = 120 ∨ k.val = 121 ∨ k.val = 122 ∨ k.val = 123 ∨ k.val = 124 ∨ k.val = 125 ∨ k.val = 126 ∨ k.val = 127 := by omega
  rcases heq with h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127
  · have he : k = (112 : Fin 2425) := Fin.ext h112
    subst k
    rw [sourceRowsAt112]
    exact rowSound112 B hB hF
  · have he : k = (113 : Fin 2425) := Fin.ext h113
    subst k
    rw [sourceRowsAt113]
    exact rowSound113 B hB hF
  · have he : k = (114 : Fin 2425) := Fin.ext h114
    subst k
    rw [sourceRowsAt114]
    exact rowSound114 B hB hF
  · have he : k = (115 : Fin 2425) := Fin.ext h115
    subst k
    rw [sourceRowsAt115]
    exact rowSound115 B hB hF
  · have he : k = (116 : Fin 2425) := Fin.ext h116
    subst k
    rw [sourceRowsAt116]
    exact rowSound116 B hB hF
  · have he : k = (117 : Fin 2425) := Fin.ext h117
    subst k
    rw [sourceRowsAt117]
    exact rowSound117 B hB hF
  · have he : k = (118 : Fin 2425) := Fin.ext h118
    subst k
    rw [sourceRowsAt118]
    exact rowSound118 B hB hF
  · have he : k = (119 : Fin 2425) := Fin.ext h119
    subst k
    rw [sourceRowsAt119]
    exact rowSound119 B hB hF
  · have he : k = (120 : Fin 2425) := Fin.ext h120
    subst k
    rw [sourceRowsAt120]
    exact rowSound120 B hB hF
  · have he : k = (121 : Fin 2425) := Fin.ext h121
    subst k
    rw [sourceRowsAt121]
    exact rowSound121 B hB hF
  · have he : k = (122 : Fin 2425) := Fin.ext h122
    subst k
    rw [sourceRowsAt122]
    exact rowSound122 B hB hF
  · have he : k = (123 : Fin 2425) := Fin.ext h123
    subst k
    rw [sourceRowsAt123]
    exact rowSound123 B hB hF
  · have he : k = (124 : Fin 2425) := Fin.ext h124
    subst k
    rw [sourceRowsAt124]
    exact rowSound124 B hB hF
  · have he : k = (125 : Fin 2425) := Fin.ext h125
    subst k
    rw [sourceRowsAt125]
    exact rowSound125 B hB hF
  · have he : k = (126 : Fin 2425) := Fin.ext h126
    subst k
    rw [sourceRowsAt126]
    exact rowSound126 B hB hF
  · have he : k = (127 : Fin 2425) := Fin.ext h127
    subst k
    rw [sourceRowsAt127]
    exact rowSound127 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
