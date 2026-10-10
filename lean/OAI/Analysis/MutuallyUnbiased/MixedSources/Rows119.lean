import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic119
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources73

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1904 (mixedVector B) = 0 := by
  have h4550 : mixedVector B (Sum.inr 4550) = Sparse.eval nodeValue4550 (mixedVector B) := by
    change mixedMoment B node4550 node4550Labels = _
    exact sound4550 B hB hF
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4553 : mixedVector B (Sum.inr 4553) = Sparse.eval nodeValue4553 (mixedVector B) := by
    change mixedMoment B node4553 node4553Labels = _
    exact sound4553 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4967 : mixedVector B (Sum.inr 4967) = Sparse.eval nodeValue4967 (mixedVector B) := by
    change mixedMoment B node4967 node4967Labels = _
    exact sound4967 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h5113 : mixedVector B (Sum.inr 5113) = Sparse.eval nodeValue5113 (mixedVector B) := by
    change mixedMoment B node5113 node5113Labels = _
    exact sound5113 B hB hF
  have h5114 : mixedVector B (Sum.inr 5114) = Sparse.eval nodeValue5114 (mixedVector B) := by
    change mixedMoment B node5114 node5114Labels = _
    exact sound5114 B hB hF
  have h5166 : mixedVector B (Sum.inr 5166) = Sparse.eval nodeValue5166 (mixedVector B) := by
    change mixedMoment B node5166 node5166Labels = _
    exact sound5166 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5415 : mixedVector B (Sum.inr 5415) = Sparse.eval nodeValue5415 (mixedVector B) := by
    change mixedMoment B node5415 node5415Labels = _
    exact sound5415 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  simpa only [sourceForm2338, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4550, h4551, h4553, h4623, h4967, h4970, h4973, h5113, h5114, h5166, h5168, h5170, h5171, h5176, h5306, h5308, h5387, h5415, h5439, h5441, reducedSource1904] using sourceEq2338 B hB

theorem rowSound1904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1904 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1904, numericCheck1904, reducedZero1904 B hB hF, mul_zero]

theorem reducedZero1905 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1905 (mixedVector B) = 0 := by
  have h1135 : mixedVector B (Sum.inr 1135) = Sparse.eval nodeValue1135 (mixedVector B) := by
    change mixedMoment B node1135 node1135Labels = _
    exact sound1135 B hB hF
  have h1136 : mixedVector B (Sum.inr 1136) = Sparse.eval nodeValue1136 (mixedVector B) := by
    change mixedMoment B node1136 node1136Labels = _
    exact sound1136 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h2814 : mixedVector B (Sum.inr 2814) = Sparse.eval nodeValue2814 (mixedVector B) := by
    change mixedMoment B node2814 node2814Labels = _
    exact sound2814 B hB hF
  have h2815 : mixedVector B (Sum.inr 2815) = Sparse.eval nodeValue2815 (mixedVector B) := by
    change mixedMoment B node2815 node2815Labels = _
    exact sound2815 B hB hF
  have h2817 : mixedVector B (Sum.inr 2817) = Sparse.eval nodeValue2817 (mixedVector B) := by
    change mixedMoment B node2817 node2817Labels = _
    exact sound2817 B hB hF
  have h2894 : mixedVector B (Sum.inr 2894) = Sparse.eval nodeValue2894 (mixedVector B) := by
    change mixedMoment B node2894 node2894Labels = _
    exact sound2894 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2953 : mixedVector B (Sum.inr 2953) = Sparse.eval nodeValue2953 (mixedVector B) := by
    change mixedMoment B node2953 node2953Labels = _
    exact sound2953 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2963 : mixedVector B (Sum.inr 2963) = Sparse.eval nodeValue2963 (mixedVector B) := by
    change mixedMoment B node2963 node2963Labels = _
    exact sound2963 B hB hF
  have h2965 : mixedVector B (Sum.inr 2965) = Sparse.eval nodeValue2965 (mixedVector B) := by
    change mixedMoment B node2965 node2965Labels = _
    exact sound2965 B hB hF
  have h2968 : mixedVector B (Sum.inr 2968) = Sparse.eval nodeValue2968 (mixedVector B) := by
    change mixedMoment B node2968 node2968Labels = _
    exact sound2968 B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  have h3739 : mixedVector B (Sum.inr 3739) = Sparse.eval nodeValue3739 (mixedVector B) := by
    change mixedMoment B node3739 node3739Labels = _
    exact sound3739 B hB hF
  have h4012 : mixedVector B (Sum.inr 4012) = Sparse.eval nodeValue4012 (mixedVector B) := by
    change mixedMoment B node4012 node4012Labels = _
    exact sound4012 B hB hF
  have h4031 : mixedVector B (Sum.inr 4031) = Sparse.eval nodeValue4031 (mixedVector B) := by
    change mixedMoment B node4031 node4031Labels = _
    exact sound4031 B hB hF
  have h4037 : mixedVector B (Sum.inr 4037) = Sparse.eval nodeValue4037 (mixedVector B) := by
    change mixedMoment B node4037 node4037Labels = _
    exact sound4037 B hB hF
  simpa only [sourceForm2339, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1135, h1136, h1138, h1305, h2814, h2815, h2817, h2894, h2896, h2953, h2954, h2963, h2965, h2968, h3120, h3124, h3739, h4012, h4031, h4037, reducedSource1905] using sourceEq2339 B hB

theorem rowSound1905 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1905 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1905, numericCheck1905, reducedZero1905 B hB hF, mul_zero]

theorem reducedZero1906 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1906 (mixedVector B) = 0 := by
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm2340, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4341, h4343, h4349, h4457, h4760, h4769, h4804, h4939, h4946, h5036, h5072, h5134, h5141, h5167, h5169, h5258, h5292, h5416, h5418, h5434, h5486, reducedSource1906] using sourceEq2340 B hB

theorem rowSound1906 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1906 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1906, numericCheck1906, reducedZero1906 B hB hF, mul_zero]

theorem reducedZero1907 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1907 (mixedVector B) = 0 := by
  have h919 : mixedVector B (Sum.inr 919) = Sparse.eval nodeValue919 (mixedVector B) := by
    change mixedMoment B node919 node919Labels = _
    exact sound919 B hB hF
  have h921 : mixedVector B (Sum.inr 921) = Sparse.eval nodeValue921 (mixedVector B) := by
    change mixedMoment B node921 node921Labels = _
    exact sound921 B hB hF
  have h927 : mixedVector B (Sum.inr 927) = Sparse.eval nodeValue927 (mixedVector B) := by
    change mixedMoment B node927 node927Labels = _
    exact sound927 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1960 : mixedVector B (Sum.inr 1960) = Sparse.eval nodeValue1960 (mixedVector B) := by
    change mixedMoment B node1960 node1960Labels = _
    exact sound1960 B hB hF
  have h1969 : mixedVector B (Sum.inr 1969) = Sparse.eval nodeValue1969 (mixedVector B) := by
    change mixedMoment B node1969 node1969Labels = _
    exact sound1969 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2330 : mixedVector B (Sum.inr 2330) = Sparse.eval nodeValue2330 (mixedVector B) := by
    change mixedMoment B node2330 node2330Labels = _
    exact sound2330 B hB hF
  have h2337 : mixedVector B (Sum.inr 2337) = Sparse.eval nodeValue2337 (mixedVector B) := by
    change mixedMoment B node2337 node2337Labels = _
    exact sound2337 B hB hF
  have h2428 : mixedVector B (Sum.inr 2428) = Sparse.eval nodeValue2428 (mixedVector B) := by
    change mixedMoment B node2428 node2428Labels = _
    exact sound2428 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h2593 : mixedVector B (Sum.inr 2593) = Sparse.eval nodeValue2593 (mixedVector B) := by
    change mixedMoment B node2593 node2593Labels = _
    exact sound2593 B hB hF
  have h2595 : mixedVector B (Sum.inr 2595) = Sparse.eval nodeValue2595 (mixedVector B) := by
    change mixedMoment B node2595 node2595Labels = _
    exact sound2595 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h3821 : mixedVector B (Sum.inr 3821) = Sparse.eval nodeValue3821 (mixedVector B) := by
    change mixedMoment B node3821 node3821Labels = _
    exact sound3821 B hB hF
  have h3824 : mixedVector B (Sum.inr 3824) = Sparse.eval nodeValue3824 (mixedVector B) := by
    change mixedMoment B node3824 node3824Labels = _
    exact sound3824 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852 B hB hF
  have h3999 : mixedVector B (Sum.inr 3999) = Sparse.eval nodeValue3999 (mixedVector B) := by
    change mixedMoment B node3999 node3999Labels = _
    exact sound3999 B hB hF
  simpa only [sourceForm2341, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h919, h921, h927, h1040, h1960, h1969, h2022, h2330, h2337, h2428, h2479, h2553, h2561, h2593, h2595, h2722, h2766, h3821, h3824, h3852, h3999, reducedSource1907] using sourceEq2341 B hB

theorem rowSound1907 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1907 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1907, numericCheck1907, reducedZero1907 B hB hF, mul_zero]

theorem reducedZero1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1908 (mixedVector B) = 0 := by
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4554 : mixedVector B (Sum.inr 4554) = Sparse.eval nodeValue4554 (mixedVector B) := by
    change mixedMoment B node4554 node4554Labels = _
    exact sound4554 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h4974 : mixedVector B (Sum.inr 4974) = Sparse.eval nodeValue4974 (mixedVector B) := by
    change mixedMoment B node4974 node4974Labels = _
    exact sound4974 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h5037 : mixedVector B (Sum.inr 5037) = Sparse.eval nodeValue5037 (mixedVector B) := by
    change mixedMoment B node5037 node5037Labels = _
    exact sound5037 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5115 : mixedVector B (Sum.inr 5115) = Sparse.eval nodeValue5115 (mixedVector B) := by
    change mixedMoment B node5115 node5115Labels = _
    exact sound5115 B hB hF
  have h5117 : mixedVector B (Sum.inr 5117) = Sparse.eval nodeValue5117 (mixedVector B) := by
    change mixedMoment B node5117 node5117Labels = _
    exact sound5117 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  simpa only [sourceForm2342, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4544, h4546, h4549, h4554, h4624, h4968, h4972, h4974, h4977, h5037, h5078, h5115, h5117, h5148, h5152, h5167, h5169, h5172, h5174, h5177, h5293, h5307, h5309, h5388, h5416, h5434, h5440, h5442, reducedSource1908] using sourceEq2342 B hB

theorem rowSound1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1908 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1908, numericCheck1908, reducedZero1908 B hB hF, mul_zero]

theorem reducedZero1909 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1909 (mixedVector B) = 0 := by
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1301 : mixedVector B (Sum.inr 1301) = Sparse.eval nodeValue1301 (mixedVector B) := by
    change mixedMoment B node1301 node1301Labels = _
    exact sound1301 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2434 : mixedVector B (Sum.inr 2434) = Sparse.eval nodeValue2434 (mixedVector B) := by
    change mixedMoment B node2434 node2434Labels = _
    exact sound2434 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2809 : mixedVector B (Sum.inr 2809) = Sparse.eval nodeValue2809 (mixedVector B) := by
    change mixedMoment B node2809 node2809Labels = _
    exact sound2809 B hB hF
  have h2813 : mixedVector B (Sum.inr 2813) = Sparse.eval nodeValue2813 (mixedVector B) := by
    change mixedMoment B node2813 node2813Labels = _
    exact sound2813 B hB hF
  have h2818 : mixedVector B (Sum.inr 2818) = Sparse.eval nodeValue2818 (mixedVector B) := by
    change mixedMoment B node2818 node2818Labels = _
    exact sound2818 B hB hF
  have h2893 : mixedVector B (Sum.inr 2893) = Sparse.eval nodeValue2893 (mixedVector B) := by
    change mixedMoment B node2893 node2893Labels = _
    exact sound2893 B hB hF
  have h2897 : mixedVector B (Sum.inr 2897) = Sparse.eval nodeValue2897 (mixedVector B) := by
    change mixedMoment B node2897 node2897Labels = _
    exact sound2897 B hB hF
  have h2927 : mixedVector B (Sum.inr 2927) = Sparse.eval nodeValue2927 (mixedVector B) := by
    change mixedMoment B node2927 node2927Labels = _
    exact sound2927 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2958 : mixedVector B (Sum.inr 2958) = Sparse.eval nodeValue2958 (mixedVector B) := by
    change mixedMoment B node2958 node2958Labels = _
    exact sound2958 B hB hF
  have h2959 : mixedVector B (Sum.inr 2959) = Sparse.eval nodeValue2959 (mixedVector B) := by
    change mixedMoment B node2959 node2959Labels = _
    exact sound2959 B hB hF
  have h2960 : mixedVector B (Sum.inr 2960) = Sparse.eval nodeValue2960 (mixedVector B) := by
    change mixedMoment B node2960 node2960Labels = _
    exact sound2960 B hB hF
  have h2969 : mixedVector B (Sum.inr 2969) = Sparse.eval nodeValue2969 (mixedVector B) := by
    change mixedMoment B node2969 node2969Labels = _
    exact sound2969 B hB hF
  have h3102 : mixedVector B (Sum.inr 3102) = Sparse.eval nodeValue3102 (mixedVector B) := by
    change mixedMoment B node3102 node3102Labels = _
    exact sound3102 B hB hF
  have h3122 : mixedVector B (Sum.inr 3122) = Sparse.eval nodeValue3122 (mixedVector B) := by
    change mixedMoment B node3122 node3122Labels = _
    exact sound3122 B hB hF
  have h3123 : mixedVector B (Sum.inr 3123) = Sparse.eval nodeValue3123 (mixedVector B) := by
    change mixedMoment B node3123 node3123Labels = _
    exact sound3123 B hB hF
  have h3737 : mixedVector B (Sum.inr 3737) = Sparse.eval nodeValue3737 (mixedVector B) := by
    change mixedMoment B node3737 node3737Labels = _
    exact sound3737 B hB hF
  have h3967 : mixedVector B (Sum.inr 3967) = Sparse.eval nodeValue3967 (mixedVector B) := by
    change mixedMoment B node3967 node3967Labels = _
    exact sound3967 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  have h4036 : mixedVector B (Sum.inr 4036) = Sparse.eval nodeValue4036 (mixedVector B) := by
    change mixedMoment B node4036 node4036Labels = _
    exact sound4036 B hB hF
  simpa only [sourceForm2343, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1129, h1131, h1134, h1139, h1301, h2429, h2434, h2485, h2601, h2809, h2813, h2818, h2893, h2897, h2927, h2931, h2958, h2959, h2960, h2969, h3102, h3122, h3123, h3737, h3967, h3982, h4001, h4036, reducedSource1909] using sourceEq2343 B hB

theorem rowSound1909 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1909 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1909, numericCheck1909, reducedZero1909 B hB hF, mul_zero]

theorem reducedZero1910 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1910 (mixedVector B) = 0 := by
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4950 : mixedVector B (Sum.inr 4950) = Sparse.eval nodeValue4950 (mixedVector B) := by
    change mixedMoment B node4950 node4950Labels = _
    exact sound4950 B hB hF
  have h5033 : mixedVector B (Sum.inr 5033) = Sparse.eval nodeValue5033 (mixedVector B) := by
    change mixedMoment B node5033 node5033Labels = _
    exact sound5033 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5039 : mixedVector B (Sum.inr 5039) = Sparse.eval nodeValue5039 (mixedVector B) := by
    change mixedMoment B node5039 node5039Labels = _
    exact sound5039 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465 B hB hF
  have h5476 : mixedVector B (Sum.inr 5476) = Sparse.eval nodeValue5476 (mixedVector B) := by
    change mixedMoment B node5476 node5476Labels = _
    exact sound5476 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  have h5487 : mixedVector B (Sum.inr 5487) = Sparse.eval nodeValue5487 (mixedVector B) := by
    change mixedMoment B node5487 node5487Labels = _
    exact sound5487 B hB hF
  simpa only [sourceForm2344, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4344, h4346, h4349, h4355, h4458, h4941, h4943, h4946, h4950, h5033, h5036, h5039, h5073, h5075, h5137, h5141, h5167, h5168, h5169, h5171, h5177, h5259, h5292, h5293, h5465, h5476, h5483, h5486, h5487, reducedSource1910] using sourceEq2344 B hB

theorem rowSound1910 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1910 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1910, numericCheck1910, reducedZero1910 B hB hF, mul_zero]

theorem reducedZero1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1911 (mixedVector B) = 0 := by
  have h922 : mixedVector B (Sum.inr 922) = Sparse.eval nodeValue922 (mixedVector B) := by
    change mixedMoment B node922 node922Labels = _
    exact sound922 B hB hF
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h927 : mixedVector B (Sum.inr 927) = Sparse.eval nodeValue927 (mixedVector B) := by
    change mixedMoment B node927 node927Labels = _
    exact sound927 B hB hF
  have h933 : mixedVector B (Sum.inr 933) = Sparse.eval nodeValue933 (mixedVector B) := by
    change mixedMoment B node933 node933Labels = _
    exact sound933 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h2332 : mixedVector B (Sum.inr 2332) = Sparse.eval nodeValue2332 (mixedVector B) := by
    change mixedMoment B node2332 node2332Labels = _
    exact sound2332 B hB hF
  have h2334 : mixedVector B (Sum.inr 2334) = Sparse.eval nodeValue2334 (mixedVector B) := by
    change mixedMoment B node2334 node2334Labels = _
    exact sound2334 B hB hF
  have h2337 : mixedVector B (Sum.inr 2337) = Sparse.eval nodeValue2337 (mixedVector B) := by
    change mixedMoment B node2337 node2337Labels = _
    exact sound2337 B hB hF
  have h2342 : mixedVector B (Sum.inr 2342) = Sparse.eval nodeValue2342 (mixedVector B) := by
    change mixedMoment B node2342 node2342Labels = _
    exact sound2342 B hB hF
  have h2425 : mixedVector B (Sum.inr 2425) = Sparse.eval nodeValue2425 (mixedVector B) := by
    change mixedMoment B node2425 node2425Labels = _
    exact sound2425 B hB hF
  have h2428 : mixedVector B (Sum.inr 2428) = Sparse.eval nodeValue2428 (mixedVector B) := by
    change mixedMoment B node2428 node2428Labels = _
    exact sound2428 B hB hF
  have h2432 : mixedVector B (Sum.inr 2432) = Sparse.eval nodeValue2432 (mixedVector B) := by
    change mixedMoment B node2432 node2432Labels = _
    exact sound2432 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h2593 : mixedVector B (Sum.inr 2593) = Sparse.eval nodeValue2593 (mixedVector B) := by
    change mixedMoment B node2593 node2593Labels = _
    exact sound2593 B hB hF
  have h2594 : mixedVector B (Sum.inr 2594) = Sparse.eval nodeValue2594 (mixedVector B) := by
    change mixedMoment B node2594 node2594Labels = _
    exact sound2594 B hB hF
  have h2595 : mixedVector B (Sum.inr 2595) = Sparse.eval nodeValue2595 (mixedVector B) := by
    change mixedMoment B node2595 node2595Labels = _
    exact sound2595 B hB hF
  have h2598 : mixedVector B (Sum.inr 2598) = Sparse.eval nodeValue2598 (mixedVector B) := by
    change mixedMoment B node2598 node2598Labels = _
    exact sound2598 B hB hF
  have h2605 : mixedVector B (Sum.inr 2605) = Sparse.eval nodeValue2605 (mixedVector B) := by
    change mixedMoment B node2605 node2605Labels = _
    exact sound2605 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h3931 : mixedVector B (Sum.inr 3931) = Sparse.eval nodeValue3931 (mixedVector B) := by
    change mixedMoment B node3931 node3931Labels = _
    exact sound3931 B hB hF
  have h3965 : mixedVector B (Sum.inr 3965) = Sparse.eval nodeValue3965 (mixedVector B) := by
    change mixedMoment B node3965 node3965Labels = _
    exact sound3965 B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981 B hB hF
  have h3999 : mixedVector B (Sum.inr 3999) = Sparse.eval nodeValue3999 (mixedVector B) := by
    change mixedMoment B node3999 node3999Labels = _
    exact sound3999 B hB hF
  have h4000 : mixedVector B (Sum.inr 4000) = Sparse.eval nodeValue4000 (mixedVector B) := by
    change mixedMoment B node4000 node4000Labels = _
    exact sound4000 B hB hF
  simpa only [sourceForm2345, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h922, h924, h927, h933, h1041, h2332, h2334, h2337, h2342, h2425, h2428, h2432, h2480, h2482, h2556, h2561, h2593, h2594, h2595, h2598, h2605, h2723, h2766, h2767, h3931, h3965, h3981, h3999, h4000, reducedSource1911] using sourceEq2345 B hB

theorem rowSound1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1911 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1911, numericCheck1911, reducedZero1911 B hB hF, mul_zero]

theorem reducedZero1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1912 (mixedVector B) = 0 := by
  have h4345 : mixedVector B (Sum.inr 4345) = Sparse.eval nodeValue4345 (mixedVector B) := by
    change mixedMoment B node4345 node4345Labels = _
    exact sound4345 B hB hF
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4348 : mixedVector B (Sum.inr 4348) = Sparse.eval nodeValue4348 (mixedVector B) := by
    change mixedMoment B node4348 node4348Labels = _
    exact sound4348 B hB hF
  have h4357 : mixedVector B (Sum.inr 4357) = Sparse.eval nodeValue4357 (mixedVector B) := by
    change mixedMoment B node4357 node4357Labels = _
    exact sound4357 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4942 : mixedVector B (Sum.inr 4942) = Sparse.eval nodeValue4942 (mixedVector B) := by
    change mixedMoment B node4942 node4942Labels = _
    exact sound4942 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h5034 : mixedVector B (Sum.inr 5034) = Sparse.eval nodeValue5034 (mixedVector B) := by
    change mixedMoment B node5034 node5034Labels = _
    exact sound5034 B hB hF
  have h5035 : mixedVector B (Sum.inr 5035) = Sparse.eval nodeValue5035 (mixedVector B) := by
    change mixedMoment B node5035 node5035Labels = _
    exact sound5035 B hB hF
  have h5040 : mixedVector B (Sum.inr 5040) = Sparse.eval nodeValue5040 (mixedVector B) := by
    change mixedMoment B node5040 node5040Labels = _
    exact sound5040 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5161 : mixedVector B (Sum.inr 5161) = Sparse.eval nodeValue5161 (mixedVector B) := by
    change mixedMoment B node5161 node5161Labels = _
    exact sound5161 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  simpa only [sourceForm2348, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4345, h4347, h4348, h4357, h4459, h4942, h4944, h4945, h4951, h5034, h5035, h5040, h5074, h5078, h5138, h5139, h5140, h5149, h5152, h5160, h5161, h5164, h5260, h5284, h5289, h5401, h5404, h5410, h5438, h5484, reducedSource1912] using sourceEq2348 B hB

theorem rowSound1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1912 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1912, numericCheck1912, reducedZero1912 B hB hF, mul_zero]

theorem reducedZero1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1913 (mixedVector B) = 0 := by
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h2652 : mixedVector B (Sum.inr 2652) = Sparse.eval nodeValue2652 (mixedVector B) := by
    change mixedMoment B node2652 node2652Labels = _
    exact sound2652 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3454 : mixedVector B (Sum.inr 3454) = Sparse.eval nodeValue3454 (mixedVector B) := by
    change mixedMoment B node3454 node3454Labels = _
    exact sound3454 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3815 : mixedVector B (Sum.inr 3815) = Sparse.eval nodeValue3815 (mixedVector B) := by
    change mixedMoment B node3815 node3815Labels = _
    exact sound3815 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  simpa only [sourceForm2349, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1668, h1669, h1676, h1682, h1714, h2652, h2658, h2670, h2719, h3407, h3413, h3418, h3451, h3454, h3463, h3481, h3517, h3523, h3540, h3558, h3565, h3572, h3605, h3612, h3625, h3804, h3815, h3816, h3857, h3983, reducedSource1913] using sourceEq2349 B hB

theorem rowSound1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1913 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1913, numericCheck1913, reducedZero1913 B hB hF, mul_zero]

theorem reducedZero1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1914 (mixedVector B) = 0 := by
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4971 : mixedVector B (Sum.inr 4971) = Sparse.eval nodeValue4971 (mixedVector B) := by
    change mixedMoment B node4971 node4971Labels = _
    exact sound4971 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h5117 : mixedVector B (Sum.inr 5117) = Sparse.eval nodeValue5117 (mixedVector B) := by
    change mixedMoment B node5117 node5117Labels = _
    exact sound5117 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387 B hB hF
  have h5417 : mixedVector B (Sum.inr 5417) = Sparse.eval nodeValue5417 (mixedVector B) := by
    change mixedMoment B node5417 node5417Labels = _
    exact sound5417 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  simpa only [sourceForm2350, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4541, h4543, h4549, h4623, h4764, h4770, h4807, h4971, h4977, h5117, h5149, h5152, h5167, h5169, h5172, h5294, h5307, h5387, h5417, h5435, h5440, reducedSource1914] using sourceEq2350 B hB

theorem rowSound1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1914 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1914, numericCheck1914, reducedZero1914 B hB hF, mul_zero]

theorem reducedZero1915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1915 (mixedVector B) = 0 := by
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1300 : mixedVector B (Sum.inr 1300) = Sparse.eval nodeValue1300 (mixedVector B) := by
    change mixedMoment B node1300 node1300Labels = _
    exact sound1300 B hB hF
  have h1964 : mixedVector B (Sum.inr 1964) = Sparse.eval nodeValue1964 (mixedVector B) := by
    change mixedMoment B node1964 node1964Labels = _
    exact sound1964 B hB hF
  have h1970 : mixedVector B (Sum.inr 1970) = Sparse.eval nodeValue1970 (mixedVector B) := by
    change mixedMoment B node1970 node1970Labels = _
    exact sound1970 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2807 : mixedVector B (Sum.inr 2807) = Sparse.eval nodeValue2807 (mixedVector B) := by
    change mixedMoment B node2807 node2807Labels = _
    exact sound2807 B hB hF
  have h2813 : mixedVector B (Sum.inr 2813) = Sparse.eval nodeValue2813 (mixedVector B) := by
    change mixedMoment B node2813 node2813Labels = _
    exact sound2813 B hB hF
  have h2893 : mixedVector B (Sum.inr 2893) = Sparse.eval nodeValue2893 (mixedVector B) := by
    change mixedMoment B node2893 node2893Labels = _
    exact sound2893 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2958 : mixedVector B (Sum.inr 2958) = Sparse.eval nodeValue2958 (mixedVector B) := by
    change mixedMoment B node2958 node2958Labels = _
    exact sound2958 B hB hF
  have h2959 : mixedVector B (Sum.inr 2959) = Sparse.eval nodeValue2959 (mixedVector B) := by
    change mixedMoment B node2959 node2959Labels = _
    exact sound2959 B hB hF
  have h2960 : mixedVector B (Sum.inr 2960) = Sparse.eval nodeValue2960 (mixedVector B) := by
    change mixedMoment B node2960 node2960Labels = _
    exact sound2960 B hB hF
  have h3101 : mixedVector B (Sum.inr 3101) = Sparse.eval nodeValue3101 (mixedVector B) := by
    change mixedMoment B node3101 node3101Labels = _
    exact sound3101 B hB hF
  have h3122 : mixedVector B (Sum.inr 3122) = Sparse.eval nodeValue3122 (mixedVector B) := by
    change mixedMoment B node3122 node3122Labels = _
    exact sound3122 B hB hF
  have h3736 : mixedVector B (Sum.inr 3736) = Sparse.eval nodeValue3736 (mixedVector B) := by
    change mixedMoment B node3736 node3736Labels = _
    exact sound3736 B hB hF
  have h3823 : mixedVector B (Sum.inr 3823) = Sparse.eval nodeValue3823 (mixedVector B) := by
    change mixedMoment B node3823 node3823Labels = _
    exact sound3823 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853 B hB hF
  have h4036 : mixedVector B (Sum.inr 4036) = Sparse.eval nodeValue4036 (mixedVector B) := by
    change mixedMoment B node4036 node4036Labels = _
    exact sound4036 B hB hF
  simpa only [sourceForm2351, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1126, h1128, h1134, h1300, h1964, h1970, h2025, h2807, h2813, h2893, h2924, h2931, h2958, h2959, h2960, h3101, h3122, h3736, h3823, h3853, h4036, reducedSource1915] using sourceEq2351 B hB

theorem rowSound1915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1915 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1915, numericCheck1915, reducedZero1915 B hB hF, mul_zero]

theorem reducedZero1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1916 (mixedVector B) = 0 := by
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4947 : mixedVector B (Sum.inr 4947) = Sparse.eval nodeValue4947 (mixedVector B) := by
    change mixedMoment B node4947 node4947Labels = _
    exact sound4947 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h5037 : mixedVector B (Sum.inr 5037) = Sparse.eval nodeValue5037 (mixedVector B) := by
    change mixedMoment B node5037 node5037Labels = _
    exact sound5037 B hB hF
  have h5038 : mixedVector B (Sum.inr 5038) = Sparse.eval nodeValue5038 (mixedVector B) := by
    change mixedMoment B node5038 node5038Labels = _
    exact sound5038 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416 B hB hF
  have h5418 : mixedVector B (Sum.inr 5418) = Sparse.eval nodeValue5418 (mixedVector B) := by
    change mixedMoment B node5418 node5418Labels = _
    exact sound5418 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  simpa only [sourceForm2352, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4351, h4352, h4354, h4461, h4947, h4948, h4949, h5037, h5038, h5076, h5162, h5163, h5172, h5174, h5176, h5290, h5294, h5416, h5418, h5442, h5485, reducedSource1916] using sourceEq2352 B hB

theorem rowSound1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1916 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1916, numericCheck1916, reducedZero1916 B hB hF, mul_zero]

theorem reducedZero1917 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1917 (mixedVector B) = 0 := by
  have h929 : mixedVector B (Sum.inr 929) = Sparse.eval nodeValue929 (mixedVector B) := by
    change mixedMoment B node929 node929Labels = _
    exact sound929 B hB hF
  have h930 : mixedVector B (Sum.inr 930) = Sparse.eval nodeValue930 (mixedVector B) := by
    change mixedMoment B node930 node930Labels = _
    exact sound930 B hB hF
  have h932 : mixedVector B (Sum.inr 932) = Sparse.eval nodeValue932 (mixedVector B) := by
    change mixedMoment B node932 node932Labels = _
    exact sound932 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h2338 : mixedVector B (Sum.inr 2338) = Sparse.eval nodeValue2338 (mixedVector B) := by
    change mixedMoment B node2338 node2338Labels = _
    exact sound2338 B hB hF
  have h2339 : mixedVector B (Sum.inr 2339) = Sparse.eval nodeValue2339 (mixedVector B) := by
    change mixedMoment B node2339 node2339Labels = _
    exact sound2339 B hB hF
  have h2341 : mixedVector B (Sum.inr 2341) = Sparse.eval nodeValue2341 (mixedVector B) := by
    change mixedMoment B node2341 node2341Labels = _
    exact sound2341 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h2589 : mixedVector B (Sum.inr 2589) = Sparse.eval nodeValue2589 (mixedVector B) := by
    change mixedMoment B node2589 node2589Labels = _
    exact sound2589 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2599 : mixedVector B (Sum.inr 2599) = Sparse.eval nodeValue2599 (mixedVector B) := by
    change mixedMoment B node2599 node2599Labels = _
    exact sound2599 B hB hF
  have h2601 : mixedVector B (Sum.inr 2601) = Sparse.eval nodeValue2601 (mixedVector B) := by
    change mixedMoment B node2601 node2601Labels = _
    exact sound2601 B hB hF
  have h2604 : mixedVector B (Sum.inr 2604) = Sparse.eval nodeValue2604 (mixedVector B) := by
    change mixedMoment B node2604 node2604Labels = _
    exact sound2604 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h3933 : mixedVector B (Sum.inr 3933) = Sparse.eval nodeValue3933 (mixedVector B) := by
    change mixedMoment B node3933 node3933Labels = _
    exact sound3933 B hB hF
  have h3967 : mixedVector B (Sum.inr 3967) = Sparse.eval nodeValue3967 (mixedVector B) := by
    change mixedMoment B node3967 node3967Labels = _
    exact sound3967 B hB hF
  have h3998 : mixedVector B (Sum.inr 3998) = Sparse.eval nodeValue3998 (mixedVector B) := by
    change mixedMoment B node3998 node3998Labels = _
    exact sound3998 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  simpa only [sourceForm2353, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h929, h930, h932, h1044, h2338, h2339, h2341, h2429, h2431, h2483, h2589, h2590, h2599, h2601, h2604, h2764, h2768, h3933, h3967, h3998, h4001, reducedSource1917] using sourceEq2353 B hB

theorem rowSound1917 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1917 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1917, numericCheck1917, reducedZero1917 B hB hF, mul_zero]

theorem reducedZero1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1918 (mixedVector B) = 0 := by
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5187 : mixedVector B (Sum.inr 5187) = Sparse.eval nodeValue5187 (mixedVector B) := by
    change mixedMoment B node5187 node5187Labels = _
    exact sound5187 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5205 : mixedVector B (Sum.inr 5205) = Sparse.eval nodeValue5205 (mixedVector B) := by
    change mixedMoment B node5205 node5205Labels = _
    exact sound5205 B hB hF
  simpa only [sourceForm2354, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4805, h4838, h4839, h4869, h5072, h5076, h5099, h5101, h5104, h5105, h5137, h5138, h5149, h5150, h5168, h5169, h5170, h5173, h5187, h5204, h5205, reducedSource1918] using sourceEq2354 B hB

theorem rowSound1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1918 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1918, numericCheck1918, reducedZero1918 B hB hF, mul_zero]

theorem reducedZero1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1919 (mixedVector B) = 0 := by
  have h1156 : mixedVector B (Sum.inr 1156) = Sparse.eval nodeValue1156 (mixedVector B) := by
    change mixedMoment B node1156 node1156Labels = _
    exact sound1156 B hB hF
  have h2353 : mixedVector B (Sum.inr 2353) = Sparse.eval nodeValue2353 (mixedVector B) := by
    change mixedMoment B node2353 node2353Labels = _
    exact sound2353 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2355, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1156, h2353, h2553, h2566, h2587, h2590, h4092, reducedSource1919] using sourceEq2355 B hB

theorem rowSound1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1919 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1919, numericCheck1919, reducedZero1919 B hB hF, mul_zero]

theorem sourceRowsAt1904 : MixedData.sourceRows (1904 : Fin 2425) =
    MixedData.row1904 := by decide +kernel

theorem sourceRowsAt1905 : MixedData.sourceRows (1905 : Fin 2425) =
    MixedData.row1905 := by decide +kernel

theorem sourceRowsAt1906 : MixedData.sourceRows (1906 : Fin 2425) =
    MixedData.row1906 := by decide +kernel

theorem sourceRowsAt1907 : MixedData.sourceRows (1907 : Fin 2425) =
    MixedData.row1907 := by decide +kernel

theorem sourceRowsAt1908 : MixedData.sourceRows (1908 : Fin 2425) =
    MixedData.row1908 := by decide +kernel

theorem sourceRowsAt1909 : MixedData.sourceRows (1909 : Fin 2425) =
    MixedData.row1909 := by decide +kernel

theorem sourceRowsAt1910 : MixedData.sourceRows (1910 : Fin 2425) =
    MixedData.row1910 := by decide +kernel

theorem sourceRowsAt1911 : MixedData.sourceRows (1911 : Fin 2425) =
    MixedData.row1911 := by decide +kernel

theorem sourceRowsAt1912 : MixedData.sourceRows (1912 : Fin 2425) =
    MixedData.row1912 := by decide +kernel

theorem sourceRowsAt1913 : MixedData.sourceRows (1913 : Fin 2425) =
    MixedData.row1913 := by decide +kernel

theorem sourceRowsAt1914 : MixedData.sourceRows (1914 : Fin 2425) =
    MixedData.row1914 := by decide +kernel

theorem sourceRowsAt1915 : MixedData.sourceRows (1915 : Fin 2425) =
    MixedData.row1915 := by decide +kernel

theorem sourceRowsAt1916 : MixedData.sourceRows (1916 : Fin 2425) =
    MixedData.row1916 := by decide +kernel

theorem sourceRowsAt1917 : MixedData.sourceRows (1917 : Fin 2425) =
    MixedData.row1917 := by decide +kernel

theorem sourceRowsAt1918 : MixedData.sourceRows (1918 : Fin 2425) =
    MixedData.row1918 := by decide +kernel

theorem sourceRowsAt1919 : MixedData.sourceRows (1919 : Fin 2425) =
    MixedData.row1919 := by decide +kernel

theorem chunkSound119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 119) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1904 ∨ k.val = 1905 ∨ k.val = 1906 ∨ k.val = 1907 ∨ k.val = 1908 ∨ k.val = 1909 ∨ k.val = 1910 ∨ k.val = 1911 ∨ k.val = 1912 ∨ k.val = 1913 ∨ k.val = 1914 ∨ k.val = 1915 ∨ k.val = 1916 ∨ k.val = 1917 ∨ k.val = 1918 ∨ k.val = 1919 := by omega
  rcases heq with h1904 | h1905 | h1906 | h1907 | h1908 | h1909 | h1910 | h1911 | h1912 | h1913 | h1914 | h1915 | h1916 | h1917 | h1918 | h1919
  · have he : k = (1904 : Fin 2425) := Fin.ext h1904
    subst k
    rw [sourceRowsAt1904]
    exact rowSound1904 B hB hF
  · have he : k = (1905 : Fin 2425) := Fin.ext h1905
    subst k
    rw [sourceRowsAt1905]
    exact rowSound1905 B hB hF
  · have he : k = (1906 : Fin 2425) := Fin.ext h1906
    subst k
    rw [sourceRowsAt1906]
    exact rowSound1906 B hB hF
  · have he : k = (1907 : Fin 2425) := Fin.ext h1907
    subst k
    rw [sourceRowsAt1907]
    exact rowSound1907 B hB hF
  · have he : k = (1908 : Fin 2425) := Fin.ext h1908
    subst k
    rw [sourceRowsAt1908]
    exact rowSound1908 B hB hF
  · have he : k = (1909 : Fin 2425) := Fin.ext h1909
    subst k
    rw [sourceRowsAt1909]
    exact rowSound1909 B hB hF
  · have he : k = (1910 : Fin 2425) := Fin.ext h1910
    subst k
    rw [sourceRowsAt1910]
    exact rowSound1910 B hB hF
  · have he : k = (1911 : Fin 2425) := Fin.ext h1911
    subst k
    rw [sourceRowsAt1911]
    exact rowSound1911 B hB hF
  · have he : k = (1912 : Fin 2425) := Fin.ext h1912
    subst k
    rw [sourceRowsAt1912]
    exact rowSound1912 B hB hF
  · have he : k = (1913 : Fin 2425) := Fin.ext h1913
    subst k
    rw [sourceRowsAt1913]
    exact rowSound1913 B hB hF
  · have he : k = (1914 : Fin 2425) := Fin.ext h1914
    subst k
    rw [sourceRowsAt1914]
    exact rowSound1914 B hB hF
  · have he : k = (1915 : Fin 2425) := Fin.ext h1915
    subst k
    rw [sourceRowsAt1915]
    exact rowSound1915 B hB hF
  · have he : k = (1916 : Fin 2425) := Fin.ext h1916
    subst k
    rw [sourceRowsAt1916]
    exact rowSound1916 B hB hF
  · have he : k = (1917 : Fin 2425) := Fin.ext h1917
    subst k
    rw [sourceRowsAt1917]
    exact rowSound1917 B hB hF
  · have he : k = (1918 : Fin 2425) := Fin.ext h1918
    subst k
    rw [sourceRowsAt1918]
    exact rowSound1918 B hB hF
  · have he : k = (1919 : Fin 2425) := Fin.ext h1919
    subst k
    rw [sourceRowsAt1919]
    exact rowSound1919 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
