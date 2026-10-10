import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic107
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources64

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1712 (mixedVector B) = 0 := by
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h2325 : mixedVector B (Sum.inr 2325) = Sparse.eval nodeValue2325 (mixedVector B) := by
    change mixedMoment B node2325 node2325Labels = _
    exact sound2325 B hB hF
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2355 : mixedVector B (Sum.inr 2355) = Sparse.eval nodeValue2355 (mixedVector B) := by
    change mixedMoment B node2355 node2355Labels = _
    exact sound2355 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2033, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1119, h2325, h2347, h2355, h2482, h2488, h4092, reducedSource1712] using sourceEq2033 B hB

theorem rowSound1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1712 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1712, numericCheck1712, reducedZero1712 B hB hF, mul_zero]

theorem reducedZero1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1713 (mixedVector B) = 0 := by
  have h1111 : mixedVector B (Sum.inr 1111) = Sparse.eval nodeValue1111 (mixedVector B) := by
    change mixedMoment B node1111 node1111Labels = _
    exact sound1111 B hB hF
  have h2319 : mixedVector B (Sum.inr 2319) = Sparse.eval nodeValue2319 (mixedVector B) := by
    change mixedMoment B node2319 node2319Labels = _
    exact sound2319 B hB hF
  have h2436 : mixedVector B (Sum.inr 2436) = Sparse.eval nodeValue2436 (mixedVector B) := by
    change mixedMoment B node2436 node2436Labels = _
    exact sound2436 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2034, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1111, h2319, h2436, h2479, h2482, h4092, reducedSource1713] using sourceEq2034 B hB

theorem rowSound1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1713 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1713, numericCheck1713, reducedZero1713 B hB hF, mul_zero]

theorem reducedZero1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1714 (mixedVector B) = 0 := by
  have h1131 : mixedVector B (Sum.inr 1131) = Sparse.eval nodeValue1131 (mixedVector B) := by
    change mixedMoment B node1131 node1131Labels = _
    exact sound1131 B hB hF
  have h2334 : mixedVector B (Sum.inr 2334) = Sparse.eval nodeValue2334 (mixedVector B) := by
    change mixedMoment B node2334 node2334Labels = _
    exact sound2334 B hB hF
  have h2425 : mixedVector B (Sum.inr 2425) = Sparse.eval nodeValue2425 (mixedVector B) := by
    change mixedMoment B node2425 node2425Labels = _
    exact sound2425 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2511 : mixedVector B (Sum.inr 2511) = Sparse.eval nodeValue2511 (mixedVector B) := by
    change mixedMoment B node2511 node2511Labels = _
    exact sound2511 B hB hF
  have h2517 : mixedVector B (Sum.inr 2517) = Sparse.eval nodeValue2517 (mixedVector B) := by
    change mixedMoment B node2517 node2517Labels = _
    exact sound2517 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2035, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1131, h2334, h2425, h2482, h2511, h2517, h4092, reducedSource1714] using sourceEq2035 B hB

theorem rowSound1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1714 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1714, numericCheck1714, reducedZero1714 B hB hF, mul_zero]

theorem reducedZero1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1715 (mixedVector B) = 0 := by
  have h4287 : mixedVector B (Sum.inr 4287) = Sparse.eval nodeValue4287 (mixedVector B) := by
    change mixedMoment B node4287 node4287Labels = _
    exact sound4287 B hB hF
  have h4289 : mixedVector B (Sum.inr 4289) = Sparse.eval nodeValue4289 (mixedVector B) := by
    change mixedMoment B node4289 node4289Labels = _
    exact sound4289 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4303 : mixedVector B (Sum.inr 4303) = Sparse.eval nodeValue4303 (mixedVector B) := by
    change mixedMoment B node4303 node4303Labels = _
    exact sound4303 B hB hF
  have h4322 : mixedVector B (Sum.inr 4322) = Sparse.eval nodeValue4322 (mixedVector B) := by
    change mixedMoment B node4322 node4322Labels = _
    exact sound4322 B hB hF
  have h4325 : mixedVector B (Sum.inr 4325) = Sparse.eval nodeValue4325 (mixedVector B) := by
    change mixedMoment B node4325 node4325Labels = _
    exact sound4325 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4902 : mixedVector B (Sum.inr 4902) = Sparse.eval nodeValue4902 (mixedVector B) := by
    change mixedMoment B node4902 node4902Labels = _
    exact sound4902 B hB hF
  have h4907 : mixedVector B (Sum.inr 4907) = Sparse.eval nodeValue4907 (mixedVector B) := by
    change mixedMoment B node4907 node4907Labels = _
    exact sound4907 B hB hF
  have h4913 : mixedVector B (Sum.inr 4913) = Sparse.eval nodeValue4913 (mixedVector B) := by
    change mixedMoment B node4913 node4913Labels = _
    exact sound4913 B hB hF
  have h4927 : mixedVector B (Sum.inr 4927) = Sparse.eval nodeValue4927 (mixedVector B) := by
    change mixedMoment B node4927 node4927Labels = _
    exact sound4927 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4986 : mixedVector B (Sum.inr 4986) = Sparse.eval nodeValue4986 (mixedVector B) := by
    change mixedMoment B node4986 node4986Labels = _
    exact sound4986 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5033 : mixedVector B (Sum.inr 5033) = Sparse.eval nodeValue5033 (mixedVector B) := by
    change mixedMoment B node5033 node5033Labels = _
    exact sound5033 B hB hF
  have h5047 : mixedVector B (Sum.inr 5047) = Sparse.eval nodeValue5047 (mixedVector B) := by
    change mixedMoment B node5047 node5047Labels = _
    exact sound5047 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169 B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483 B hB hF
  simpa only [sourceForm2036, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4287, h4289, h4295, h4303, h4322, h4325, h4346, h4401, h4460, h4902, h4907, h4913, h4927, h4943, h4986, h5000, h5033, h5047, h5073, h5075, h5081, h5102, h5137, h5141, h5169, h5171, h5259, h5261, h5293, h5483, reducedSource1715] using sourceEq2036 B hB

theorem rowSound1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1715 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1715, numericCheck1715, reducedZero1715 B hB hF, mul_zero]

theorem reducedZero1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1716 (mixedVector B) = 0 := by
  have h4326 : mixedVector B (Sum.inr 4326) = Sparse.eval nodeValue4326 (mixedVector B) := by
    change mixedMoment B node4326 node4326Labels = _
    exact sound4326 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4532 : mixedVector B (Sum.inr 4532) = Sparse.eval nodeValue4532 (mixedVector B) := by
    change mixedMoment B node4532 node4532Labels = _
    exact sound4532 B hB hF
  have h4536 : mixedVector B (Sum.inr 4536) = Sparse.eval nodeValue4536 (mixedVector B) := by
    change mixedMoment B node4536 node4536Labels = _
    exact sound4536 B hB hF
  have h4552 : mixedVector B (Sum.inr 4552) = Sparse.eval nodeValue4552 (mixedVector B) := by
    change mixedMoment B node4552 node4552Labels = _
    exact sound4552 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4663 : mixedVector B (Sum.inr 4663) = Sparse.eval nodeValue4663 (mixedVector B) := by
    change mixedMoment B node4663 node4663Labels = _
    exact sound4663 B hB hF
  have h4669 : mixedVector B (Sum.inr 4669) = Sparse.eval nodeValue4669 (mixedVector B) := by
    change mixedMoment B node4669 node4669Labels = _
    exact sound4669 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4756 : mixedVector B (Sum.inr 4756) = Sparse.eval nodeValue4756 (mixedVector B) := by
    change mixedMoment B node4756 node4756Labels = _
    exact sound4756 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4771 : mixedVector B (Sum.inr 4771) = Sparse.eval nodeValue4771 (mixedVector B) := by
    change mixedMoment B node4771 node4771Labels = _
    exact sound4771 B hB hF
  have h4776 : mixedVector B (Sum.inr 4776) = Sparse.eval nodeValue4776 (mixedVector B) := by
    change mixedMoment B node4776 node4776Labels = _
    exact sound4776 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5133 : mixedVector B (Sum.inr 5133) = Sparse.eval nodeValue5133 (mixedVector B) := by
    change mixedMoment B node5133 node5133Labels = _
    exact sound5133 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5161 : mixedVector B (Sum.inr 5161) = Sparse.eval nodeValue5161 (mixedVector B) := by
    change mixedMoment B node5161 node5161Labels = _
    exact sound5161 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  simpa only [sourceForm2039, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4326, h4330, h4334, h4346, h4460, h4532, h4536, h4552, h4605, h4663, h4669, h4681, h4756, h4760, h4771, h4776, h4801, h4804, h4810, h4834, h4841, h4868, h4894, h4897, h5133, h5140, h5161, h5258, h5272, reducedSource1716] using sourceEq2039 B hB

theorem rowSound1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1716 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1716, numericCheck1716, reducedZero1716 B hB hF, mul_zero]

theorem reducedZero1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1717 (mixedVector B) = 0 := by
  have h1116 : mixedVector B (Sum.inr 1116) = Sparse.eval nodeValue1116 (mixedVector B) := by
    change mixedMoment B node1116 node1116Labels = _
    exact sound1116 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1121 : mixedVector B (Sum.inr 1121) = Sparse.eval nodeValue1121 (mixedVector B) := by
    change mixedMoment B node1121 node1121Labels = _
    exact sound1121 B hB hF
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1329 : mixedVector B (Sum.inr 1329) = Sparse.eval nodeValue1329 (mixedVector B) := by
    change mixedMoment B node1329 node1329Labels = _
    exact sound1329 B hB hF
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h1342 : mixedVector B (Sum.inr 1342) = Sparse.eval nodeValue1342 (mixedVector B) := by
    change mixedMoment B node1342 node1342Labels = _
    exact sound1342 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h2800 : mixedVector B (Sum.inr 2800) = Sparse.eval nodeValue2800 (mixedVector B) := by
    change mixedMoment B node2800 node2800Labels = _
    exact sound2800 B hB hF
  have h2803 : mixedVector B (Sum.inr 2803) = Sparse.eval nodeValue2803 (mixedVector B) := by
    change mixedMoment B node2803 node2803Labels = _
    exact sound2803 B hB hF
  have h2816 : mixedVector B (Sum.inr 2816) = Sparse.eval nodeValue2816 (mixedVector B) := by
    change mixedMoment B node2816 node2816Labels = _
    exact sound2816 B hB hF
  have h2890 : mixedVector B (Sum.inr 2890) = Sparse.eval nodeValue2890 (mixedVector B) := by
    change mixedMoment B node2890 node2890Labels = _
    exact sound2890 B hB hF
  have h2895 : mixedVector B (Sum.inr 2895) = Sparse.eval nodeValue2895 (mixedVector B) := by
    change mixedMoment B node2895 node2895Labels = _
    exact sound2895 B hB hF
  have h2901 : mixedVector B (Sum.inr 2901) = Sparse.eval nodeValue2901 (mixedVector B) := by
    change mixedMoment B node2901 node2901Labels = _
    exact sound2901 B hB hF
  have h2904 : mixedVector B (Sum.inr 2904) = Sparse.eval nodeValue2904 (mixedVector B) := by
    change mixedMoment B node2904 node2904Labels = _
    exact sound2904 B hB hF
  have h2940 : mixedVector B (Sum.inr 2940) = Sparse.eval nodeValue2940 (mixedVector B) := by
    change mixedMoment B node2940 node2940Labels = _
    exact sound2940 B hB hF
  have h2941 : mixedVector B (Sum.inr 2941) = Sparse.eval nodeValue2941 (mixedVector B) := by
    change mixedMoment B node2941 node2941Labels = _
    exact sound2941 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2964 : mixedVector B (Sum.inr 2964) = Sparse.eval nodeValue2964 (mixedVector B) := by
    change mixedMoment B node2964 node2964Labels = _
    exact sound2964 B hB hF
  have h2966 : mixedVector B (Sum.inr 2966) = Sparse.eval nodeValue2966 (mixedVector B) := by
    change mixedMoment B node2966 node2966Labels = _
    exact sound2966 B hB hF
  have h3004 : mixedVector B (Sum.inr 3004) = Sparse.eval nodeValue3004 (mixedVector B) := by
    change mixedMoment B node3004 node3004Labels = _
    exact sound3004 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3113 : mixedVector B (Sum.inr 3113) = Sparse.eval nodeValue3113 (mixedVector B) := by
    change mixedMoment B node3113 node3113Labels = _
    exact sound3113 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  have h3205 : mixedVector B (Sum.inr 3205) = Sparse.eval nodeValue3205 (mixedVector B) := by
    change mixedMoment B node3205 node3205Labels = _
    exact sound3205 B hB hF
  have h3206 : mixedVector B (Sum.inr 3206) = Sparse.eval nodeValue3206 (mixedVector B) := by
    change mixedMoment B node3206 node3206Labels = _
    exact sound3206 B hB hF
  have h3214 : mixedVector B (Sum.inr 3214) = Sparse.eval nodeValue3214 (mixedVector B) := by
    change mixedMoment B node3214 node3214Labels = _
    exact sound3214 B hB hF
  have h3230 : mixedVector B (Sum.inr 3230) = Sparse.eval nodeValue3230 (mixedVector B) := by
    change mixedMoment B node3230 node3230Labels = _
    exact sound3230 B hB hF
  simpa only [sourceForm2040, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1116, h1118, h1121, h1137, h1271, h1329, h1334, h1342, h1416, h2800, h2803, h2816, h2890, h2895, h2901, h2904, h2940, h2941, h2942, h2964, h2966, h3004, h3089, h3113, h3114, h3205, h3206, h3214, h3230, reducedSource1717] using sourceEq2040 B hB

theorem rowSound1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1717 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1717, numericCheck1717, reducedZero1717 B hB hF, mul_zero]

theorem reducedZero1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1718 (mixedVector B) = 0 := by
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h2140 : mixedVector B (Sum.inr 2140) = Sparse.eval nodeValue2140 (mixedVector B) := by
    change mixedMoment B node2140 node2140Labels = _
    exact sound2140 B hB hF
  have h2149 : mixedVector B (Sum.inr 2149) = Sparse.eval nodeValue2149 (mixedVector B) := by
    change mixedMoment B node2149 node2149Labels = _
    exact sound2149 B hB hF
  have h2151 : mixedVector B (Sum.inr 2151) = Sparse.eval nodeValue2151 (mixedVector B) := by
    change mixedMoment B node2151 node2151Labels = _
    exact sound2151 B hB hF
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2172 : mixedVector B (Sum.inr 2172) = Sparse.eval nodeValue2172 (mixedVector B) := by
    change mixedMoment B node2172 node2172Labels = _
    exact sound2172 B hB hF
  have h2173 : mixedVector B (Sum.inr 2173) = Sparse.eval nodeValue2173 (mixedVector B) := by
    change mixedMoment B node2173 node2173Labels = _
    exact sound2173 B hB hF
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2189 : mixedVector B (Sum.inr 2189) = Sparse.eval nodeValue2189 (mixedVector B) := by
    change mixedMoment B node2189 node2189Labels = _
    exact sound2189 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2200 : mixedVector B (Sum.inr 2200) = Sparse.eval nodeValue2200 (mixedVector B) := by
    change mixedMoment B node2200 node2200Labels = _
    exact sound2200 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  simpa only [sourceForm2041, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1663, h1672, h1674, h1679, h1725, h2140, h2149, h2151, h2155, h2172, h2173, h2176, h2189, h2190, h2200, h2203, h2205, h2212, h2215, h2226, h2228, h2261, h2264, h2292, h2670, h2693, h2719, h2722, h2740, reducedSource1718] using sourceEq2041 B hB

theorem rowSound1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1718 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1718, numericCheck1718, reducedZero1718 B hB hF, mul_zero]

theorem reducedZero1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1719 (mixedVector B) = 0 := by
  have h912 : mixedVector B (Sum.inr 912) = Sparse.eval nodeValue912 (mixedVector B) := by
    change mixedMoment B node912 node912Labels = _
    exact sound912 B hB hF
  have h1795 : mixedVector B (Sum.inr 1795) = Sparse.eval nodeValue1795 (mixedVector B) := by
    change mixedMoment B node1795 node1795Labels = _
    exact sound1795 B hB hF
  have h1955 : mixedVector B (Sum.inr 1955) = Sparse.eval nodeValue1955 (mixedVector B) := by
    change mixedMoment B node1955 node1955Labels = _
    exact sound1955 B hB hF
  have h1978 : mixedVector B (Sum.inr 1978) = Sparse.eval nodeValue1978 (mixedVector B) := by
    change mixedMoment B node1978 node1978Labels = _
    exact sound1978 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2042, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h912, h1795, h1955, h1978, h2022, h2028, h4084, reducedSource1719] using sourceEq2042 B hB

theorem rowSound1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1719 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1719, numericCheck1719, reducedZero1719 B hB hF, mul_zero]

theorem reducedZero1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1720 (mixedVector B) = 0 := by
  have h1147 : mixedVector B (Sum.inr 1147) = Sparse.eval nodeValue1147 (mixedVector B) := by
    change mixedMoment B node1147 node1147Labels = _
    exact sound1147 B hB hF
  have h1955 : mixedVector B (Sum.inr 1955) = Sparse.eval nodeValue1955 (mixedVector B) := by
    change mixedMoment B node1955 node1955Labels = _
    exact sound1955 B hB hF
  have h1960 : mixedVector B (Sum.inr 1960) = Sparse.eval nodeValue1960 (mixedVector B) := by
    change mixedMoment B node1960 node1960Labels = _
    exact sound1960 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2043, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1147, h1955, h1960, h2022, h2552, h4084, reducedSource1720] using sourceEq2043 B hB

theorem rowSound1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1720 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1720, numericCheck1720, reducedZero1720 B hB hF, mul_zero]

theorem reducedZero1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1721 (mixedVector B) = 0 := by
  have h904 : mixedVector B (Sum.inr 904) = Sparse.eval nodeValue904 (mixedVector B) := by
    change mixedMoment B node904 node904Labels = _
    exact sound904 B hB hF
  have h1789 : mixedVector B (Sum.inr 1789) = Sparse.eval nodeValue1789 (mixedVector B) := by
    change mixedMoment B node1789 node1789Labels = _
    exact sound1789 B hB hF
  have h1972 : mixedVector B (Sum.inr 1972) = Sparse.eval nodeValue1972 (mixedVector B) := by
    change mixedMoment B node1972 node1972Labels = _
    exact sound1972 B hB hF
  have h2019 : mixedVector B (Sum.inr 2019) = Sparse.eval nodeValue2019 (mixedVector B) := by
    change mixedMoment B node2019 node2019Labels = _
    exact sound2019 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2044, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h904, h1789, h1972, h2019, h2022, h4084, reducedSource1721] using sourceEq2044 B hB

theorem rowSound1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1721 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1721, numericCheck1721, reducedZero1721 B hB hF, mul_zero]

theorem reducedZero1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1722 (mixedVector B) = 0 := by
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h1807 : mixedVector B (Sum.inr 1807) = Sparse.eval nodeValue1807 (mixedVector B) := by
    change mixedMoment B node1807 node1807Labels = _
    exact sound1807 B hB hF
  have h1960 : mixedVector B (Sum.inr 1960) = Sparse.eval nodeValue1960 (mixedVector B) := by
    change mixedMoment B node1960 node1960Labels = _
    exact sound1960 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2053 : mixedVector B (Sum.inr 2053) = Sparse.eval nodeValue2053 (mixedVector B) := by
    change mixedMoment B node2053 node2053Labels = _
    exact sound2053 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2045, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h924, h1807, h1960, h2022, h2053, h2060, h4084, reducedSource1722] using sourceEq2045 B hB

theorem rowSound1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1722 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1722, numericCheck1722, reducedZero1722 B hB hF, mul_zero]

theorem reducedZero1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1723 (mixedVector B) = 0 := by
  have h4196 : mixedVector B (Sum.inr 4196) = Sparse.eval nodeValue4196 (mixedVector B) := by
    change mixedMoment B node4196 node4196Labels = _
    exact sound4196 B hB hF
  have h4198 : mixedVector B (Sum.inr 4198) = Sparse.eval nodeValue4198 (mixedVector B) := by
    change mixedMoment B node4198 node4198Labels = _
    exact sound4198 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4212 : mixedVector B (Sum.inr 4212) = Sparse.eval nodeValue4212 (mixedVector B) := by
    change mixedMoment B node4212 node4212Labels = _
    exact sound4212 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4320 : mixedVector B (Sum.inr 4320) = Sparse.eval nodeValue4320 (mixedVector B) := by
    change mixedMoment B node4320 node4320Labels = _
    exact sound4320 B hB hF
  have h4324 : mixedVector B (Sum.inr 4324) = Sparse.eval nodeValue4324 (mixedVector B) := by
    change mixedMoment B node4324 node4324Labels = _
    exact sound4324 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4709 : mixedVector B (Sum.inr 4709) = Sparse.eval nodeValue4709 (mixedVector B) := by
    change mixedMoment B node4709 node4709Labels = _
    exact sound4709 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434 B hB hF
  simpa only [sourceForm2046, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4196, h4198, h4204, h4212, h4251, h4320, h4324, h4343, h4398, h4631, h4637, h4644, h4706, h4709, h4728, h4760, h4769, h4779, h4788, h4802, h4804, h4811, h4832, h4835, h4888, h5134, h5141, h5168, h5258, h5434, reducedSource1723] using sourceEq2046 B hB

theorem rowSound1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1723 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1723, numericCheck1723, reducedZero1723 B hB hF, mul_zero]

theorem reducedZero1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1724 (mixedVector B) = 0 := by
  have h2391 : mixedVector B (Sum.inr 2391) = Sparse.eval nodeValue2391 (mixedVector B) := by
    change mixedMoment B node2391 node2391Labels = _
    exact sound2391 B hB hF
  have h2535 : mixedVector B (Sum.inr 2535) = Sparse.eval nodeValue2535 (mixedVector B) := by
    change mixedMoment B node2535 node2535Labels = _
    exact sound2535 B hB hF
  have h2539 : mixedVector B (Sum.inr 2539) = Sparse.eval nodeValue2539 (mixedVector B) := by
    change mixedMoment B node2539 node2539Labels = _
    exact sound2539 B hB hF
  have h2585 : mixedVector B (Sum.inr 2585) = Sparse.eval nodeValue2585 (mixedVector B) := by
    change mixedMoment B node2585 node2585Labels = _
    exact sound2585 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h3770 : mixedVector B (Sum.inr 3770) = Sparse.eval nodeValue3770 (mixedVector B) := by
    change mixedMoment B node3770 node3770Labels = _
    exact sound3770 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm2051, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2391, h2535, h2539, h2585, h2686, h3770, h4089, reducedSource1724] using sourceEq2051 B hB

theorem rowSound1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1724 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1724, numericCheck1724, reducedZero1724 B hB hF, mul_zero]

theorem reducedZero1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1725 (mixedVector B) = 0 := by
  have h1921 : mixedVector B (Sum.inr 1921) = Sparse.eval nodeValue1921 (mixedVector B) := by
    change mixedMoment B node1921 node1921Labels = _
    exact sound1921 B hB hF
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h1945 : mixedVector B (Sum.inr 1945) = Sparse.eval nodeValue1945 (mixedVector B) := by
    change mixedMoment B node1945 node1945Labels = _
    exact sound1945 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2052, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1921, h1924, h1928, h1945, h2215, h3478, h4082, reducedSource1725] using sourceEq2052 B hB

theorem rowSound1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1725 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1725, numericCheck1725, reducedZero1725 B hB hF, mul_zero]

theorem reducedZero1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1726 (mixedVector B) = 0 := by
  have h1924 : mixedVector B (Sum.inr 1924) = Sparse.eval nodeValue1924 (mixedVector B) := by
    change mixedMoment B node1924 node1924Labels = _
    exact sound1924 B hB hF
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h2538 : mixedVector B (Sum.inr 2538) = Sparse.eval nodeValue2538 (mixedVector B) := by
    change mixedMoment B node2538 node2538Labels = _
    exact sound2538 B hB hF
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2054, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1924, h2534, h2538, h2584, h2685, h3478, h4082, reducedSource1726] using sourceEq2054 B hB

theorem rowSound1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1726 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1726, numericCheck1726, reducedZero1726 B hB hF, mul_zero]

theorem reducedZero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1727 (mixedVector B) = 0 := by
  have h2377 : mixedVector B (Sum.inr 2377) = Sparse.eval nodeValue2377 (mixedVector B) := by
    change mixedMoment B node2377 node2377Labels = _
    exact sound2377 B hB hF
  have h2379 : mixedVector B (Sum.inr 2379) = Sparse.eval nodeValue2379 (mixedVector B) := by
    change mixedMoment B node2379 node2379Labels = _
    exact sound2379 B hB hF
  have h2382 : mixedVector B (Sum.inr 2382) = Sparse.eval nodeValue2382 (mixedVector B) := by
    change mixedMoment B node2382 node2382Labels = _
    exact sound2382 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm2056, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2377, h2379, h2382, h2661, h3757, h4088, reducedSource1727] using sourceEq2056 B hB

theorem rowSound1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1727 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1727, numericCheck1727, reducedZero1727 B hB hF, mul_zero]

theorem sourceRowsAt1712 : MixedData.sourceRows (1712 : Fin 2425) =
    MixedData.row1712 := by decide +kernel

theorem sourceRowsAt1713 : MixedData.sourceRows (1713 : Fin 2425) =
    MixedData.row1713 := by decide +kernel

theorem sourceRowsAt1714 : MixedData.sourceRows (1714 : Fin 2425) =
    MixedData.row1714 := by decide +kernel

theorem sourceRowsAt1715 : MixedData.sourceRows (1715 : Fin 2425) =
    MixedData.row1715 := by decide +kernel

theorem sourceRowsAt1716 : MixedData.sourceRows (1716 : Fin 2425) =
    MixedData.row1716 := by decide +kernel

theorem sourceRowsAt1717 : MixedData.sourceRows (1717 : Fin 2425) =
    MixedData.row1717 := by decide +kernel

theorem sourceRowsAt1718 : MixedData.sourceRows (1718 : Fin 2425) =
    MixedData.row1718 := by decide +kernel

theorem sourceRowsAt1719 : MixedData.sourceRows (1719 : Fin 2425) =
    MixedData.row1719 := by decide +kernel

theorem sourceRowsAt1720 : MixedData.sourceRows (1720 : Fin 2425) =
    MixedData.row1720 := by decide +kernel

theorem sourceRowsAt1721 : MixedData.sourceRows (1721 : Fin 2425) =
    MixedData.row1721 := by decide +kernel

theorem sourceRowsAt1722 : MixedData.sourceRows (1722 : Fin 2425) =
    MixedData.row1722 := by decide +kernel

theorem sourceRowsAt1723 : MixedData.sourceRows (1723 : Fin 2425) =
    MixedData.row1723 := by decide +kernel

theorem sourceRowsAt1724 : MixedData.sourceRows (1724 : Fin 2425) =
    MixedData.row1724 := by decide +kernel

theorem sourceRowsAt1725 : MixedData.sourceRows (1725 : Fin 2425) =
    MixedData.row1725 := by decide +kernel

theorem sourceRowsAt1726 : MixedData.sourceRows (1726 : Fin 2425) =
    MixedData.row1726 := by decide +kernel

theorem sourceRowsAt1727 : MixedData.sourceRows (1727 : Fin 2425) =
    MixedData.row1727 := by decide +kernel

theorem chunkSound107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 107) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1712 ∨ k.val = 1713 ∨ k.val = 1714 ∨ k.val = 1715 ∨ k.val = 1716 ∨ k.val = 1717 ∨ k.val = 1718 ∨ k.val = 1719 ∨ k.val = 1720 ∨ k.val = 1721 ∨ k.val = 1722 ∨ k.val = 1723 ∨ k.val = 1724 ∨ k.val = 1725 ∨ k.val = 1726 ∨ k.val = 1727 := by omega
  rcases heq with h1712 | h1713 | h1714 | h1715 | h1716 | h1717 | h1718 | h1719 | h1720 | h1721 | h1722 | h1723 | h1724 | h1725 | h1726 | h1727
  · have he : k = (1712 : Fin 2425) := Fin.ext h1712
    subst k
    rw [sourceRowsAt1712]
    exact rowSound1712 B hB hF
  · have he : k = (1713 : Fin 2425) := Fin.ext h1713
    subst k
    rw [sourceRowsAt1713]
    exact rowSound1713 B hB hF
  · have he : k = (1714 : Fin 2425) := Fin.ext h1714
    subst k
    rw [sourceRowsAt1714]
    exact rowSound1714 B hB hF
  · have he : k = (1715 : Fin 2425) := Fin.ext h1715
    subst k
    rw [sourceRowsAt1715]
    exact rowSound1715 B hB hF
  · have he : k = (1716 : Fin 2425) := Fin.ext h1716
    subst k
    rw [sourceRowsAt1716]
    exact rowSound1716 B hB hF
  · have he : k = (1717 : Fin 2425) := Fin.ext h1717
    subst k
    rw [sourceRowsAt1717]
    exact rowSound1717 B hB hF
  · have he : k = (1718 : Fin 2425) := Fin.ext h1718
    subst k
    rw [sourceRowsAt1718]
    exact rowSound1718 B hB hF
  · have he : k = (1719 : Fin 2425) := Fin.ext h1719
    subst k
    rw [sourceRowsAt1719]
    exact rowSound1719 B hB hF
  · have he : k = (1720 : Fin 2425) := Fin.ext h1720
    subst k
    rw [sourceRowsAt1720]
    exact rowSound1720 B hB hF
  · have he : k = (1721 : Fin 2425) := Fin.ext h1721
    subst k
    rw [sourceRowsAt1721]
    exact rowSound1721 B hB hF
  · have he : k = (1722 : Fin 2425) := Fin.ext h1722
    subst k
    rw [sourceRowsAt1722]
    exact rowSound1722 B hB hF
  · have he : k = (1723 : Fin 2425) := Fin.ext h1723
    subst k
    rw [sourceRowsAt1723]
    exact rowSound1723 B hB hF
  · have he : k = (1724 : Fin 2425) := Fin.ext h1724
    subst k
    rw [sourceRowsAt1724]
    exact rowSound1724 B hB hF
  · have he : k = (1725 : Fin 2425) := Fin.ext h1725
    subst k
    rw [sourceRowsAt1725]
    exact rowSound1725 B hB hF
  · have he : k = (1726 : Fin 2425) := Fin.ext h1726
    subst k
    rw [sourceRowsAt1726]
    exact rowSound1726 B hB hF
  · have he : k = (1727 : Fin 2425) := Fin.ext h1727
    subst k
    rw [sourceRowsAt1727]
    exact rowSound1727 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
