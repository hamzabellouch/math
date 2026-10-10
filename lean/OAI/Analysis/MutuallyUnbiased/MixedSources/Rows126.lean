import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources78

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2016 (mixedVector B) = 0 := by
  have h4540 : mixedVector B (Sum.inr 4540) = Sparse.eval nodeValue4540 (mixedVector B) := by
    change mixedMoment B node4540 node4540Labels = _
    exact sound4540 B hB hF
  have h4542 : mixedVector B (Sum.inr 4542) = Sparse.eval nodeValue4542 (mixedVector B) := by
    change mixedMoment B node4542 node4542Labels = _
    exact sound4542 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h4964 : mixedVector B (Sum.inr 4964) = Sparse.eval nodeValue4964 (mixedVector B) := by
    change mixedMoment B node4964 node4964Labels = _
    exact sound4964 B hB hF
  have h4975 : mixedVector B (Sum.inr 4975) = Sparse.eval nodeValue4975 (mixedVector B) := by
    change mixedMoment B node4975 node4975Labels = _
    exact sound4975 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5427 : mixedVector B (Sum.inr 5427) = Sparse.eval nodeValue5427 (mixedVector B) := by
    change mixedMoment B node5427 node5427Labels = _
    exact sound5427 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  simpa only [sourceForm2502, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4540, h4542, h4618, h4964, h4975, h5137, h5145, h5150, h5273, h5290, h5383, h5427, h5431, reducedSource2016] using sourceEq2502 B hB

theorem rowSound2016 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2016 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2016, numericCheck2016, reducedZero2016 B hB hF, mul_zero]

theorem reducedZero2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2017 (mixedVector B) = 0 := by
  have h2688 : mixedVector B (Sum.inr 2688) = Sparse.eval nodeValue2688 (mixedVector B) := by
    change mixedMoment B node2688 node2688Labels = _
    exact sound2688 B hB hF
  have h2690 : mixedVector B (Sum.inr 2690) = Sparse.eval nodeValue2690 (mixedVector B) := by
    change mixedMoment B node2690 node2690Labels = _
    exact sound2690 B hB hF
  have h2700 : mixedVector B (Sum.inr 2700) = Sparse.eval nodeValue2700 (mixedVector B) := by
    change mixedMoment B node2700 node2700Labels = _
    exact sound2700 B hB hF
  have h3257 : mixedVector B (Sum.inr 3257) = Sparse.eval nodeValue3257 (mixedVector B) := by
    change mixedMoment B node3257 node3257Labels = _
    exact sound3257 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3554 : mixedVector B (Sum.inr 3554) = Sparse.eval nodeValue3554 (mixedVector B) := by
    change mixedMoment B node3554 node3554Labels = _
    exact sound3554 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3844 : mixedVector B (Sum.inr 3844) = Sparse.eval nodeValue3844 (mixedVector B) := by
    change mixedMoment B node3844 node3844Labels = _
    exact sound3844 B hB hF
  have h3867 : mixedVector B (Sum.inr 3867) = Sparse.eval nodeValue3867 (mixedVector B) := by
    change mixedMoment B node3867 node3867Labels = _
    exact sound3867 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  simpa only [sourceForm2503, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2688, h2690, h2700, h3257, h3304, h3521, h3546, h3554, h3562, h3581, h3844, h3867, h3875, reducedSource2017] using sourceEq2503 B hB

theorem rowSound2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2017 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2017, numericCheck2017, reducedZero2017 B hB hF, mul_zero]

theorem reducedZero2018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2018 (mixedVector B) = 0 := by
  have h4337 : mixedVector B (Sum.inr 4337) = Sparse.eval nodeValue4337 (mixedVector B) := by
    change mixedMoment B node4337 node4337Labels = _
    exact sound4337 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4936 : mixedVector B (Sum.inr 4936) = Sparse.eval nodeValue4936 (mixedVector B) := by
    change mixedMoment B node4936 node4936Labels = _
    exact sound4936 B hB hF
  have h4947 : mixedVector B (Sum.inr 4947) = Sparse.eval nodeValue4947 (mixedVector B) := by
    change mixedMoment B node4947 node4947Labels = _
    exact sound4947 B hB hF
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5462 : mixedVector B (Sum.inr 5462) = Sparse.eval nodeValue5462 (mixedVector B) := by
    change mixedMoment B node5462 node5462Labels = _
    exact sound5462 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485 B hB hF
  simpa only [sourceForm2504, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4337, h4351, h4451, h4936, h4947, h5123, h5163, h5172, h5227, h5290, h5447, h5462, h5485, reducedSource2018] using sourceEq2504 B hB

theorem rowSound2018 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2018 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2018, numericCheck2018, reducedZero2018 B hB hF, mul_zero]

theorem reducedZero2019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2019 (mixedVector B) = 0 := by
  have h4364 : mixedVector B (Sum.inr 4364) = Sparse.eval nodeValue4364 (mixedVector B) := by
    change mixedMoment B node4364 node4364Labels = _
    exact sound4364 B hB hF
  have h4366 : mixedVector B (Sum.inr 4366) = Sparse.eval nodeValue4366 (mixedVector B) := by
    change mixedMoment B node4366 node4366Labels = _
    exact sound4366 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4696 : mixedVector B (Sum.inr 4696) = Sparse.eval nodeValue4696 (mixedVector B) := by
    change mixedMoment B node4696 node4696Labels = _
    exact sound4696 B hB hF
  have h4698 : mixedVector B (Sum.inr 4698) = Sparse.eval nodeValue4698 (mixedVector B) := by
    change mixedMoment B node4698 node4698Labels = _
    exact sound4698 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5278 : mixedVector B (Sum.inr 5278) = Sparse.eval nodeValue5278 (mixedVector B) := by
    change mixedMoment B node5278 node5278Labels = _
    exact sound5278 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  simpa only [sourceForm2508, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4364, h4366, h4456, h4696, h4698, h4851, h4852, h4866, h4869, h4887, h4893, h5278, h5281, h5290, reducedSource2019] using sourceEq2508 B hB

theorem rowSound2019 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2019 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2019, numericCheck2019, reducedZero2019 B hB hF, mul_zero]

theorem reducedZero2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2020 (mixedVector B) = 0 := by
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h2238 : mixedVector B (Sum.inr 2238) = Sparse.eval nodeValue2238 (mixedVector B) := by
    change mixedMoment B node2238 node2238Labels = _
    exact sound2238 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2248 : mixedVector B (Sum.inr 2248) = Sparse.eval nodeValue2248 (mixedVector B) := by
    change mixedMoment B node2248 node2248Labels = _
    exact sound2248 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2747 : mixedVector B (Sum.inr 2747) = Sparse.eval nodeValue2747 (mixedVector B) := by
    change mixedMoment B node2747 node2747Labels = _
    exact sound2747 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  simpa only [sourceForm2509, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1703, h1706, h1711, h2238, h2240, h2243, h2248, h2250, h2260, h2263, h2275, h2747, h2750, h2764, reducedSource2020] using sourceEq2509 B hB

theorem rowSound2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2020 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2020, numericCheck2020, reducedZero2020 B hB hF, mul_zero]

theorem reducedZero2021 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2021 (mixedVector B) = 0 := by
  have h4230 : mixedVector B (Sum.inr 4230) = Sparse.eval nodeValue4230 (mixedVector B) := by
    change mixedMoment B node4230 node4230Labels = _
    exact sound4230 B hB hF
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450 B hB hF
  simpa only [sourceForm2510, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4230, h4232, h4252, h4676, h4679, h4798, h4805, h4826, h4865, h4866, h4889, h5386, h5431, h5450, reducedSource2021] using sourceEq2510 B hB

theorem rowSound2021 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2021 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2021, numericCheck2021, reducedZero2021 B hB hF, mul_zero]

theorem reducedZero2022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2022 (mixedVector B) = 0 := by
  have h4436 : mixedVector B (Sum.inr 4436) = Sparse.eval nodeValue4436 (mixedVector B) := by
    change mixedMoment B node4436 node4436Labels = _
    exact sound4436 B hB hF
  have h4441 : mixedVector B (Sum.inr 4441) = Sparse.eval nodeValue4441 (mixedVector B) := by
    change mixedMoment B node4441 node4441Labels = _
    exact sound4441 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4849 : mixedVector B (Sum.inr 4849) = Sparse.eval nodeValue4849 (mixedVector B) := by
    change mixedMoment B node4849 node4849Labels = _
    exact sound4849 B hB hF
  have h4854 : mixedVector B (Sum.inr 4854) = Sparse.eval nodeValue4854 (mixedVector B) := by
    change mixedMoment B node4854 node4854Labels = _
    exact sound4854 B hB hF
  have h4859 : mixedVector B (Sum.inr 4859) = Sparse.eval nodeValue4859 (mixedVector B) := by
    change mixedMoment B node4859 node4859Labels = _
    exact sound4859 B hB hF
  have h4863 : mixedVector B (Sum.inr 4863) = Sparse.eval nodeValue4863 (mixedVector B) := by
    change mixedMoment B node4863 node4863Labels = _
    exact sound4863 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167 B hB hF
  have h5197 : mixedVector B (Sum.inr 5197) = Sparse.eval nodeValue5197 (mixedVector B) := by
    change mixedMoment B node5197 node5197Labels = _
    exact sound5197 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  simpa only [sourceForm2511, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4436, h4441, h4451, h4831, h4833, h4849, h4854, h4859, h4863, h4864, h4878, h5167, h5197, h5202, reducedSource2022] using sourceEq2511 B hB

theorem rowSound2022 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2022 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2022, numericCheck2022, reducedZero2022 B hB hF, mul_zero]

theorem reducedZero2023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2023 (mixedVector B) = 0 := by
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4342 : mixedVector B (Sum.inr 4342) = Sparse.eval nodeValue4342 (mixedVector B) := by
    change mixedMoment B node4342 node4342Labels = _
    exact sound4342 B hB hF
  have h4345 : mixedVector B (Sum.inr 4345) = Sparse.eval nodeValue4345 (mixedVector B) := by
    change mixedMoment B node4345 node4345Labels = _
    exact sound4345 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4677 : mixedVector B (Sum.inr 4677) = Sparse.eval nodeValue4677 (mixedVector B) := by
    change mixedMoment B node4677 node4677Labels = _
    exact sound4677 B hB hF
  have h4680 : mixedVector B (Sum.inr 4680) = Sparse.eval nodeValue4680 (mixedVector B) := by
    change mixedMoment B node4680 node4680Labels = _
    exact sound4680 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4815 : mixedVector B (Sum.inr 4815) = Sparse.eval nodeValue4815 (mixedVector B) := by
    change mixedMoment B node4815 node4815Labels = _
    exact sound4815 B hB hF
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5250 : mixedVector B (Sum.inr 5250) = Sparse.eval nodeValue5250 (mixedVector B) := by
    change mixedMoment B node5250 node5250Labels = _
    exact sound5250 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  simpa only [sourceForm2512, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4341, h4342, h4345, h4495, h4676, h4677, h4680, h4801, h4803, h4815, h4816, h4834, h4835, h4839, h4888, h4889, h4895, h5220, h5250, h5251, h5259, reducedSource2023] using sourceEq2512 B hB

theorem rowSound2023 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2023 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2023, numericCheck2023, reducedZero2023 B hB hF, mul_zero]

theorem reducedZero2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2024 (mixedVector B) = 0 := by
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1665 : mixedVector B (Sum.inr 1665) = Sparse.eval nodeValue1665 (mixedVector B) := by
    change mixedMoment B node1665 node1665Labels = _
    exact sound1665 B hB hF
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h2141 : mixedVector B (Sum.inr 2141) = Sparse.eval nodeValue2141 (mixedVector B) := by
    change mixedMoment B node2141 node2141Labels = _
    exact sound2141 B hB hF
  have h2142 : mixedVector B (Sum.inr 2142) = Sparse.eval nodeValue2142 (mixedVector B) := by
    change mixedMoment B node2142 node2142Labels = _
    exact sound2142 B hB hF
  have h2145 : mixedVector B (Sum.inr 2145) = Sparse.eval nodeValue2145 (mixedVector B) := by
    change mixedMoment B node2145 node2145Labels = _
    exact sound2145 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  simpa only [sourceForm2513, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1664, h1665, h1668, h1708, h2141, h2142, h2145, h2190, h2192, h2195, h2196, h2205, h2206, h2216, h2244, h2245, h2265, h2662, h2709, h2710, h2723, reducedSource2024] using sourceEq2513 B hB

theorem rowSound2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2024 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2024, numericCheck2024, reducedZero2024 B hB hF, mul_zero]

theorem reducedZero2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2025 (mixedVector B) = 0 := by
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4073 : mixedVector B (Sum.inr 4073) = Sparse.eval nodeValue4073 (mixedVector B) := by
    change mixedMoment B node4073 node4073Labels = _
    exact sound4073 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2514, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4063, h4068, h4073, h4080, h4083, h4087, h4091, reducedSource2025] using sourceEq2514 B hB

theorem rowSound2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2025 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2025, numericCheck2025, reducedZero2025 B hB hF, mul_zero]

theorem reducedZero2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2026 (mixedVector B) = 0 := by
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h3131 : mixedVector B (Sum.inr 3131) = Sparse.eval nodeValue3131 (mixedVector B) := by
    change mixedMoment B node3131 node3131Labels = _
    exact sound3131 B hB hF
  have h3365 : mixedVector B (Sum.inr 3365) = Sparse.eval nodeValue3365 (mixedVector B) := by
    change mixedMoment B node3365 node3365Labels = _
    exact sound3365 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2515, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1814, h3131, h3365, h3379, h3391, h3395, h4084, reducedSource2026] using sourceEq2515 B hB

theorem rowSound2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2026 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2026, numericCheck2026, reducedZero2026 B hB hF, mul_zero]

theorem reducedZero2027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2027 (mixedVector B) = 0 := by
  have h2362 : mixedVector B (Sum.inr 2362) = Sparse.eval nodeValue2362 (mixedVector B) := by
    change mixedMoment B node2362 node2362Labels = _
    exact sound2362 B hB hF
  have h3032 : mixedVector B (Sum.inr 3032) = Sparse.eval nodeValue3032 (mixedVector B) := by
    change mixedMoment B node3032 node3032Labels = _
    exact sound3032 B hB hF
  have h3033 : mixedVector B (Sum.inr 3033) = Sparse.eval nodeValue3033 (mixedVector B) := by
    change mixedMoment B node3033 node3033Labels = _
    exact sound3033 B hB hF
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2516, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2362, h3032, h3033, h3040, h3045, h3732, h4092, reducedSource2027] using sourceEq2516 B hB

theorem rowSound2027 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2027 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2027, numericCheck2027, reducedZero2027 B hB hF, mul_zero]

theorem reducedZero2028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2028 (mixedVector B) = 0 := by
  have h2343 : mixedVector B (Sum.inr 2343) = Sparse.eval nodeValue2343 (mixedVector B) := by
    change mixedMoment B node2343 node2343Labels = _
    exact sound2343 B hB hF
  have h2819 : mixedVector B (Sum.inr 2819) = Sparse.eval nodeValue2819 (mixedVector B) := by
    change mixedMoment B node2819 node2819Labels = _
    exact sound2819 B hB hF
  have h3673 : mixedVector B (Sum.inr 3673) = Sparse.eval nodeValue3673 (mixedVector B) := by
    change mixedMoment B node3673 node3673Labels = _
    exact sound3673 B hB hF
  have h3699 : mixedVector B (Sum.inr 3699) = Sparse.eval nodeValue3699 (mixedVector B) := by
    change mixedMoment B node3699 node3699Labels = _
    exact sound3699 B hB hF
  have h3705 : mixedVector B (Sum.inr 3705) = Sparse.eval nodeValue3705 (mixedVector B) := by
    change mixedMoment B node3705 node3705Labels = _
    exact sound3705 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2519, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2343, h2819, h3673, h3699, h3705, h3706, h4092, reducedSource2028] using sourceEq2519 B hB

theorem rowSound2028 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2028 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2028, numericCheck2028, reducedZero2028 B hB hF, mul_zero]

theorem reducedZero2029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2029 (mixedVector B) = 0 := by
  have h2324 : mixedVector B (Sum.inr 2324) = Sparse.eval nodeValue2324 (mixedVector B) := by
    change mixedMoment B node2324 node2324Labels = _
    exact sound2324 B hB hF
  have h2801 : mixedVector B (Sum.inr 2801) = Sparse.eval nodeValue2801 (mixedVector B) := by
    change mixedMoment B node2801 node2801Labels = _
    exact sound2801 B hB hF
  have h3676 : mixedVector B (Sum.inr 3676) = Sparse.eval nodeValue3676 (mixedVector B) := by
    change mixedMoment B node3676 node3676Labels = _
    exact sound3676 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2520, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2324, h2801, h3676, h3685, h3690, h3692, h4091, reducedSource2029] using sourceEq2520 B hB

theorem rowSound2029 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2029 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2029, numericCheck2029, reducedZero2029 B hB hF, mul_zero]

theorem reducedZero2030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2030 (mixedVector B) = 0 := by
  have h2350 : mixedVector B (Sum.inr 2350) = Sparse.eval nodeValue2350 (mixedVector B) := by
    change mixedMoment B node2350 node2350Labels = _
    exact sound2350 B hB hF
  have h3134 : mixedVector B (Sum.inr 3134) = Sparse.eval nodeValue3134 (mixedVector B) := by
    change mixedMoment B node3134 node3134Labels = _
    exact sound3134 B hB hF
  have h3708 : mixedVector B (Sum.inr 3708) = Sparse.eval nodeValue3708 (mixedVector B) := by
    change mixedMoment B node3708 node3708Labels = _
    exact sound3708 B hB hF
  have h3715 : mixedVector B (Sum.inr 3715) = Sparse.eval nodeValue3715 (mixedVector B) := by
    change mixedMoment B node3715 node3715Labels = _
    exact sound3715 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2521, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2350, h3134, h3708, h3715, h3719, h3722, h4092, reducedSource2030] using sourceEq2521 B hB

theorem rowSound2030 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2030 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2030, numericCheck2030, reducedZero2030 B hB hF, mul_zero]

theorem reducedZero2031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2031 (mixedVector B) = 0 := by
  have h2824 : mixedVector B (Sum.inr 2824) = Sparse.eval nodeValue2824 (mixedVector B) := by
    change mixedMoment B node2824 node2824Labels = _
    exact sound2824 B hB hF
  have h3709 : mixedVector B (Sum.inr 3709) = Sparse.eval nodeValue3709 (mixedVector B) := by
    change mixedMoment B node3709 node3709Labels = _
    exact sound3709 B hB hF
  have h3716 : mixedVector B (Sum.inr 3716) = Sparse.eval nodeValue3716 (mixedVector B) := by
    change mixedMoment B node3716 node3716Labels = _
    exact sound3716 B hB hF
  have h3779 : mixedVector B (Sum.inr 3779) = Sparse.eval nodeValue3779 (mixedVector B) := by
    change mixedMoment B node3779 node3779Labels = _
    exact sound3779 B hB hF
  have h3922 : mixedVector B (Sum.inr 3922) = Sparse.eval nodeValue3922 (mixedVector B) := by
    change mixedMoment B node3922 node3922Labels = _
    exact sound3922 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2522, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2824, h3709, h3716, h3779, h3922, h4091, reducedSource2031] using sourceEq2522 B hB

theorem rowSound2031 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2031 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2031, numericCheck2031, reducedZero2031 B hB hF, mul_zero]

theorem sourceRowsAt2016 : MixedData.sourceRows (2016 : Fin 2425) =
    MixedData.row2016 := by decide +kernel

theorem sourceRowsAt2017 : MixedData.sourceRows (2017 : Fin 2425) =
    MixedData.row2017 := by decide +kernel

theorem sourceRowsAt2018 : MixedData.sourceRows (2018 : Fin 2425) =
    MixedData.row2018 := by decide +kernel

theorem sourceRowsAt2019 : MixedData.sourceRows (2019 : Fin 2425) =
    MixedData.row2019 := by decide +kernel

theorem sourceRowsAt2020 : MixedData.sourceRows (2020 : Fin 2425) =
    MixedData.row2020 := by decide +kernel

theorem sourceRowsAt2021 : MixedData.sourceRows (2021 : Fin 2425) =
    MixedData.row2021 := by decide +kernel

theorem sourceRowsAt2022 : MixedData.sourceRows (2022 : Fin 2425) =
    MixedData.row2022 := by decide +kernel

theorem sourceRowsAt2023 : MixedData.sourceRows (2023 : Fin 2425) =
    MixedData.row2023 := by decide +kernel

theorem sourceRowsAt2024 : MixedData.sourceRows (2024 : Fin 2425) =
    MixedData.row2024 := by decide +kernel

theorem sourceRowsAt2025 : MixedData.sourceRows (2025 : Fin 2425) =
    MixedData.row2025 := by decide +kernel

theorem sourceRowsAt2026 : MixedData.sourceRows (2026 : Fin 2425) =
    MixedData.row2026 := by decide +kernel

theorem sourceRowsAt2027 : MixedData.sourceRows (2027 : Fin 2425) =
    MixedData.row2027 := by decide +kernel

theorem sourceRowsAt2028 : MixedData.sourceRows (2028 : Fin 2425) =
    MixedData.row2028 := by decide +kernel

theorem sourceRowsAt2029 : MixedData.sourceRows (2029 : Fin 2425) =
    MixedData.row2029 := by decide +kernel

theorem sourceRowsAt2030 : MixedData.sourceRows (2030 : Fin 2425) =
    MixedData.row2030 := by decide +kernel

theorem sourceRowsAt2031 : MixedData.sourceRows (2031 : Fin 2425) =
    MixedData.row2031 := by decide +kernel

theorem chunkSound126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 126) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2016 ∨ k.val = 2017 ∨ k.val = 2018 ∨ k.val = 2019 ∨ k.val = 2020 ∨ k.val = 2021 ∨ k.val = 2022 ∨ k.val = 2023 ∨ k.val = 2024 ∨ k.val = 2025 ∨ k.val = 2026 ∨ k.val = 2027 ∨ k.val = 2028 ∨ k.val = 2029 ∨ k.val = 2030 ∨ k.val = 2031 := by omega
  rcases heq with h2016 | h2017 | h2018 | h2019 | h2020 | h2021 | h2022 | h2023 | h2024 | h2025 | h2026 | h2027 | h2028 | h2029 | h2030 | h2031
  · have he : k = (2016 : Fin 2425) := Fin.ext h2016
    subst k
    rw [sourceRowsAt2016]
    exact rowSound2016 B hB hF
  · have he : k = (2017 : Fin 2425) := Fin.ext h2017
    subst k
    rw [sourceRowsAt2017]
    exact rowSound2017 B hB hF
  · have he : k = (2018 : Fin 2425) := Fin.ext h2018
    subst k
    rw [sourceRowsAt2018]
    exact rowSound2018 B hB hF
  · have he : k = (2019 : Fin 2425) := Fin.ext h2019
    subst k
    rw [sourceRowsAt2019]
    exact rowSound2019 B hB hF
  · have he : k = (2020 : Fin 2425) := Fin.ext h2020
    subst k
    rw [sourceRowsAt2020]
    exact rowSound2020 B hB hF
  · have he : k = (2021 : Fin 2425) := Fin.ext h2021
    subst k
    rw [sourceRowsAt2021]
    exact rowSound2021 B hB hF
  · have he : k = (2022 : Fin 2425) := Fin.ext h2022
    subst k
    rw [sourceRowsAt2022]
    exact rowSound2022 B hB hF
  · have he : k = (2023 : Fin 2425) := Fin.ext h2023
    subst k
    rw [sourceRowsAt2023]
    exact rowSound2023 B hB hF
  · have he : k = (2024 : Fin 2425) := Fin.ext h2024
    subst k
    rw [sourceRowsAt2024]
    exact rowSound2024 B hB hF
  · have he : k = (2025 : Fin 2425) := Fin.ext h2025
    subst k
    rw [sourceRowsAt2025]
    exact rowSound2025 B hB hF
  · have he : k = (2026 : Fin 2425) := Fin.ext h2026
    subst k
    rw [sourceRowsAt2026]
    exact rowSound2026 B hB hF
  · have he : k = (2027 : Fin 2425) := Fin.ext h2027
    subst k
    rw [sourceRowsAt2027]
    exact rowSound2027 B hB hF
  · have he : k = (2028 : Fin 2425) := Fin.ext h2028
    subst k
    rw [sourceRowsAt2028]
    exact rowSound2028 B hB hF
  · have he : k = (2029 : Fin 2425) := Fin.ext h2029
    subst k
    rw [sourceRowsAt2029]
    exact rowSound2029 B hB hF
  · have he : k = (2030 : Fin 2425) := Fin.ext h2030
    subst k
    rw [sourceRowsAt2030]
    exact rowSound2030 B hB hF
  · have he : k = (2031 : Fin 2425) := Fin.ext h2031
    subst k
    rw [sourceRowsAt2031]
    exact rowSound2031 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
