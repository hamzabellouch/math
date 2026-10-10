import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources14

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource368 (mixedVector B) = 0 := by
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
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
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2770 : mixedVector B (Sum.inr 2770) = Sparse.eval nodeValue2770 (mixedVector B) := by
    change mixedMoment B node2770 node2770Labels = _
    exact sound2770 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h2788 : mixedVector B (Sum.inr 2788) = Sparse.eval nodeValue2788 (mixedVector B) := by
    change mixedMoment B node2788 node2788Labels = _
    exact sound2788 B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  have h4017 : mixedVector B (Sum.inr 4017) = Sparse.eval nodeValue4017 (mixedVector B) := by
    change mixedMoment B node4017 node4017Labels = _
    exact sound4017 B hB hF
  have h4019 : mixedVector B (Sum.inr 4019) = Sparse.eval nodeValue4019 (mixedVector B) := by
    change mixedMoment B node4019 node4019Labels = _
    exact sound4019 B hB hF
  simpa only [sourceForm436, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1044, h1046, h1049, h1087, h2483, h2485, h2488, h2515, h2599, h2601, h2604, h2764, h2765, h2768, h2770, h2782, h2788, h3982, h4001, h4017, h4019, reducedSource368] using sourceEq436 B hB

theorem rowSound368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row368 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck368, numericCheck368, reducedZero368 B hB hF, mul_zero]

theorem reducedZero369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource369 (mixedVector B) = 0 := by
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  have h5309 : mixedVector B (Sum.inr 5309) = Sparse.eval nodeValue5309 (mixedVector B) := by
    change mixedMoment B node5309 node5309Labels = _
    exact sound5309 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  simpa only [sourceForm437, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4889, h4895, h4896, h4898, h5251, h5258, h5259, h5260, h5267, h5270, h5272, h5274, h5276, h5284, h5293, h5294, h5295, h5302, h5308, h5309, h5310, reducedSource369] using sourceEq437 B hB

theorem rowSound369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row369 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck369, numericCheck369, reducedZero369 B hB hF, mul_zero]

theorem reducedZero370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource370 (mixedVector B) = 0 := by
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2710 : mixedVector B (Sum.inr 2710) = Sparse.eval nodeValue2710 (mixedVector B) := by
    change mixedMoment B node2710 node2710Labels = _
    exact sound2710 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2753 : mixedVector B (Sum.inr 2753) = Sparse.eval nodeValue2753 (mixedVector B) := by
    change mixedMoment B node2753 node2753Labels = _
    exact sound2753 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2767 : mixedVector B (Sum.inr 2767) = Sparse.eval nodeValue2767 (mixedVector B) := by
    change mixedMoment B node2767 node2767Labels = _
    exact sound2767 B hB hF
  have h2768 : mixedVector B (Sum.inr 2768) = Sparse.eval nodeValue2768 (mixedVector B) := by
    change mixedMoment B node2768 node2768Labels = _
    exact sound2768 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h2787 : mixedVector B (Sum.inr 2787) = Sparse.eval nodeValue2787 (mixedVector B) := by
    change mixedMoment B node2787 node2787Labels = _
    exact sound2787 B hB hF
  have h2788 : mixedVector B (Sum.inr 2788) = Sparse.eval nodeValue2788 (mixedVector B) := by
    change mixedMoment B node2788 node2788Labels = _
    exact sound2788 B hB hF
  have h3089 : mixedVector B (Sum.inr 3089) = Sparse.eval nodeValue3089 (mixedVector B) := by
    change mixedMoment B node3089 node3089Labels = _
    exact sound3089 B hB hF
  have h3112 : mixedVector B (Sum.inr 3112) = Sparse.eval nodeValue3112 (mixedVector B) := by
    change mixedMoment B node3112 node3112Labels = _
    exact sound3112 B hB hF
  have h3113 : mixedVector B (Sum.inr 3113) = Sparse.eval nodeValue3113 (mixedVector B) := by
    change mixedMoment B node3113 node3113Labels = _
    exact sound3113 B hB hF
  have h3124 : mixedVector B (Sum.inr 3124) = Sparse.eval nodeValue3124 (mixedVector B) := by
    change mixedMoment B node3124 node3124Labels = _
    exact sound3124 B hB hF
  simpa only [sourceForm438, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2245, h2265, h2266, h2279, h2710, h2723, h2724, h2732, h2753, h2754, h2767, h2768, h2769, h2776, h2777, h2787, h2788, h3089, h3112, h3113, h3124, reducedSource370] using sourceEq438 B hB

theorem rowSound370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row370 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck370, numericCheck370, reducedZero370 B hB hF, mul_zero]

theorem reducedZero371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource371 (mixedVector B) = 0 := by
  have h1229 : mixedVector B (Sum.inr 1229) = Sparse.eval nodeValue1229 (mixedVector B) := by
    change mixedMoment B node1229 node1229Labels = _
    exact sound1229 B hB hF
  have h1231 : mixedVector B (Sum.inr 1231) = Sparse.eval nodeValue1231 (mixedVector B) := by
    change mixedMoment B node1231 node1231Labels = _
    exact sound1231 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h1292 : mixedVector B (Sum.inr 1292) = Sparse.eval nodeValue1292 (mixedVector B) := by
    change mixedMoment B node1292 node1292Labels = _
    exact sound1292 B hB hF
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h2875 : mixedVector B (Sum.inr 2875) = Sparse.eval nodeValue2875 (mixedVector B) := by
    change mixedMoment B node2875 node2875Labels = _
    exact sound2875 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h2921 : mixedVector B (Sum.inr 2921) = Sparse.eval nodeValue2921 (mixedVector B) := by
    change mixedMoment B node2921 node2921Labels = _
    exact sound2921 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3103 : mixedVector B (Sum.inr 3103) = Sparse.eval nodeValue3103 (mixedVector B) := by
    change mixedMoment B node3103 node3103Labels = _
    exact sound3103 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3987 : mixedVector B (Sum.inr 3987) = Sparse.eval nodeValue3987 (mixedVector B) := by
    change mixedMoment B node3987 node3987Labels = _
    exact sound3987 B hB hF
  simpa only [sourceForm440, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1229, h1231, h1245, h1292, h1639, h1651, h1716, h2875, h2888, h2921, h2930, h2952, h3024, h3052, h3097, h3103, h3119, h3573, h3584, h3626, h3987, reducedSource371] using sourceEq440 B hB

theorem rowSound371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row371 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck371, numericCheck371, reducedZero371 B hB hF, mul_zero]

theorem reducedZero372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource372 (mixedVector B) = 0 := by
  have h1070 : mixedVector B (Sum.inr 1070) = Sparse.eval nodeValue1070 (mixedVector B) := by
    change mixedMoment B node1070 node1070Labels = _
    exact sound1070 B hB hF
  have h1072 : mixedVector B (Sum.inr 1072) = Sparse.eval nodeValue1072 (mixedVector B) := by
    change mixedMoment B node1072 node1072Labels = _
    exact sound1072 B hB hF
  have h1076 : mixedVector B (Sum.inr 1076) = Sparse.eval nodeValue1076 (mixedVector B) := by
    change mixedMoment B node1076 node1076Labels = _
    exact sound1076 B hB hF
  have h1084 : mixedVector B (Sum.inr 1084) = Sparse.eval nodeValue1084 (mixedVector B) := by
    change mixedMoment B node1084 node1084Labels = _
    exact sound1084 B hB hF
  have h2500 : mixedVector B (Sum.inr 2500) = Sparse.eval nodeValue2500 (mixedVector B) := by
    change mixedMoment B node2500 node2500Labels = _
    exact sound2500 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h2506 : mixedVector B (Sum.inr 2506) = Sparse.eval nodeValue2506 (mixedVector B) := by
    change mixedMoment B node2506 node2506Labels = _
    exact sound2506 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  simpa only [sourceForm441, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1070, h1072, h1076, h1084, h2500, h2502, h2506, h2513, h2681, h2683, h2687, h2735, h2737, h2744, h2773, h2774, h2776, h3572, h3582, h3583, h3888, reducedSource372] using sourceEq441 B hB

theorem rowSound372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row372 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck372, numericCheck372, reducedZero372 B hB hF, mul_zero]

theorem reducedZero373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource373 (mixedVector B) = 0 := by
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm442, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2769, h3051, h3054, h3055, h3913, h4092, reducedSource373] using sourceEq442 B hB

theorem rowSound373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row373 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck373, numericCheck373, reducedZero373 B hB hF, mul_zero]

theorem reducedZero374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource374 (mixedVector B) = 0 := by
  have h1268 : mixedVector B (Sum.inr 1268) = Sparse.eval nodeValue1268 (mixedVector B) := by
    change mixedMoment B node1268 node1268Labels = _
    exact sound1268 B hB hF
  have h1272 : mixedVector B (Sum.inr 1272) = Sparse.eval nodeValue1272 (mixedVector B) := by
    change mixedMoment B node1272 node1272Labels = _
    exact sound1272 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm443, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1268, h1272, h1273, h1306, h2769, h4092, reducedSource374] using sourceEq443 B hB

theorem rowSound374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row374 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck374, numericCheck374, reducedZero374 B hB hF, mul_zero]

theorem reducedZero375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource375 (mixedVector B) = 0 := by
  have h1268 : mixedVector B (Sum.inr 1268) = Sparse.eval nodeValue1268 (mixedVector B) := by
    change mixedMoment B node1268 node1268Labels = _
    exact sound1268 B hB hF
  have h2571 : mixedVector B (Sum.inr 2571) = Sparse.eval nodeValue2571 (mixedVector B) := by
    change mixedMoment B node2571 node2571Labels = _
    exact sound2571 B hB hF
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm444, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1268, h2571, h2639, h2759, h2763, h2769, h4092, reducedSource375] using sourceEq444 B hB

theorem rowSound375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row375 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck375, numericCheck375, reducedZero375 B hB hF, mul_zero]

theorem reducedZero376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource376 (mixedVector B) = 0 := by
  have h1433 : mixedVector B (Sum.inr 1433) = Sparse.eval nodeValue1433 (mixedVector B) := by
    change mixedMoment B node1433 node1433Labels = _
    exact sound1433 B hB hF
  have h2571 : mixedVector B (Sum.inr 2571) = Sparse.eval nodeValue2571 (mixedVector B) := by
    change mixedMoment B node2571 node2571Labels = _
    exact sound2571 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2600 : mixedVector B (Sum.inr 2600) = Sparse.eval nodeValue2600 (mixedVector B) := by
    change mixedMoment B node2600 node2600Labels = _
    exact sound2600 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm445, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1433, h2571, h2575, h2600, h2769, h3051, h4092, reducedSource376] using sourceEq445 B hB

theorem rowSound376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row376 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck376, numericCheck376, reducedZero376 B hB hF, mul_zero]

theorem reducedZero377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource377 (mixedVector B) = 0 := by
  have h1437 : mixedVector B (Sum.inr 1437) = Sparse.eval nodeValue1437 (mixedVector B) := by
    change mixedMoment B node1437 node1437Labels = _
    exact sound1437 B hB hF
  have h2639 : mixedVector B (Sum.inr 2639) = Sparse.eval nodeValue2639 (mixedVector B) := by
    change mixedMoment B node2639 node2639Labels = _
    exact sound2639 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm446, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1437, h2639, h2643, h2769, h3055, h4092, reducedSource377] using sourceEq446 B hB

theorem rowSound377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row377 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck377, numericCheck377, reducedZero377 B hB hF, mul_zero]

theorem reducedZero378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource378 (mixedVector B) = 0 := by
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h2575 : mixedVector B (Sum.inr 2575) = Sparse.eval nodeValue2575 (mixedVector B) := by
    change mixedMoment B node2575 node2575Labels = _
    exact sound2575 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm447, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1273, h2575, h2643, h2765, h2769, h4092, reducedSource378] using sourceEq447 B hB

theorem rowSound378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row378 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck378, numericCheck378, reducedZero378 B hB hF, mul_zero]

theorem reducedZero379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource379 (mixedVector B) = 0 := by
  have h1272 : mixedVector B (Sum.inr 1272) = Sparse.eval nodeValue1272 (mixedVector B) := by
    change mixedMoment B node1272 node1272Labels = _
    exact sound1272 B hB hF
  have h1433 : mixedVector B (Sum.inr 1433) = Sparse.eval nodeValue1433 (mixedVector B) := by
    change mixedMoment B node1433 node1433Labels = _
    exact sound1433 B hB hF
  have h1436 : mixedVector B (Sum.inr 1436) = Sparse.eval nodeValue1436 (mixedVector B) := by
    change mixedMoment B node1436 node1436Labels = _
    exact sound1436 B hB hF
  have h1437 : mixedVector B (Sum.inr 1437) = Sparse.eval nodeValue1437 (mixedVector B) := by
    change mixedMoment B node1437 node1437Labels = _
    exact sound1437 B hB hF
  have h2769 : mixedVector B (Sum.inr 2769) = Sparse.eval nodeValue2769 (mixedVector B) := by
    change mixedMoment B node2769 node2769Labels = _
    exact sound2769 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm448, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1272, h1433, h1436, h1437, h2769, h4092, reducedSource379] using sourceEq448 B hB

theorem rowSound379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row379 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck379, numericCheck379, reducedZero379 B hB hF, mul_zero]

theorem reducedZero380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource380 (mixedVector B) = 0 := by
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1657 : mixedVector B (Sum.inr 1657) = Sparse.eval nodeValue1657 (mixedVector B) := by
    change mixedMoment B node1657 node1657Labels = _
    exact sound1657 B hB hF
  have h1661 : mixedVector B (Sum.inr 1661) = Sparse.eval nodeValue1661 (mixedVector B) := by
    change mixedMoment B node1661 node1661Labels = _
    exact sound1661 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2603 : mixedVector B (Sum.inr 2603) = Sparse.eval nodeValue2603 (mixedVector B) := by
    change mixedMoment B node2603 node2603Labels = _
    exact sound2603 B hB hF
  have h2717 : mixedVector B (Sum.inr 2717) = Sparse.eval nodeValue2717 (mixedVector B) := by
    change mixedMoment B node2717 node2717Labels = _
    exact sound2717 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2761 : mixedVector B (Sum.inr 2761) = Sparse.eval nodeValue2761 (mixedVector B) := by
    change mixedMoment B node2761 node2761Labels = _
    exact sound2761 B hB hF
  have h2762 : mixedVector B (Sum.inr 2762) = Sparse.eval nodeValue2762 (mixedVector B) := by
    change mixedMoment B node2762 node2762Labels = _
    exact sound2762 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h2784 : mixedVector B (Sum.inr 2784) = Sparse.eval nodeValue2784 (mixedVector B) := by
    change mixedMoment B node2784 node2784Labels = _
    exact sound2784 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3118 : mixedVector B (Sum.inr 3118) = Sparse.eval nodeValue3118 (mixedVector B) := by
    change mixedMoment B node3118 node3118Labels = _
    exact sound3118 B hB hF
  have h3119 : mixedVector B (Sum.inr 3119) = Sparse.eval nodeValue3119 (mixedVector B) := by
    change mixedMoment B node3119 node3119Labels = _
    exact sound3119 B hB hF
  simpa only [sourceForm451, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1656, h1657, h1661, h1745, h2259, h2287, h2290, h2584, h2603, h2717, h2735, h2738, h2761, h2762, h2763, h2781, h2782, h2784, h3096, h3118, h3119, reducedSource380] using sourceEq451 B hB

theorem rowSound380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row380 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck380, numericCheck380, reducedZero380 B hB hF, mul_zero]

theorem reducedZero381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource381 (mixedVector B) = 0 := by
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm452, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3098, h3572, h3583, h3623, h4083, reducedSource381] using sourceEq452 B hB

theorem rowSound381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row381 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck381, numericCheck381, reducedZero381 B hB hF, mul_zero]

theorem reducedZero382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource382 (mixedVector B) = 0 := by
  have h1404 : mixedVector B (Sum.inr 1404) = Sparse.eval nodeValue1404 (mixedVector B) := by
    change mixedMoment B node1404 node1404Labels = _
    exact sound1404 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h1418 : mixedVector B (Sum.inr 1418) = Sparse.eval nodeValue1418 (mixedVector B) := by
    change mixedMoment B node1418 node1418Labels = _
    exact sound1418 B hB hF
  have h1440 : mixedVector B (Sum.inr 1440) = Sparse.eval nodeValue1440 (mixedVector B) := by
    change mixedMoment B node1440 node1440Labels = _
    exact sound1440 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm453, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1404, h1408, h1418, h1440, h3098, h4083, reducedSource382] using sourceEq453 B hB

theorem rowSound382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row382 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck382, numericCheck382, reducedZero382 B hB hF, mul_zero]

theorem reducedZero383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource383 (mixedVector B) = 0 := by
  have h1404 : mixedVector B (Sum.inr 1404) = Sparse.eval nodeValue1404 (mixedVector B) := by
    change mixedMoment B node1404 node1404Labels = _
    exact sound1404 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h2983 : mixedVector B (Sum.inr 2983) = Sparse.eval nodeValue2983 (mixedVector B) := by
    change mixedMoment B node2983 node2983Labels = _
    exact sound2983 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3096 : mixedVector B (Sum.inr 3096) = Sparse.eval nodeValue3096 (mixedVector B) := by
    change mixedMoment B node3096 node3096Labels = _
    exact sound3096 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm454, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1404, h2952, h2983, h3075, h3096, h3098, h4083, reducedSource383] using sourceEq454 B hB

theorem rowSound383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row383 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck383, numericCheck383, reducedZero383 B hB hF, mul_zero]

theorem sourceRowsAt368 : MixedData.sourceRows (368 : Fin 2425) =
    MixedData.row368 := by decide +kernel

theorem sourceRowsAt369 : MixedData.sourceRows (369 : Fin 2425) =
    MixedData.row369 := by decide +kernel

theorem sourceRowsAt370 : MixedData.sourceRows (370 : Fin 2425) =
    MixedData.row370 := by decide +kernel

theorem sourceRowsAt371 : MixedData.sourceRows (371 : Fin 2425) =
    MixedData.row371 := by decide +kernel

theorem sourceRowsAt372 : MixedData.sourceRows (372 : Fin 2425) =
    MixedData.row372 := by decide +kernel

theorem sourceRowsAt373 : MixedData.sourceRows (373 : Fin 2425) =
    MixedData.row373 := by decide +kernel

theorem sourceRowsAt374 : MixedData.sourceRows (374 : Fin 2425) =
    MixedData.row374 := by decide +kernel

theorem sourceRowsAt375 : MixedData.sourceRows (375 : Fin 2425) =
    MixedData.row375 := by decide +kernel

theorem sourceRowsAt376 : MixedData.sourceRows (376 : Fin 2425) =
    MixedData.row376 := by decide +kernel

theorem sourceRowsAt377 : MixedData.sourceRows (377 : Fin 2425) =
    MixedData.row377 := by decide +kernel

theorem sourceRowsAt378 : MixedData.sourceRows (378 : Fin 2425) =
    MixedData.row378 := by decide +kernel

theorem sourceRowsAt379 : MixedData.sourceRows (379 : Fin 2425) =
    MixedData.row379 := by decide +kernel

theorem sourceRowsAt380 : MixedData.sourceRows (380 : Fin 2425) =
    MixedData.row380 := by decide +kernel

theorem sourceRowsAt381 : MixedData.sourceRows (381 : Fin 2425) =
    MixedData.row381 := by decide +kernel

theorem sourceRowsAt382 : MixedData.sourceRows (382 : Fin 2425) =
    MixedData.row382 := by decide +kernel

theorem sourceRowsAt383 : MixedData.sourceRows (383 : Fin 2425) =
    MixedData.row383 := by decide +kernel

theorem chunkSound23 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 23) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 368 ∨ k.val = 369 ∨ k.val = 370 ∨ k.val = 371 ∨ k.val = 372 ∨ k.val = 373 ∨ k.val = 374 ∨ k.val = 375 ∨ k.val = 376 ∨ k.val = 377 ∨ k.val = 378 ∨ k.val = 379 ∨ k.val = 380 ∨ k.val = 381 ∨ k.val = 382 ∨ k.val = 383 := by omega
  rcases heq with h368 | h369 | h370 | h371 | h372 | h373 | h374 | h375 | h376 | h377 | h378 | h379 | h380 | h381 | h382 | h383
  · have he : k = (368 : Fin 2425) := Fin.ext h368
    subst k
    rw [sourceRowsAt368]
    exact rowSound368 B hB hF
  · have he : k = (369 : Fin 2425) := Fin.ext h369
    subst k
    rw [sourceRowsAt369]
    exact rowSound369 B hB hF
  · have he : k = (370 : Fin 2425) := Fin.ext h370
    subst k
    rw [sourceRowsAt370]
    exact rowSound370 B hB hF
  · have he : k = (371 : Fin 2425) := Fin.ext h371
    subst k
    rw [sourceRowsAt371]
    exact rowSound371 B hB hF
  · have he : k = (372 : Fin 2425) := Fin.ext h372
    subst k
    rw [sourceRowsAt372]
    exact rowSound372 B hB hF
  · have he : k = (373 : Fin 2425) := Fin.ext h373
    subst k
    rw [sourceRowsAt373]
    exact rowSound373 B hB hF
  · have he : k = (374 : Fin 2425) := Fin.ext h374
    subst k
    rw [sourceRowsAt374]
    exact rowSound374 B hB hF
  · have he : k = (375 : Fin 2425) := Fin.ext h375
    subst k
    rw [sourceRowsAt375]
    exact rowSound375 B hB hF
  · have he : k = (376 : Fin 2425) := Fin.ext h376
    subst k
    rw [sourceRowsAt376]
    exact rowSound376 B hB hF
  · have he : k = (377 : Fin 2425) := Fin.ext h377
    subst k
    rw [sourceRowsAt377]
    exact rowSound377 B hB hF
  · have he : k = (378 : Fin 2425) := Fin.ext h378
    subst k
    rw [sourceRowsAt378]
    exact rowSound378 B hB hF
  · have he : k = (379 : Fin 2425) := Fin.ext h379
    subst k
    rw [sourceRowsAt379]
    exact rowSound379 B hB hF
  · have he : k = (380 : Fin 2425) := Fin.ext h380
    subst k
    rw [sourceRowsAt380]
    exact rowSound380 B hB hF
  · have he : k = (381 : Fin 2425) := Fin.ext h381
    subst k
    rw [sourceRowsAt381]
    exact rowSound381 B hB hF
  · have he : k = (382 : Fin 2425) := Fin.ext h382
    subst k
    rw [sourceRowsAt382]
    exact rowSound382 B hB hF
  · have he : k = (383 : Fin 2425) := Fin.ext h383
    subst k
    rw [sourceRowsAt383]
    exact rowSound383 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
