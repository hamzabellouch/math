import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources5

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource144 (mixedVector B) = 0 := by
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5312 : mixedVector B (Sum.inr 5312) = Sparse.eval nodeValue5312 (mixedVector B) := by
    change mixedMoment B node5312 node5312Labels = _
    exact sound5312 B hB hF
  simpa only [sourceForm164, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4085, h4897, h5261, h5296, h5312, reducedSource144] using sourceEq164 B hB

theorem rowSound144 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row144 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck144, numericCheck144, reducedZero144 B hB hF, mul_zero]

theorem reducedZero145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource145 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  have h5308 : mixedVector B (Sum.inr 5308) = Sparse.eval nodeValue5308 (mixedVector B) := by
    change mixedMoment B node5308 node5308Labels = _
    exact sound5308 B hB hF
  simpa only [sourceForm165, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4460, h4468, h4505, h4605, h4621, h4804, h4841, h4868, h4894, h5272, h5305, h5308, reducedSource145] using sourceEq165 B hB

theorem rowSound145 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row145 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck145, numericCheck145, reducedZero145 B hB hF, mul_zero]

theorem reducedZero146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource146 (mixedVector B) = 0 := by
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
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
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h2786 : mixedVector B (Sum.inr 2786) = Sparse.eval nodeValue2786 (mixedVector B) := by
    change mixedMoment B node2786 node2786Labels = _
    exact sound2786 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm166, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1725, h1752, h1754, h2203, h2226, h2228, h2261, h2264, h2289, h2740, h2783, h2786, h4084, reducedSource146] using sourceEq166 B hB

theorem rowSound146 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row146 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck146, numericCheck146, reducedZero146 B hB hF, mul_zero]

theorem reducedZero147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource147 (mixedVector B) = 0 := by
  have h1051 : mixedVector B (Sum.inr 1051) = Sparse.eval nodeValue1051 (mixedVector B) := by
    change mixedMoment B node1051 node1051Labels = _
    exact sound1051 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm167, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1051, h1239, h1297, h2268, h4084, reducedSource147] using sourceEq167 B hB

theorem rowSound147 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row147 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck147, numericCheck147, reducedZero147 B hB hF, mul_zero]

theorem reducedZero148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource148 (mixedVector B) = 0 := by
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm168, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1239, h2022, h2060, h2268, h2740, h4084, reducedSource148] using sourceEq168 B hB

theorem rowSound148 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row148 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck148, numericCheck148, reducedZero148 B hB hF, mul_zero]

theorem reducedZero149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource149 (mixedVector B) = 0 := by
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm169, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1043, h2022, h2109, h2264, h2268, h4084, reducedSource149] using sourceEq169 B hB

theorem rowSound149 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row149 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck149, numericCheck149, reducedZero149 B hB hF, mul_zero]

theorem reducedZero150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource150 (mixedVector B) = 0 := by
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm170, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1297, h2109, h2268, h2783, h4084, reducedSource150] using sourceEq170 B hB

theorem rowSound150 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row150 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck150, numericCheck150, reducedZero150 B hB hF, mul_zero]

theorem reducedZero151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource151 (mixedVector B) = 0 := by
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5312 : mixedVector B (Sum.inr 5312) = Sparse.eval nodeValue5312 (mixedVector B) := by
    change mixedMoment B node5312 node5312Labels = _
    exact sound5312 B hB hF
  simpa only [sourceForm171, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4085, h4496, h4501, h4510, h4832, h4837, h4845, h4890, h4897, h4899, h5261, h5296, h5312, reducedSource151] using sourceEq171 B hB

theorem rowSound151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row151 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck151, numericCheck151, reducedZero151 B hB hF, mul_zero]

theorem reducedZero152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource152 (mixedVector B) = 0 := by
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  simpa only [sourceForm172, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4070, h4072, h4081, h4084, h4094, reducedSource152] using sourceEq172 B hB

theorem rowSound152 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row152 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck152, numericCheck152, reducedZero152 B hB hF, mul_zero]

theorem reducedZero153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource153 (mixedVector B) = 0 := by
  have h1354 : mixedVector B (Sum.inr 1354) = Sparse.eval nodeValue1354 (mixedVector B) := by
    change mixedMoment B node1354 node1354Labels = _
    exact sound1354 B hB hF
  have h1355 : mixedVector B (Sum.inr 1355) = Sparse.eval nodeValue1355 (mixedVector B) := by
    change mixedMoment B node1355 node1355Labels = _
    exact sound1355 B hB hF
  have h1356 : mixedVector B (Sum.inr 1356) = Sparse.eval nodeValue1356 (mixedVector B) := by
    change mixedMoment B node1356 node1356Labels = _
    exact sound1356 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h1903 : mixedVector B (Sum.inr 1903) = Sparse.eval nodeValue1903 (mixedVector B) := by
    change mixedMoment B node1903 node1903Labels = _
    exact sound1903 B hB hF
  have h1916 : mixedVector B (Sum.inr 1916) = Sparse.eval nodeValue1916 (mixedVector B) := by
    change mixedMoment B node1916 node1916Labels = _
    exact sound1916 B hB hF
  have h1927 : mixedVector B (Sum.inr 1927) = Sparse.eval nodeValue1927 (mixedVector B) := by
    change mixedMoment B node1927 node1927Labels = _
    exact sound1927 B hB hF
  have h2255 : mixedVector B (Sum.inr 2255) = Sparse.eval nodeValue2255 (mixedVector B) := by
    change mixedMoment B node2255 node2255Labels = _
    exact sound2255 B hB hF
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3146 : mixedVector B (Sum.inr 3146) = Sparse.eval nodeValue3146 (mixedVector B) := by
    change mixedMoment B node3146 node3146Labels = _
    exact sound3146 B hB hF
  have h3147 : mixedVector B (Sum.inr 3147) = Sparse.eval nodeValue3147 (mixedVector B) := by
    change mixedMoment B node3147 node3147Labels = _
    exact sound3147 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3165 : mixedVector B (Sum.inr 3165) = Sparse.eval nodeValue3165 (mixedVector B) := by
    change mixedMoment B node3165 node3165Labels = _
    exact sound3165 B hB hF
  have h3166 : mixedVector B (Sum.inr 3166) = Sparse.eval nodeValue3166 (mixedVector B) := by
    change mixedMoment B node3166 node3166Labels = _
    exact sound3166 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3193 : mixedVector B (Sum.inr 3193) = Sparse.eval nodeValue3193 (mixedVector B) := by
    change mixedMoment B node3193 node3193Labels = _
    exact sound3193 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223 B hB hF
  have h3224 : mixedVector B (Sum.inr 3224) = Sparse.eval nodeValue3224 (mixedVector B) := by
    change mixedMoment B node3224 node3224Labels = _
    exact sound3224 B hB hF
  have h3225 : mixedVector B (Sum.inr 3225) = Sparse.eval nodeValue3225 (mixedVector B) := by
    change mixedMoment B node3225 node3225Labels = _
    exact sound3225 B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227 B hB hF
  simpa only [sourceForm174, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1354, h1355, h1356, h1367, h1406, h1903, h1916, h1927, h2255, h3016, h3024, h3025, h3054, h3077, h3146, h3147, h3156, h3165, h3166, h3180, h3193, h3196, h3202, h3221, h3222, h3223, h3224, h3225, h3227, reducedSource153] using sourceEq174 B hB

theorem rowSound153 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row153 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck153, numericCheck153, reducedZero153 B hB hF, mul_zero]

theorem reducedZero154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource154 (mixedVector B) = 0 := by
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm176, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2253, h2513, h3528, h3577, h3625, h3626, h4084, reducedSource154] using sourceEq176 B hB

theorem rowSound154 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row154 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck154, numericCheck154, reducedZero154 B hB hF, mul_zero]

theorem reducedZero155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource155 (mixedVector B) = 0 := by
  have h1028 : mixedVector B (Sum.inr 1028) = Sparse.eval nodeValue1028 (mixedVector B) := by
    change mixedMoment B node1028 node1028Labels = _
    exact sound1028 B hB hF
  have h1029 : mixedVector B (Sum.inr 1029) = Sparse.eval nodeValue1029 (mixedVector B) := by
    change mixedMoment B node1029 node1029Labels = _
    exact sound1029 B hB hF
  have h1030 : mixedVector B (Sum.inr 1030) = Sparse.eval nodeValue1030 (mixedVector B) := by
    change mixedMoment B node1030 node1030Labels = _
    exact sound1030 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm177, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1028, h1029, h1030, h1042, h1058, h2253, h4084, reducedSource155] using sourceEq177 B hB

theorem rowSound155 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row155 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck155, numericCheck155, reducedZero155 B hB hF, mul_zero]

theorem reducedZero156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource156 (mixedVector B) = 0 := by
  have h1028 : mixedVector B (Sum.inr 1028) = Sparse.eval nodeValue1028 (mixedVector B) := by
    change mixedMoment B node1028 node1028Labels = _
    exact sound1028 B hB hF
  have h2095 : mixedVector B (Sum.inr 2095) = Sparse.eval nodeValue2095 (mixedVector B) := by
    change mixedMoment B node2095 node2095Labels = _
    exact sound2095 B hB hF
  have h2124 : mixedVector B (Sum.inr 2124) = Sparse.eval nodeValue2124 (mixedVector B) := by
    change mixedMoment B node2124 node2124Labels = _
    exact sound2124 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm178, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1028, h2095, h2124, h2252, h2253, h4084, reducedSource156] using sourceEq178 B hB

theorem rowSound156 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row156 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck156, numericCheck156, reducedZero156 B hB hF, mul_zero]

theorem reducedZero157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource157 (mixedVector B) = 0 := by
  have h2013 : mixedVector B (Sum.inr 2013) = Sparse.eval nodeValue2013 (mixedVector B) := by
    change mixedMoment B node2013 node2013Labels = _
    exact sound2013 B hB hF
  have h2014 : mixedVector B (Sum.inr 2014) = Sparse.eval nodeValue2014 (mixedVector B) := by
    change mixedMoment B node2014 node2014Labels = _
    exact sound2014 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm179, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2013, h2014, h2021, h2034, h2253, h3528, h4084, reducedSource157] using sourceEq179 B hB

theorem rowSound157 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row157 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck157, numericCheck157, reducedZero157 B hB hF, mul_zero]

theorem reducedZero158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource158 (mixedVector B) = 0 := by
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm180, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1058, h2034, h2133, h2253, h2277, h2279, h4084, reducedSource158] using sourceEq180 B hB

theorem rowSound158 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row158 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck158, numericCheck158, reducedZero158 B hB hF, mul_zero]

theorem reducedZero159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource159 (mixedVector B) = 0 := by
  have h2095 : mixedVector B (Sum.inr 2095) = Sparse.eval nodeValue2095 (mixedVector B) := by
    change mixedMoment B node2095 node2095Labels = _
    exact sound2095 B hB hF
  have h2096 : mixedVector B (Sum.inr 2096) = Sparse.eval nodeValue2096 (mixedVector B) := by
    change mixedMoment B node2096 node2096Labels = _
    exact sound2096 B hB hF
  have h2097 : mixedVector B (Sum.inr 2097) = Sparse.eval nodeValue2097 (mixedVector B) := by
    change mixedMoment B node2097 node2097Labels = _
    exact sound2097 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h3577 : mixedVector B (Sum.inr 3577) = Sparse.eval nodeValue3577 (mixedVector B) := by
    change mixedMoment B node3577 node3577Labels = _
    exact sound3577 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm181, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2095, h2096, h2097, h2108, h2253, h3577, h4084, reducedSource159] using sourceEq181 B hB

theorem rowSound159 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row159 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck159, numericCheck159, reducedZero159 B hB hF, mul_zero]

theorem sourceRowsAt144 : MixedData.sourceRows (144 : Fin 2425) =
    MixedData.row144 := by decide +kernel

theorem sourceRowsAt145 : MixedData.sourceRows (145 : Fin 2425) =
    MixedData.row145 := by decide +kernel

theorem sourceRowsAt146 : MixedData.sourceRows (146 : Fin 2425) =
    MixedData.row146 := by decide +kernel

theorem sourceRowsAt147 : MixedData.sourceRows (147 : Fin 2425) =
    MixedData.row147 := by decide +kernel

theorem sourceRowsAt148 : MixedData.sourceRows (148 : Fin 2425) =
    MixedData.row148 := by decide +kernel

theorem sourceRowsAt149 : MixedData.sourceRows (149 : Fin 2425) =
    MixedData.row149 := by decide +kernel

theorem sourceRowsAt150 : MixedData.sourceRows (150 : Fin 2425) =
    MixedData.row150 := by decide +kernel

theorem sourceRowsAt151 : MixedData.sourceRows (151 : Fin 2425) =
    MixedData.row151 := by decide +kernel

theorem sourceRowsAt152 : MixedData.sourceRows (152 : Fin 2425) =
    MixedData.row152 := by decide +kernel

theorem sourceRowsAt153 : MixedData.sourceRows (153 : Fin 2425) =
    MixedData.row153 := by decide +kernel

theorem sourceRowsAt154 : MixedData.sourceRows (154 : Fin 2425) =
    MixedData.row154 := by decide +kernel

theorem sourceRowsAt155 : MixedData.sourceRows (155 : Fin 2425) =
    MixedData.row155 := by decide +kernel

theorem sourceRowsAt156 : MixedData.sourceRows (156 : Fin 2425) =
    MixedData.row156 := by decide +kernel

theorem sourceRowsAt157 : MixedData.sourceRows (157 : Fin 2425) =
    MixedData.row157 := by decide +kernel

theorem sourceRowsAt158 : MixedData.sourceRows (158 : Fin 2425) =
    MixedData.row158 := by decide +kernel

theorem sourceRowsAt159 : MixedData.sourceRows (159 : Fin 2425) =
    MixedData.row159 := by decide +kernel

theorem chunkSound9 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 9) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 144 ∨ k.val = 145 ∨ k.val = 146 ∨ k.val = 147 ∨ k.val = 148 ∨ k.val = 149 ∨ k.val = 150 ∨ k.val = 151 ∨ k.val = 152 ∨ k.val = 153 ∨ k.val = 154 ∨ k.val = 155 ∨ k.val = 156 ∨ k.val = 157 ∨ k.val = 158 ∨ k.val = 159 := by omega
  rcases heq with h144 | h145 | h146 | h147 | h148 | h149 | h150 | h151 | h152 | h153 | h154 | h155 | h156 | h157 | h158 | h159
  · have he : k = (144 : Fin 2425) := Fin.ext h144
    subst k
    rw [sourceRowsAt144]
    exact rowSound144 B hB hF
  · have he : k = (145 : Fin 2425) := Fin.ext h145
    subst k
    rw [sourceRowsAt145]
    exact rowSound145 B hB hF
  · have he : k = (146 : Fin 2425) := Fin.ext h146
    subst k
    rw [sourceRowsAt146]
    exact rowSound146 B hB hF
  · have he : k = (147 : Fin 2425) := Fin.ext h147
    subst k
    rw [sourceRowsAt147]
    exact rowSound147 B hB hF
  · have he : k = (148 : Fin 2425) := Fin.ext h148
    subst k
    rw [sourceRowsAt148]
    exact rowSound148 B hB hF
  · have he : k = (149 : Fin 2425) := Fin.ext h149
    subst k
    rw [sourceRowsAt149]
    exact rowSound149 B hB hF
  · have he : k = (150 : Fin 2425) := Fin.ext h150
    subst k
    rw [sourceRowsAt150]
    exact rowSound150 B hB hF
  · have he : k = (151 : Fin 2425) := Fin.ext h151
    subst k
    rw [sourceRowsAt151]
    exact rowSound151 B hB hF
  · have he : k = (152 : Fin 2425) := Fin.ext h152
    subst k
    rw [sourceRowsAt152]
    exact rowSound152 B hB hF
  · have he : k = (153 : Fin 2425) := Fin.ext h153
    subst k
    rw [sourceRowsAt153]
    exact rowSound153 B hB hF
  · have he : k = (154 : Fin 2425) := Fin.ext h154
    subst k
    rw [sourceRowsAt154]
    exact rowSound154 B hB hF
  · have he : k = (155 : Fin 2425) := Fin.ext h155
    subst k
    rw [sourceRowsAt155]
    exact rowSound155 B hB hF
  · have he : k = (156 : Fin 2425) := Fin.ext h156
    subst k
    rw [sourceRowsAt156]
    exact rowSound156 B hB hF
  · have he : k = (157 : Fin 2425) := Fin.ext h157
    subst k
    rw [sourceRowsAt157]
    exact rowSound157 B hB hF
  · have he : k = (158 : Fin 2425) := Fin.ext h158
    subst k
    rw [sourceRowsAt158]
    exact rowSound158 B hB hF
  · have he : k = (159 : Fin 2425) := Fin.ext h159
    subst k
    rw [sourceRowsAt159]
    exact rowSound159 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
