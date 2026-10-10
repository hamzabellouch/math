import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources45

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1232 (mixedVector B) = 0 := by
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4121 : mixedVector B (Sum.inr 4121) = Sparse.eval nodeValue4121 (mixedVector B) := by
    change mixedMoment B node4121 node4121Labels = _
    exact sound4121 B hB hF
  have h4134 : mixedVector B (Sum.inr 4134) = Sparse.eval nodeValue4134 (mixedVector B) := by
    change mixedMoment B node4134 node4134Labels = _
    exact sound4134 B hB hF
  have h4137 : mixedVector B (Sum.inr 4137) = Sparse.eval nodeValue4137 (mixedVector B) := by
    change mixedMoment B node4137 node4137Labels = _
    exact sound4137 B hB hF
  have h4212 : mixedVector B (Sum.inr 4212) = Sparse.eval nodeValue4212 (mixedVector B) := by
    change mixedMoment B node4212 node4212Labels = _
    exact sound4212 B hB hF
  have h4225 : mixedVector B (Sum.inr 4225) = Sparse.eval nodeValue4225 (mixedVector B) := by
    change mixedMoment B node4225 node4225Labels = _
    exact sound4225 B hB hF
  have h4228 : mixedVector B (Sum.inr 4228) = Sparse.eval nodeValue4228 (mixedVector B) := by
    change mixedMoment B node4228 node4228Labels = _
    exact sound4228 B hB hF
  have h4272 : mixedVector B (Sum.inr 4272) = Sparse.eval nodeValue4272 (mixedVector B) := by
    change mixedMoment B node4272 node4272Labels = _
    exact sound4272 B hB hF
  have h4273 : mixedVector B (Sum.inr 4273) = Sparse.eval nodeValue4273 (mixedVector B) := by
    change mixedMoment B node4273 node4273Labels = _
    exact sound4273 B hB hF
  have h4280 : mixedVector B (Sum.inr 4280) = Sparse.eval nodeValue4280 (mixedVector B) := by
    change mixedMoment B node4280 node4280Labels = _
    exact sound4280 B hB hF
  have h4431 : mixedVector B (Sum.inr 4431) = Sparse.eval nodeValue4431 (mixedVector B) := by
    change mixedMoment B node4431 node4431Labels = _
    exact sound4431 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  simpa only [sourceForm1437, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4071, h4121, h4134, h4137, h4212, h4225, h4228, h4272, h4273, h4280, h4431, h4510, h4511, reducedSource1232] using sourceEq1437 B hB

theorem rowSound1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1232 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1232, numericCheck1232, reducedZero1232 B hB hF, mul_zero]

theorem reducedZero1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1233 (mixedVector B) = 0 := by
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4122 : mixedVector B (Sum.inr 4122) = Sparse.eval nodeValue4122 (mixedVector B) := by
    change mixedMoment B node4122 node4122Labels = _
    exact sound4122 B hB hF
  have h4136 : mixedVector B (Sum.inr 4136) = Sparse.eval nodeValue4136 (mixedVector B) := by
    change mixedMoment B node4136 node4136Labels = _
    exact sound4136 B hB hF
  have h4138 : mixedVector B (Sum.inr 4138) = Sparse.eval nodeValue4138 (mixedVector B) := by
    change mixedMoment B node4138 node4138Labels = _
    exact sound4138 B hB hF
  have h4213 : mixedVector B (Sum.inr 4213) = Sparse.eval nodeValue4213 (mixedVector B) := by
    change mixedMoment B node4213 node4213Labels = _
    exact sound4213 B hB hF
  have h4227 : mixedVector B (Sum.inr 4227) = Sparse.eval nodeValue4227 (mixedVector B) := by
    change mixedMoment B node4227 node4227Labels = _
    exact sound4227 B hB hF
  have h4229 : mixedVector B (Sum.inr 4229) = Sparse.eval nodeValue4229 (mixedVector B) := by
    change mixedMoment B node4229 node4229Labels = _
    exact sound4229 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4285 : mixedVector B (Sum.inr 4285) = Sparse.eval nodeValue4285 (mixedVector B) := by
    change mixedMoment B node4285 node4285Labels = _
    exact sound4285 B hB hF
  have h4428 : mixedVector B (Sum.inr 4428) = Sparse.eval nodeValue4428 (mixedVector B) := by
    change mixedMoment B node4428 node4428Labels = _
    exact sound4428 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  simpa only [sourceForm1438, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4070, h4122, h4136, h4138, h4213, h4227, h4229, h4269, h4270, h4285, h4428, h4505, h4507, reducedSource1233] using sourceEq1438 B hB

theorem rowSound1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1233 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1233, numericCheck1233, reducedZero1233 B hB hF, mul_zero]

theorem reducedZero1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1234 (mixedVector B) = 0 := by
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  have h4060 : mixedVector B (Sum.inr 4060) = Sparse.eval nodeValue4060 (mixedVector B) := by
    change mixedMoment B node4060 node4060Labels = _
    exact sound4060 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4066 : mixedVector B (Sum.inr 4066) = Sparse.eval nodeValue4066 (mixedVector B) := by
    change mixedMoment B node4066 node4066Labels = _
    exact sound4066 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4072 : mixedVector B (Sum.inr 4072) = Sparse.eval nodeValue4072 (mixedVector B) := by
    change mixedMoment B node4072 node4072Labels = _
    exact sound4072 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1439, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4058, h4060, h4061, h4064, h4066, h4067, h4069, h4070, h4071, h4072, h4081, h4084, h4085, reducedSource1234] using sourceEq1439 B hB

theorem rowSound1234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1234 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1234, numericCheck1234, reducedZero1234 B hB hF, mul_zero]

theorem reducedZero1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1235 (mixedVector B) = 0 := by
  have h616 : mixedVector B (Sum.inr 616) = Sparse.eval nodeValue616 (mixedVector B) := by
    change mixedMoment B node616 node616Labels = _
    exact sound616 B hB hF
  have h935 : mixedVector B (Sum.inr 935) = Sparse.eval nodeValue935 (mixedVector B) := by
    change mixedMoment B node935 node935Labels = _
    exact sound935 B hB hF
  have h1063 : mixedVector B (Sum.inr 1063) = Sparse.eval nodeValue1063 (mixedVector B) := by
    change mixedMoment B node1063 node1063Labels = _
    exact sound1063 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1440, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h616, h935, h1063, h1083, h1087, h4084, reducedSource1235] using sourceEq1440 B hB

theorem rowSound1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1235 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1235, numericCheck1235, reducedZero1235 B hB hF, mul_zero]

theorem reducedZero1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1236 (mixedVector B) = 0 := by
  have h1318 : mixedVector B (Sum.inr 1318) = Sparse.eval nodeValue1318 (mixedVector B) := by
    change mixedMoment B node1318 node1318Labels = _
    exact sound1318 B hB hF
  have h1324 : mixedVector B (Sum.inr 1324) = Sparse.eval nodeValue1324 (mixedVector B) := by
    change mixedMoment B node1324 node1324Labels = _
    exact sound1324 B hB hF
  have h1325 : mixedVector B (Sum.inr 1325) = Sparse.eval nodeValue1325 (mixedVector B) := by
    change mixedMoment B node1325 node1325Labels = _
    exact sound1325 B hB hF
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h2889 : mixedVector B (Sum.inr 2889) = Sparse.eval nodeValue2889 (mixedVector B) := by
    change mixedMoment B node2889 node2889Labels = _
    exact sound2889 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1441, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1318, h1324, h1325, h1375, h2889, h4092, reducedSource1236] using sourceEq1441 B hB

theorem rowSound1236 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1236 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1236, numericCheck1236, reducedZero1236 B hB hF, mul_zero]

theorem reducedZero1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1237 (mixedVector B) = 0 := by
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1443, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1736, h1738, h1740, h1751, h3301, h4071, reducedSource1237] using sourceEq1443 B hB

theorem rowSound1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1237 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1237, numericCheck1237, reducedZero1237 B hB hF, mul_zero]

theorem reducedZero1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1238 (mixedVector B) = 0 := by
  have h858 : mixedVector B (Sum.inr 858) = Sparse.eval nodeValue858 (mixedVector B) := by
    change mixedMoment B node858 node858Labels = _
    exact sound858 B hB hF
  have h1626 : mixedVector B (Sum.inr 1626) = Sparse.eval nodeValue1626 (mixedVector B) := by
    change mixedMoment B node1626 node1626Labels = _
    exact sound1626 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1444, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h858, h1626, h1740, h1751, h4071, reducedSource1238] using sourceEq1444 B hB

theorem rowSound1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1238 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1238, numericCheck1238, reducedZero1238 B hB hF, mul_zero]

theorem reducedZero1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1239 (mixedVector B) = 0 := by
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h1611 : mixedVector B (Sum.inr 1611) = Sparse.eval nodeValue1611 (mixedVector B) := by
    change mixedMoment B node1611 node1611Labels = _
    exact sound1611 B hB hF
  have h1660 : mixedVector B (Sum.inr 1660) = Sparse.eval nodeValue1660 (mixedVector B) := by
    change mixedMoment B node1660 node1660Labels = _
    exact sound1660 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1445, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h830, h1611, h1660, h1738, h1740, h4071, reducedSource1239] using sourceEq1445 B hB

theorem rowSound1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1239 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1239, numericCheck1239, reducedZero1239 B hB hF, mul_zero]

theorem reducedZero1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1240 (mixedVector B) = 0 := by
  have h586 : mixedVector B (Sum.inr 586) = Sparse.eval nodeValue586 (mixedVector B) := by
    change mixedMoment B node586 node586Labels = _
    exact sound586 B hB hF
  have h910 : mixedVector B (Sum.inr 910) = Sparse.eval nodeValue910 (mixedVector B) := by
    change mixedMoment B node910 node910Labels = _
    exact sound910 B hB hF
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1026 : mixedVector B (Sum.inr 1026) = Sparse.eval nodeValue1026 (mixedVector B) := by
    change mixedMoment B node1026 node1026Labels = _
    exact sound1026 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1448, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h586, h910, h950, h1026, h1041, h1044, h4083, reducedSource1240] using sourceEq1448 B hB

theorem rowSound1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1240 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1240, numericCheck1240, reducedZero1240 B hB hF, mul_zero]

theorem reducedZero1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1241 (mixedVector B) = 0 := by
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1334 : mixedVector B (Sum.inr 1334) = Sparse.eval nodeValue1334 (mixedVector B) := by
    change mixedMoment B node1334 node1334Labels = _
    exact sound1334 B hB hF
  have h1338 : mixedVector B (Sum.inr 1338) = Sparse.eval nodeValue1338 (mixedVector B) := by
    change mixedMoment B node1338 node1338Labels = _
    exact sound1338 B hB hF
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1449, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1328, h1333, h1334, h1338, h1391, h2931, h4091, reducedSource1241] using sourceEq1449 B hB

theorem rowSound1241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1241 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1241, numericCheck1241, reducedZero1241 B hB hF, mul_zero]

theorem reducedZero1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1242 (mixedVector B) = 0 := by
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h2397 : mixedVector B (Sum.inr 2397) = Sparse.eval nodeValue2397 (mixedVector B) := by
    change mixedMoment B node2397 node2397Labels = _
    exact sound2397 B hB hF
  have h3280 : mixedVector B (Sum.inr 3280) = Sparse.eval nodeValue3280 (mixedVector B) := by
    change mixedMoment B node3280 node3280Labels = _
    exact sound3280 B hB hF
  have h3284 : mixedVector B (Sum.inr 3284) = Sparse.eval nodeValue3284 (mixedVector B) := by
    change mixedMoment B node3284 node3284Labels = _
    exact sound3284 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1450, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1736, h2397, h3280, h3284, h3301, h4071, reducedSource1242] using sourceEq1450 B hB

theorem rowSound1242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1242 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1242, numericCheck1242, reducedZero1242 B hB hF, mul_zero]

theorem reducedZero1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1243 (mixedVector B) = 0 := by
  have h848 : mixedVector B (Sum.inr 848) = Sparse.eval nodeValue848 (mixedVector B) := by
    change mixedMoment B node848 node848Labels = _
    exact sound848 B hB hF
  have h1614 : mixedVector B (Sum.inr 1614) = Sparse.eval nodeValue1614 (mixedVector B) := by
    change mixedMoment B node1614 node1614Labels = _
    exact sound1614 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1452, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h848, h1614, h1736, h1751, h4071, reducedSource1243] using sourceEq1452 B hB

theorem rowSound1243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1243 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1243, numericCheck1243, reducedZero1243 B hB hF, mul_zero]

theorem reducedZero1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1244 (mixedVector B) = 0 := by
  have h823 : mixedVector B (Sum.inr 823) = Sparse.eval nodeValue823 (mixedVector B) := by
    change mixedMoment B node823 node823Labels = _
    exact sound823 B hB hF
  have h1606 : mixedVector B (Sum.inr 1606) = Sparse.eval nodeValue1606 (mixedVector B) := by
    change mixedMoment B node1606 node1606Labels = _
    exact sound1606 B hB hF
  have h1655 : mixedVector B (Sum.inr 1655) = Sparse.eval nodeValue1655 (mixedVector B) := by
    change mixedMoment B node1655 node1655Labels = _
    exact sound1655 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1453, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h823, h1606, h1655, h1736, h1738, h4071, reducedSource1244] using sourceEq1453 B hB

theorem rowSound1244 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1244 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1244, numericCheck1244, reducedZero1244 B hB hF, mul_zero]

theorem reducedZero1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1245 (mixedVector B) = 0 := by
  have h1356 : mixedVector B (Sum.inr 1356) = Sparse.eval nodeValue1356 (mixedVector B) := by
    change mixedMoment B node1356 node1356Labels = _
    exact sound1356 B hB hF
  have h2856 : mixedVector B (Sum.inr 2856) = Sparse.eval nodeValue2856 (mixedVector B) := by
    change mixedMoment B node2856 node2856Labels = _
    exact sound2856 B hB hF
  have h2911 : mixedVector B (Sum.inr 2911) = Sparse.eval nodeValue2911 (mixedVector B) := by
    change mixedMoment B node2911 node2911Labels = _
    exact sound2911 B hB hF
  have h2970 : mixedVector B (Sum.inr 2970) = Sparse.eval nodeValue2970 (mixedVector B) := by
    change mixedMoment B node2970 node2970Labels = _
    exact sound2970 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1455, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1356, h2856, h2911, h2970, h3025, h4088, reducedSource1245] using sourceEq1455 B hB

theorem rowSound1245 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1245 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1245, numericCheck1245, reducedZero1245 B hB hF, mul_zero]

theorem reducedZero1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1246 (mixedVector B) = 0 := by
  have h1133 : mixedVector B (Sum.inr 1133) = Sparse.eval nodeValue1133 (mixedVector B) := by
    change mixedMoment B node1133 node1133Labels = _
    exact sound1133 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1146 : mixedVector B (Sum.inr 1146) = Sparse.eval nodeValue1146 (mixedVector B) := by
    change mixedMoment B node1146 node1146Labels = _
    exact sound1146 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1457, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1133, h1143, h1146, h1245, h2522, h4084, reducedSource1246] using sourceEq1457 B hB

theorem rowSound1246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1246 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1246, numericCheck1246, reducedZero1246 B hB hF, mul_zero]

theorem reducedZero1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1247 (mixedVector B) = 0 := by
  have h653 : mixedVector B (Sum.inr 653) = Sparse.eval nodeValue653 (mixedVector B) := by
    change mixedMoment B node653 node653Labels = _
    exact sound653 B hB hF
  have h1171 : mixedVector B (Sum.inr 1171) = Sparse.eval nodeValue1171 (mixedVector B) := by
    change mixedMoment B node1171 node1171Labels = _
    exact sound1171 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1458, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h653, h1171, h1273, h1294, h1306, h4092, reducedSource1247] using sourceEq1458 B hB

theorem rowSound1247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1247 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1247, numericCheck1247, reducedZero1247 B hB hF, mul_zero]

theorem sourceRowsAt1232 : MixedData.sourceRows (1232 : Fin 2425) =
    MixedData.row1232 := by decide +kernel

theorem sourceRowsAt1233 : MixedData.sourceRows (1233 : Fin 2425) =
    MixedData.row1233 := by decide +kernel

theorem sourceRowsAt1234 : MixedData.sourceRows (1234 : Fin 2425) =
    MixedData.row1234 := by decide +kernel

theorem sourceRowsAt1235 : MixedData.sourceRows (1235 : Fin 2425) =
    MixedData.row1235 := by decide +kernel

theorem sourceRowsAt1236 : MixedData.sourceRows (1236 : Fin 2425) =
    MixedData.row1236 := by decide +kernel

theorem sourceRowsAt1237 : MixedData.sourceRows (1237 : Fin 2425) =
    MixedData.row1237 := by decide +kernel

theorem sourceRowsAt1238 : MixedData.sourceRows (1238 : Fin 2425) =
    MixedData.row1238 := by decide +kernel

theorem sourceRowsAt1239 : MixedData.sourceRows (1239 : Fin 2425) =
    MixedData.row1239 := by decide +kernel

theorem sourceRowsAt1240 : MixedData.sourceRows (1240 : Fin 2425) =
    MixedData.row1240 := by decide +kernel

theorem sourceRowsAt1241 : MixedData.sourceRows (1241 : Fin 2425) =
    MixedData.row1241 := by decide +kernel

theorem sourceRowsAt1242 : MixedData.sourceRows (1242 : Fin 2425) =
    MixedData.row1242 := by decide +kernel

theorem sourceRowsAt1243 : MixedData.sourceRows (1243 : Fin 2425) =
    MixedData.row1243 := by decide +kernel

theorem sourceRowsAt1244 : MixedData.sourceRows (1244 : Fin 2425) =
    MixedData.row1244 := by decide +kernel

theorem sourceRowsAt1245 : MixedData.sourceRows (1245 : Fin 2425) =
    MixedData.row1245 := by decide +kernel

theorem sourceRowsAt1246 : MixedData.sourceRows (1246 : Fin 2425) =
    MixedData.row1246 := by decide +kernel

theorem sourceRowsAt1247 : MixedData.sourceRows (1247 : Fin 2425) =
    MixedData.row1247 := by decide +kernel

theorem chunkSound77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 77) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1232 ∨ k.val = 1233 ∨ k.val = 1234 ∨ k.val = 1235 ∨ k.val = 1236 ∨ k.val = 1237 ∨ k.val = 1238 ∨ k.val = 1239 ∨ k.val = 1240 ∨ k.val = 1241 ∨ k.val = 1242 ∨ k.val = 1243 ∨ k.val = 1244 ∨ k.val = 1245 ∨ k.val = 1246 ∨ k.val = 1247 := by omega
  rcases heq with h1232 | h1233 | h1234 | h1235 | h1236 | h1237 | h1238 | h1239 | h1240 | h1241 | h1242 | h1243 | h1244 | h1245 | h1246 | h1247
  · have he : k = (1232 : Fin 2425) := Fin.ext h1232
    subst k
    rw [sourceRowsAt1232]
    exact rowSound1232 B hB hF
  · have he : k = (1233 : Fin 2425) := Fin.ext h1233
    subst k
    rw [sourceRowsAt1233]
    exact rowSound1233 B hB hF
  · have he : k = (1234 : Fin 2425) := Fin.ext h1234
    subst k
    rw [sourceRowsAt1234]
    exact rowSound1234 B hB hF
  · have he : k = (1235 : Fin 2425) := Fin.ext h1235
    subst k
    rw [sourceRowsAt1235]
    exact rowSound1235 B hB hF
  · have he : k = (1236 : Fin 2425) := Fin.ext h1236
    subst k
    rw [sourceRowsAt1236]
    exact rowSound1236 B hB hF
  · have he : k = (1237 : Fin 2425) := Fin.ext h1237
    subst k
    rw [sourceRowsAt1237]
    exact rowSound1237 B hB hF
  · have he : k = (1238 : Fin 2425) := Fin.ext h1238
    subst k
    rw [sourceRowsAt1238]
    exact rowSound1238 B hB hF
  · have he : k = (1239 : Fin 2425) := Fin.ext h1239
    subst k
    rw [sourceRowsAt1239]
    exact rowSound1239 B hB hF
  · have he : k = (1240 : Fin 2425) := Fin.ext h1240
    subst k
    rw [sourceRowsAt1240]
    exact rowSound1240 B hB hF
  · have he : k = (1241 : Fin 2425) := Fin.ext h1241
    subst k
    rw [sourceRowsAt1241]
    exact rowSound1241 B hB hF
  · have he : k = (1242 : Fin 2425) := Fin.ext h1242
    subst k
    rw [sourceRowsAt1242]
    exact rowSound1242 B hB hF
  · have he : k = (1243 : Fin 2425) := Fin.ext h1243
    subst k
    rw [sourceRowsAt1243]
    exact rowSound1243 B hB hF
  · have he : k = (1244 : Fin 2425) := Fin.ext h1244
    subst k
    rw [sourceRowsAt1244]
    exact rowSound1244 B hB hF
  · have he : k = (1245 : Fin 2425) := Fin.ext h1245
    subst k
    rw [sourceRowsAt1245]
    exact rowSound1245 B hB hF
  · have he : k = (1246 : Fin 2425) := Fin.ext h1246
    subst k
    rw [sourceRowsAt1246]
    exact rowSound1246 B hB hF
  · have he : k = (1247 : Fin 2425) := Fin.ext h1247
    subst k
    rw [sourceRowsAt1247]
    exact rowSound1247 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
