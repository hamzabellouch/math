import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic96
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources57

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1536 (mixedVector B) = 0 := by
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4105 : mixedVector B (Sum.inr 4105) = Sparse.eval nodeValue4105 (mixedVector B) := by
    change mixedMoment B node4105 node4105Labels = _
    exact sound4105 B hB hF
  have h4107 : mixedVector B (Sum.inr 4107) = Sparse.eval nodeValue4107 (mixedVector B) := by
    change mixedMoment B node4107 node4107Labels = _
    exact sound4107 B hB hF
  have h4125 : mixedVector B (Sum.inr 4125) = Sparse.eval nodeValue4125 (mixedVector B) := by
    change mixedMoment B node4125 node4125Labels = _
    exact sound4125 B hB hF
  have h4199 : mixedVector B (Sum.inr 4199) = Sparse.eval nodeValue4199 (mixedVector B) := by
    change mixedMoment B node4199 node4199Labels = _
    exact sound4199 B hB hF
  have h4201 : mixedVector B (Sum.inr 4201) = Sparse.eval nodeValue4201 (mixedVector B) := by
    change mixedMoment B node4201 node4201Labels = _
    exact sound4201 B hB hF
  have h4216 : mixedVector B (Sum.inr 4216) = Sparse.eval nodeValue4216 (mixedVector B) := by
    change mixedMoment B node4216 node4216Labels = _
    exact sound4216 B hB hF
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4237 : mixedVector B (Sum.inr 4237) = Sparse.eval nodeValue4237 (mixedVector B) := by
    change mixedMoment B node4237 node4237Labels = _
    exact sound4237 B hB hF
  have h4239 : mixedVector B (Sum.inr 4239) = Sparse.eval nodeValue4239 (mixedVector B) := by
    change mixedMoment B node4239 node4239Labels = _
    exact sound4239 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4253 : mixedVector B (Sum.inr 4253) = Sparse.eval nodeValue4253 (mixedVector B) := by
    change mixedMoment B node4253 node4253Labels = _
    exact sound4253 B hB hF
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4263 : mixedVector B (Sum.inr 4263) = Sparse.eval nodeValue4263 (mixedVector B) := by
    change mixedMoment B node4263 node4263Labels = _
    exact sound4263 B hB hF
  have h4267 : mixedVector B (Sum.inr 4267) = Sparse.eval nodeValue4267 (mixedVector B) := by
    change mixedMoment B node4267 node4267Labels = _
    exact sound4267 B hB hF
  have h4417 : mixedVector B (Sum.inr 4417) = Sparse.eval nodeValue4417 (mixedVector B) := by
    change mixedMoment B node4417 node4417Labels = _
    exact sound4417 B hB hF
  have h4489 : mixedVector B (Sum.inr 4489) = Sparse.eval nodeValue4489 (mixedVector B) := by
    change mixedMoment B node4489 node4489Labels = _
    exact sound4489 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  simpa only [sourceForm1815, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4068, h4100, h4105, h4107, h4125, h4199, h4201, h4216, h4232, h4237, h4239, h4249, h4253, h4256, h4263, h4267, h4417, h4489, h4495, h4497, reducedSource1536] using sourceEq1815 B hB

theorem rowSound1536 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1536 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1536, numericCheck1536, reducedZero1536 B hB hF, mul_zero]

theorem reducedZero1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1537 (mixedVector B) = 0 := by
  have h662 : mixedVector B (Sum.inr 662) = Sparse.eval nodeValue662 (mixedVector B) := by
    change mixedMoment B node662 node662Labels = _
    exact sound662 B hB hF
  have h681 : mixedVector B (Sum.inr 681) = Sparse.eval nodeValue681 (mixedVector B) := by
    change mixedMoment B node681 node681Labels = _
    exact sound681 B hB hF
  have h682 : mixedVector B (Sum.inr 682) = Sparse.eval nodeValue682 (mixedVector B) := by
    change mixedMoment B node682 node682Labels = _
    exact sound682 B hB hF
  have h687 : mixedVector B (Sum.inr 687) = Sparse.eval nodeValue687 (mixedVector B) := by
    change mixedMoment B node687 node687Labels = _
    exact sound687 B hB hF
  have h760 : mixedVector B (Sum.inr 760) = Sparse.eval nodeValue760 (mixedVector B) := by
    change mixedMoment B node760 node760Labels = _
    exact sound760 B hB hF
  have h761 : mixedVector B (Sum.inr 761) = Sparse.eval nodeValue761 (mixedVector B) := by
    change mixedMoment B node761 node761Labels = _
    exact sound761 B hB hF
  have h766 : mixedVector B (Sum.inr 766) = Sparse.eval nodeValue766 (mixedVector B) := by
    change mixedMoment B node766 node766Labels = _
    exact sound766 B hB hF
  have h798 : mixedVector B (Sum.inr 798) = Sparse.eval nodeValue798 (mixedVector B) := by
    change mixedMoment B node798 node798Labels = _
    exact sound798 B hB hF
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h840 : mixedVector B (Sum.inr 840) = Sparse.eval nodeValue840 (mixedVector B) := by
    change mixedMoment B node840 node840Labels = _
    exact sound840 B hB hF
  have h841 : mixedVector B (Sum.inr 841) = Sparse.eval nodeValue841 (mixedVector B) := by
    change mixedMoment B node841 node841Labels = _
    exact sound841 B hB hF
  have h847 : mixedVector B (Sum.inr 847) = Sparse.eval nodeValue847 (mixedVector B) := by
    change mixedMoment B node847 node847Labels = _
    exact sound847 B hB hF
  have h848 : mixedVector B (Sum.inr 848) = Sparse.eval nodeValue848 (mixedVector B) := by
    change mixedMoment B node848 node848Labels = _
    exact sound848 B hB hF
  have h850 : mixedVector B (Sum.inr 850) = Sparse.eval nodeValue850 (mixedVector B) := by
    change mixedMoment B node850 node850Labels = _
    exact sound850 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1816, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h662, h681, h682, h687, h760, h761, h766, h798, h803, h805, h840, h841, h847, h848, h850, h998, h1073, h1079, h1081, h4068, reducedSource1537] using sourceEq1816 B hB

theorem rowSound1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1537 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1537, numericCheck1537, reducedZero1537 B hB hF, mul_zero]

theorem reducedZero1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1538 (mixedVector B) = 0 := by
  have h732 : mixedVector B (Sum.inr 732) = Sparse.eval nodeValue732 (mixedVector B) := by
    change mixedMoment B node732 node732Labels = _
    exact sound732 B hB hF
  have h737 : mixedVector B (Sum.inr 737) = Sparse.eval nodeValue737 (mixedVector B) := by
    change mixedMoment B node737 node737Labels = _
    exact sound737 B hB hF
  have h739 : mixedVector B (Sum.inr 739) = Sparse.eval nodeValue739 (mixedVector B) := by
    change mixedMoment B node739 node739Labels = _
    exact sound739 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1817, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h732, h737, h739, h810, h1648, h4068, reducedSource1538] using sourceEq1817 B hB

theorem rowSound1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1538 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1538, numericCheck1538, reducedZero1538 B hB hF, mul_zero]

theorem reducedZero1539 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1539 (mixedVector B) = 0 := by
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4113 : mixedVector B (Sum.inr 4113) = Sparse.eval nodeValue4113 (mixedVector B) := by
    change mixedMoment B node4113 node4113Labels = _
    exact sound4113 B hB hF
  have h4118 : mixedVector B (Sum.inr 4118) = Sparse.eval nodeValue4118 (mixedVector B) := by
    change mixedMoment B node4118 node4118Labels = _
    exact sound4118 B hB hF
  have h4119 : mixedVector B (Sum.inr 4119) = Sparse.eval nodeValue4119 (mixedVector B) := by
    change mixedMoment B node4119 node4119Labels = _
    exact sound4119 B hB hF
  have h4126 : mixedVector B (Sum.inr 4126) = Sparse.eval nodeValue4126 (mixedVector B) := by
    change mixedMoment B node4126 node4126Labels = _
    exact sound4126 B hB hF
  have h4209 : mixedVector B (Sum.inr 4209) = Sparse.eval nodeValue4209 (mixedVector B) := by
    change mixedMoment B node4209 node4209Labels = _
    exact sound4209 B hB hF
  have h4210 : mixedVector B (Sum.inr 4210) = Sparse.eval nodeValue4210 (mixedVector B) := by
    change mixedMoment B node4210 node4210Labels = _
    exact sound4210 B hB hF
  have h4217 : mixedVector B (Sum.inr 4217) = Sparse.eval nodeValue4217 (mixedVector B) := by
    change mixedMoment B node4217 node4217Labels = _
    exact sound4217 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4267 : mixedVector B (Sum.inr 4267) = Sparse.eval nodeValue4267 (mixedVector B) := by
    change mixedMoment B node4267 node4267Labels = _
    exact sound4267 B hB hF
  have h4268 : mixedVector B (Sum.inr 4268) = Sparse.eval nodeValue4268 (mixedVector B) := by
    change mixedMoment B node4268 node4268Labels = _
    exact sound4268 B hB hF
  have h4275 : mixedVector B (Sum.inr 4275) = Sparse.eval nodeValue4275 (mixedVector B) := by
    change mixedMoment B node4275 node4275Labels = _
    exact sound4275 B hB hF
  have h4283 : mixedVector B (Sum.inr 4283) = Sparse.eval nodeValue4283 (mixedVector B) := by
    change mixedMoment B node4283 node4283Labels = _
    exact sound4283 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  simpa only [sourceForm1818, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4069, h4113, h4118, h4119, h4126, h4209, h4210, h4217, h4249, h4252, h4264, h4265, h4267, h4268, h4275, h4283, h4399, h4458, h4461, h4502, reducedSource1539] using sourceEq1818 B hB

theorem rowSound1539 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1539 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1539, numericCheck1539, reducedZero1539 B hB hF, mul_zero]

theorem reducedZero1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1540 (mixedVector B) = 0 := by
  have h4057 : mixedVector B (Sum.inr 4057) = Sparse.eval nodeValue4057 (mixedVector B) := by
    change mixedMoment B node4057 node4057Labels = _
    exact sound4057 B hB hF
  have h4058 : mixedVector B (Sum.inr 4058) = Sparse.eval nodeValue4058 (mixedVector B) := by
    change mixedMoment B node4058 node4058Labels = _
    exact sound4058 B hB hF
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  have h4063 : mixedVector B (Sum.inr 4063) = Sparse.eval nodeValue4063 (mixedVector B) := by
    change mixedMoment B node4063 node4063Labels = _
    exact sound4063 B hB hF
  have h4064 : mixedVector B (Sum.inr 4064) = Sparse.eval nodeValue4064 (mixedVector B) := by
    change mixedMoment B node4064 node4064Labels = _
    exact sound4064 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1821, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4057, h4058, h4059, h4063, h4064, h4065, h4068, h4069, h4070, h4071, h4080, h4083, h4084, reducedSource1540] using sourceEq1821 B hB

theorem rowSound1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1540 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1540, numericCheck1540, reducedZero1540 B hB hF, mul_zero]

theorem reducedZero1541 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1541 (mixedVector B) = 0 := by
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h3057 : mixedVector B (Sum.inr 3057) = Sparse.eval nodeValue3057 (mixedVector B) := by
    change mixedMoment B node3057 node3057Labels = _
    exact sound3057 B hB hF
  have h3072 : mixedVector B (Sum.inr 3072) = Sparse.eval nodeValue3072 (mixedVector B) := by
    change mixedMoment B node3072 node3072Labels = _
    exact sound3072 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1822, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1700, h3057, h3072, h3304, h4068, reducedSource1541] using sourceEq1822 B hB

theorem rowSound1541 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1541 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1541, numericCheck1541, reducedZero1541 B hB hF, mul_zero]

theorem reducedZero1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1542 (mixedVector B) = 0 := by
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1823, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1698, h1700, h1708, h3304, h4068, reducedSource1542] using sourceEq1823 B hB

theorem rowSound1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1542 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1542, numericCheck1542, reducedZero1542 B hB hF, mul_zero]

theorem reducedZero1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1543 (mixedVector B) = 0 := by
  have h597 : mixedVector B (Sum.inr 597) = Sparse.eval nodeValue597 (mixedVector B) := by
    change mixedMoment B node597 node597Labels = _
    exact sound597 B hB hF
  have h1038 : mixedVector B (Sum.inr 1038) = Sparse.eval nodeValue1038 (mixedVector B) := by
    change mixedMoment B node1038 node1038Labels = _
    exact sound1038 B hB hF
  have h1056 : mixedVector B (Sum.inr 1056) = Sparse.eval nodeValue1056 (mixedVector B) := by
    change mixedMoment B node1056 node1056Labels = _
    exact sound1056 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1824, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h597, h1038, h1056, h1079, h4084, reducedSource1543] using sourceEq1824 B hB

theorem rowSound1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1543 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1543, numericCheck1543, reducedZero1543 B hB hF, mul_zero]

theorem reducedZero1544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1544 (mixedVector B) = 0 := by
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h3286 : mixedVector B (Sum.inr 3286) = Sparse.eval nodeValue3286 (mixedVector B) := by
    change mixedMoment B node3286 node3286Labels = _
    exact sound3286 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1825, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1698, h3286, h3292, h3304, h4068, reducedSource1544] using sourceEq1825 B hB

theorem rowSound1544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1544 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1544, numericCheck1544, reducedZero1544 B hB hF, mul_zero]

theorem reducedZero1545 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1545 (mixedVector B) = 0 := by
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1826, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1698, h1699, h1706, h3292, h4068, reducedSource1545] using sourceEq1826 B hB

theorem rowSound1545 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1545 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1545, numericCheck1545, reducedZero1545 B hB hF, mul_zero]

theorem reducedZero1546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1546 (mixedVector B) = 0 := by
  have h1316 : mixedVector B (Sum.inr 1316) = Sparse.eval nodeValue1316 (mixedVector B) := by
    change mixedMoment B node1316 node1316Labels = _
    exact sound1316 B hB hF
  have h1319 : mixedVector B (Sum.inr 1319) = Sparse.eval nodeValue1319 (mixedVector B) := by
    change mixedMoment B node1319 node1319Labels = _
    exact sound1319 B hB hF
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1827, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1316, h1319, h1366, h2880, h4091, reducedSource1546] using sourceEq1827 B hB

theorem rowSound1546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1546 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1546, numericCheck1546, reducedZero1546 B hB hF, mul_zero]

theorem reducedZero1547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1547 (mixedVector B) = 0 := by
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h3239 : mixedVector B (Sum.inr 3239) = Sparse.eval nodeValue3239 (mixedVector B) := by
    change mixedMoment B node3239 node3239Labels = _
    exact sound3239 B hB hF
  have h3244 : mixedVector B (Sum.inr 3244) = Sparse.eval nodeValue3244 (mixedVector B) := by
    change mixedMoment B node3244 node3244Labels = _
    exact sound3244 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1828, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1699, h3239, h3244, h3292, h4068, reducedSource1547] using sourceEq1828 B hB

theorem rowSound1547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1547 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1547, numericCheck1547, reducedZero1547 B hB hF, mul_zero]

theorem reducedZero1548 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1548 (mixedVector B) = 0 := by
  have h1256 : mixedVector B (Sum.inr 1256) = Sparse.eval nodeValue1256 (mixedVector B) := by
    change mixedMoment B node1256 node1256Labels = _
    exact sound1256 B hB hF
  have h2628 : mixedVector B (Sum.inr 2628) = Sparse.eval nodeValue2628 (mixedVector B) := by
    change mixedMoment B node2628 node2628Labels = _
    exact sound2628 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2747 : mixedVector B (Sum.inr 2747) = Sparse.eval nodeValue2747 (mixedVector B) := by
    change mixedMoment B node2747 node2747Labels = _
    exact sound2747 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1831, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1256, h2628, h2671, h2747, h4087, reducedSource1548] using sourceEq1831 B hB

theorem rowSound1548 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1548 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1548, numericCheck1548, reducedZero1548 B hB hF, mul_zero]

theorem reducedZero1549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1549 (mixedVector B) = 0 := by
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h3057 : mixedVector B (Sum.inr 3057) = Sparse.eval nodeValue3057 (mixedVector B) := by
    change mixedMoment B node3057 node3057Labels = _
    exact sound3057 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1832, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1644, h3057, h3289, h3304, h4068, reducedSource1549] using sourceEq1832 B hB

theorem rowSound1549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1549 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1549, numericCheck1549, reducedZero1549 B hB hF, mul_zero]

theorem reducedZero1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1550 (mixedVector B) = 0 := by
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1833, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1126, h1127, h1130, h1233, h2508, h4092, reducedSource1550] using sourceEq1833 B hB

theorem rowSound1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1550 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1550, numericCheck1550, reducedZero1550 B hB hF, mul_zero]

theorem reducedZero1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1551 (mixedVector B) = 0 := by
  have h637 : mixedVector B (Sum.inr 637) = Sparse.eval nodeValue637 (mixedVector B) := by
    change mixedMoment B node637 node637Labels = _
    exact sound637 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1834, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h637, h1235, h1260, h1293, h4091, reducedSource1551] using sourceEq1834 B hB

theorem rowSound1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1551 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1551, numericCheck1551, reducedZero1551 B hB hF, mul_zero]

theorem sourceRowsAt1536 : MixedData.sourceRows (1536 : Fin 2425) =
    MixedData.row1536 := by decide +kernel

theorem sourceRowsAt1537 : MixedData.sourceRows (1537 : Fin 2425) =
    MixedData.row1537 := by decide +kernel

theorem sourceRowsAt1538 : MixedData.sourceRows (1538 : Fin 2425) =
    MixedData.row1538 := by decide +kernel

theorem sourceRowsAt1539 : MixedData.sourceRows (1539 : Fin 2425) =
    MixedData.row1539 := by decide +kernel

theorem sourceRowsAt1540 : MixedData.sourceRows (1540 : Fin 2425) =
    MixedData.row1540 := by decide +kernel

theorem sourceRowsAt1541 : MixedData.sourceRows (1541 : Fin 2425) =
    MixedData.row1541 := by decide +kernel

theorem sourceRowsAt1542 : MixedData.sourceRows (1542 : Fin 2425) =
    MixedData.row1542 := by decide +kernel

theorem sourceRowsAt1543 : MixedData.sourceRows (1543 : Fin 2425) =
    MixedData.row1543 := by decide +kernel

theorem sourceRowsAt1544 : MixedData.sourceRows (1544 : Fin 2425) =
    MixedData.row1544 := by decide +kernel

theorem sourceRowsAt1545 : MixedData.sourceRows (1545 : Fin 2425) =
    MixedData.row1545 := by decide +kernel

theorem sourceRowsAt1546 : MixedData.sourceRows (1546 : Fin 2425) =
    MixedData.row1546 := by decide +kernel

theorem sourceRowsAt1547 : MixedData.sourceRows (1547 : Fin 2425) =
    MixedData.row1547 := by decide +kernel

theorem sourceRowsAt1548 : MixedData.sourceRows (1548 : Fin 2425) =
    MixedData.row1548 := by decide +kernel

theorem sourceRowsAt1549 : MixedData.sourceRows (1549 : Fin 2425) =
    MixedData.row1549 := by decide +kernel

theorem sourceRowsAt1550 : MixedData.sourceRows (1550 : Fin 2425) =
    MixedData.row1550 := by decide +kernel

theorem sourceRowsAt1551 : MixedData.sourceRows (1551 : Fin 2425) =
    MixedData.row1551 := by decide +kernel

theorem chunkSound96 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 96) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1536 ∨ k.val = 1537 ∨ k.val = 1538 ∨ k.val = 1539 ∨ k.val = 1540 ∨ k.val = 1541 ∨ k.val = 1542 ∨ k.val = 1543 ∨ k.val = 1544 ∨ k.val = 1545 ∨ k.val = 1546 ∨ k.val = 1547 ∨ k.val = 1548 ∨ k.val = 1549 ∨ k.val = 1550 ∨ k.val = 1551 := by omega
  rcases heq with h1536 | h1537 | h1538 | h1539 | h1540 | h1541 | h1542 | h1543 | h1544 | h1545 | h1546 | h1547 | h1548 | h1549 | h1550 | h1551
  · have he : k = (1536 : Fin 2425) := Fin.ext h1536
    subst k
    rw [sourceRowsAt1536]
    exact rowSound1536 B hB hF
  · have he : k = (1537 : Fin 2425) := Fin.ext h1537
    subst k
    rw [sourceRowsAt1537]
    exact rowSound1537 B hB hF
  · have he : k = (1538 : Fin 2425) := Fin.ext h1538
    subst k
    rw [sourceRowsAt1538]
    exact rowSound1538 B hB hF
  · have he : k = (1539 : Fin 2425) := Fin.ext h1539
    subst k
    rw [sourceRowsAt1539]
    exact rowSound1539 B hB hF
  · have he : k = (1540 : Fin 2425) := Fin.ext h1540
    subst k
    rw [sourceRowsAt1540]
    exact rowSound1540 B hB hF
  · have he : k = (1541 : Fin 2425) := Fin.ext h1541
    subst k
    rw [sourceRowsAt1541]
    exact rowSound1541 B hB hF
  · have he : k = (1542 : Fin 2425) := Fin.ext h1542
    subst k
    rw [sourceRowsAt1542]
    exact rowSound1542 B hB hF
  · have he : k = (1543 : Fin 2425) := Fin.ext h1543
    subst k
    rw [sourceRowsAt1543]
    exact rowSound1543 B hB hF
  · have he : k = (1544 : Fin 2425) := Fin.ext h1544
    subst k
    rw [sourceRowsAt1544]
    exact rowSound1544 B hB hF
  · have he : k = (1545 : Fin 2425) := Fin.ext h1545
    subst k
    rw [sourceRowsAt1545]
    exact rowSound1545 B hB hF
  · have he : k = (1546 : Fin 2425) := Fin.ext h1546
    subst k
    rw [sourceRowsAt1546]
    exact rowSound1546 B hB hF
  · have he : k = (1547 : Fin 2425) := Fin.ext h1547
    subst k
    rw [sourceRowsAt1547]
    exact rowSound1547 B hB hF
  · have he : k = (1548 : Fin 2425) := Fin.ext h1548
    subst k
    rw [sourceRowsAt1548]
    exact rowSound1548 B hB hF
  · have he : k = (1549 : Fin 2425) := Fin.ext h1549
    subst k
    rw [sourceRowsAt1549]
    exact rowSound1549 B hB hF
  · have he : k = (1550 : Fin 2425) := Fin.ext h1550
    subst k
    rw [sourceRowsAt1550]
    exact rowSound1550 B hB hF
  · have he : k = (1551 : Fin 2425) := Fin.ext h1551
    subst k
    rw [sourceRowsAt1551]
    exact rowSound1551 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
