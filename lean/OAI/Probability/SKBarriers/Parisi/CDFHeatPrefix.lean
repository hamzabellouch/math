import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFChainAverage
import OAI.Probability.SKBarriers.Parisi.CDFSuffixSemigroup

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gaussianHeat (v : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x+v*z) ∂gaussianReal 0 1

theorem gaussianHeat_hasDerivAt {f df : ℝ → ℝ} (hf : BoundedDerivs f)
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {C : ℝ} (hb : ∀ x, |df x|  ≤  C) (v x : ℝ) :
    HasDerivAt (gaussianHeat v f) (gaussianHeat v df x) x := by
  let L : ℝ →L[ℝ] ℝ := v • ContinuousLinearMap.id ℝ ℝ
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ) (x₀:=x)
    (F:=fun a z => f (a+v*z)) (F':=fun a z => df (a+v*z)) (bound:=fun _ : ℝ => C)
    (by simp) _ _ _ _ (integrable_const C) _).2
  · exact Eventually.of_forall (fun a => (hf.1.continuous.comp (by fun_prop)).aestronglyMeasurable)
  · exact ((hf.translate x).compCLM L).hasExpGrowth.integrable_gaussianMeasure
      ((hf.translate x).compCLM L).1.continuous
  · exact (hc.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun z a _ => by simpa only [Real.norm_eq_abs] using hb (a+v*z))
  · exact ae_of_all _ (fun z a _ => by
      convert (hd (a+v*z)).comp a ((hasDerivAt_id a).add_const (v*z)) using 1 <;> first | rfl | simp)

theorem scalarCDFOperator_zero_on {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1)
    (hz : ∀ z∈Ico s (s+t), α z=0) :
    scalarCDFOperator β α s t f=gaussianHeat (β*Real.sqrt (t:ℝ)) f := by
  funext x
  rw [scalarCDFOperator_eq_chain hf hK β ha hm [(0,t)] (by simp) s t ht (by simp)
    (show TimeChainModels α s [(0,t)] from ⟨hz,True.intro⟩)]
  simp [scalarTimeChain,scalarTimeStep,scalarStep,gaussianStep,gaussianHeat]

theorem scalarCDFAverage_zero_on {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hc : Continuous dg)
    {K B C : ℝ≥0} (hK : LipschitzWith K f)
    (hB : ∀ y, |g y|  ≤  B) (hC : ∀ y, |dg y|  ≤  C)
    (β : ℝ) {α : ℝ → ℝ} (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (hz : ∀ z∈Ico s (s+t), α z=0) (x : ℝ) :
    scalarCDFAverage β α s t f g x=gaussianHeat (β*Real.sqrt (t:ℝ)) g x := by
  rw [scalarCDFAverage_eq_chainAverage hf hg hc hK hB hC β ha hm [(0,t)] (by simp)
    s t ht (by simp) (show TimeChainModels α s [(0,t)] from ⟨hz,True.intro⟩)]
  simp [scalarTimeChainAverage,scalarHierarchyAverage,scalarStepAverage,gaussianAverage,
    gaussianStepLaw,gaussianHeat]

theorem scalarCDFGradient_heat_prefix (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0 ≤ s) (hsq : s ≤ q) (hq : q ≤ 1) (hz : ∀ z∈Ico s q, α z=0) :
    scalarCDFGradient β α s (Real.toNNReal (1-s))=
      gaussianHeat (β*Real.sqrt (q-s)) (scalarCDFGradient β α q (Real.toNNReal (1-q))) := by
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hu : Real.toNNReal (1-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have he := scalarCDFValue_suffix_semigroup β α ha h1 hs hsq hq
  rw [scalarCDFOperator_zero_on (scalarCDFValue_regular β ha α.mono q _ hr)
    (scalarCDFValue_lipschitz β ha α.mono q _ hr) β ha α.mono s _ ht
    (by simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr hsq),add_sub_cancel] using hz),
    Real.coe_toNNReal _ (sub_nonneg.mpr hsq)] at he
  funext x
  have HD := scalarCDFValue_hasDerivAt β ha α.mono s _ hu x
  rw [he] at HD
  exact HD.unique (gaussianHeat_hasDerivAt (scalarCDFValue_regular β ha α.mono q _ hr)
    (scalarCDFValue_hasDerivAt β ha α.mono q _ hr)
    (scalarCDFGradient_lipschitz β ha α.mono q _ hr).continuous
    (fun y => (scalarCDF_derivative_bounds β ha α.mono q _ hr y).1) _ x)

theorem scalarCDFOverlap_heat_prefix (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) (hz : ∀ z∈Ico 0 q, α z=0) :
    scalarCDFOverlap β α q=∫ z, (scalarCDFGradient β α q (Real.toNNReal (1-q))
      (β*Real.sqrt q*z))^2 ∂gaussianReal 0 1 := by
  have ht : Real.toNNReal q ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; exact hq.2
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [hq.1]
  obtain ⟨hd,hc,hB,hC⟩ := scalarCDFGradient_sq_regular β ha hm q _ hr
  unfold scalarCDFOverlap
  rw [scalarCDFAverage_zero_on (B:=1) (C:=2) (scalarCDFValue_regular β ha hm q _ hr) hd hc
    (scalarCDFValue_lipschitz β ha hm q _ hr) hB hC β ha hm 0 _ ht
    (by simpa only [zero_add,Real.coe_toNNReal _ hq.1] using hz)]
  simp only [gaussianHeat,Real.coe_toNNReal _ hq.1,zero_add]

end SK.Analytic

end
end

end OAI
