import OAI.Analysis.StrictMeans.TransportLimit

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma ae_bad_base_positive_zero (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), (f,UpperHalfPlane.I)∉sourcePairingDomain ((β+2)/3) →
      jacobianPart ((β+2)/3) f true UpperHalfPlane.I = 0 := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  have hm : Measurable (fun f : DiskFamily => ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      badSourceTest k (f,UpperHalfPlane.I)) :=
    (((continuous_jacobianPart k true).measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul
      ((measurable_badSourceTest hk).comp (measurable_id.prodMk measurable_const))
  have hz := (lintegral_eq_zero_iff' hm.aemeasurable).mp (affine_law_base_good μ β hβ hlaw)
  filter_upwards [hz] with f hf
  intro hD
  have hDc : (f,UpperHalfPlane.I) ∈ (sourcePairingDomain k)ᶜ := hD
  simp only [badSourceTest,indicator_of_mem hDc,mul_one,Pi.zero_apply] at hf
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hf) (jacobianPart_nonneg k f true _)

lemma ae_base_positive_le_weighted (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    ∀ᵐ f ∂(μ : Measure DiskFamily),
      ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) ≤
      ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) *
        ENNReal.ofReal (partnerRatio ((β+2)/3) (f,UpperHalfPlane.I)) := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  filter_upwards [ae_bad_base_positive_zero μ β hβ hlaw] with f hf
  by_cases hD : (f,UpperHalfPlane.I)∈sourcePairingDomain k
  · have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (partnerRatio k (f,UpperHalfPlane.I)) := by
      exact_mod_cast ENNReal.ofReal_le_ofReal (partnerRatio_gt_one hk hD).le
    simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I))) hc
  · simp only [hf hD,ENNReal.ofReal_zero,zero_mul,le_refl]

lemma transport_positive_le_negative (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≤
      ∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  exact (lintegral_mono_ae (ae_base_positive_le_weighted μ β hβ hlaw)).trans
    (weighted_transport_le μ β hlaw (by linarith) (by ring))

lemma transport_equality_ae_zero (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β)
    (he : (∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) =
      ∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression ((β+2)/3) (halfPlaneFunction f) I = 0 := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  have hfin : (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≠ ⊤ := by
    rw [lintegral_jacobianPart_base]
    exact ENNReal.ofReal_ne_top
  have hm : Measurable (fun f : DiskFamily => ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      ENNReal.ofReal (partnerRatio k (f,UpperHalfPlane.I))) :=
    (((continuous_jacobianPart k true).measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul
      (((measurable_partnerRatio hk).comp (measurable_id.prodMk measurable_const)).ennreal_ofReal)
  have ha := ae_eq_of_ae_le_of_lintegral_le (ae_base_positive_le_weighted μ β hβ hlaw) hfin
    hm.aemeasurable (he ▸ weighted_transport_le μ β hlaw hk (by ring))
  have hp : ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianPart k f true UpperHalfPlane.I = 0 := by
    filter_upwards [ha,ae_bad_base_positive_zero μ β hβ hlaw] with f hf hb
    by_cases hD : (f,UpperHalfPlane.I)∈sourcePairingDomain k
    · have hc := partnerRatio_gt_one hk hD
      have hre := congrArg ENNReal.toReal hf
      rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (jacobianPart_nonneg k f true _),
        ENNReal.toReal_ofReal (partnerRatio_nonneg hk _)] at hre
      nlinarith [jacobianPart_nonneg k f true UpperHalfPlane.I]
    · exact hb hD
  have hnzero : (∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) = 0 := by
    rw [← he]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hp] with f hf
    change ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) = 0
    rw [hf,ENNReal.ofReal_zero]
  have hmn : Measurable (fun f : DiskFamily => ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I)) :=
    ((continuous_jacobianPart k false).measurable.comp
    (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have hn := (lintegral_eq_zero_iff' hmn.aemeasurable).mp hnzero
  filter_upwards [hp,hn] with f hf hg
  have hnle := ENNReal.ofReal_eq_zero.mp hg
  change max (jacobianExpression k (halfPlaneFunction f) I) 0 = 0 at hf
  change max (-jacobianExpression k (halfPlaneFunction f) I) 0 ≤ 0 at hnle
  exact le_antisymm ((le_max_left _ _).trans hf.le) (by linarith [le_max_left (-jacobianExpression k (halfPlaneFunction f) I) 0])

lemma expected_jacobian_as_parts (μ : ProbabilityMeasure DiskFamily) (k : ℝ) :
    (∫ f, jacobianExpression k (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) =
      (∫ f, jacobianPart k f true UpperHalfPlane.I ∂(μ : Measure DiskFamily)) -
      ∫ f, jacobianPart k f false UpperHalfPlane.I ∂(μ : Measure DiskFamily) := by
  rw [← integral_sub (integrable_jacobianPart_base μ k true) (integrable_jacobianPart_base μ k false)]
  apply integral_congr_ae
  filter_upwards [] with f
  simp only [jacobianPart,Bool.false_eq_true,↓reduceIte,UpperHalfPlane.coe_I]
  by_cases h : 0 ≤ jacobianExpression k (halfPlaneFunction f) I
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
    ring

theorem strict_weighted_transport (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    (∫ f, jacobianExpression ((β+2)/3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) ≤ 0 ∧
      ((∫ f, jacobianExpression ((β+2)/3) (halfPlaneFunction f) I ∂(μ : Measure DiskFamily)) = 0 →
        ∀ᵐ f ∂(μ : Measure DiskFamily), jacobianExpression ((β+2)/3) (halfPlaneFunction f) I = 0) := by
  have hN : 0 ≤ ∫ f, jacobianPart ((β+2)/3) f false UpperHalfPlane.I ∂(μ : Measure DiskFamily) :=
    integral_nonneg (fun f => jacobianPart_nonneg ((β+2)/3) f false UpperHalfPlane.I)
  have hi := transport_positive_le_negative μ β hβ hlaw
  simp only [lintegral_jacobianPart_base] at hi
  have hre := (ENNReal.ofReal_le_ofReal_iff hN).mp hi
  rw [expected_jacobian_as_parts]
  refine ⟨sub_nonpos.mpr hre,?_⟩
  intro he
  apply transport_equality_ae_zero μ β hβ hlaw
  simp only [lintegral_jacobianPart_base,sub_eq_zero.mp he]

end
end StrictInverseFirstPower

end

end OAI
