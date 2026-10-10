import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.InteriorRegularity

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_product (L : E ≃L[ℝ] E) (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    linearDistribution L (smulLeftCLM F g u) =
      smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g) (linearDistribution L u) := by
  ext φ
  simp only [linearDistribution_apply,smulLeftCLM_apply_apply]
  congr 1
  ext x
  change SchwartzMap.smulLeftCLM ℂ g (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) x =
    SchwartzMap.smulLeftCLM ℂ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g) φ (L x)
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g).hasTemperateGrowth]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [CompleteSpace G] in
lemma linearDistribution_postcomp (L : E ≃L[ℝ] E) (K : F →L[ℂ] G) (u : 𝓢'(E,F)) :
    linearDistribution L (HilbertSobolev.fiberMap K u) =
      HilbertSobolev.fiberMap K (linearDistribution L u) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_inverse (L : E ≃L[ℝ] E) (u : 𝓢'(E,F)) :
    linearDistribution L.symm (linearDistribution L u) = u := by
  ext φ
  simp only [linearDistribution_apply]
  congr 1
  ext x
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

omit [CompleteSpace F] in
lemma linearDistribution_schwartz (L : E ≃L[ℝ] E) (f : 𝓢(E,F)) :
    linearDistribution L (f : 𝓢'(E,F)) =
      ((|(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| •
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f : 𝓢(E,F)) : 𝓢'(E,F)) := by
  ext φ
  rw [linearDistribution_apply]
  simp only [SchwartzMap.coe_apply]
  let c : ℝ := |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹|
  have hm := L.toHomeomorph.measurableEmbedding.integral_map
    (μ := (volume : Measure E)) (fun y => φ y • f (L.symm y))
  change (∫ y, φ y • f (L.symm y) ∂Measure.map L volume) =
    ∫ x, φ (L x) • f (L.symm (L x)) at hm
  rw [show Measure.map L volume = ENNReal.ofReal c • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at hm
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hm
  change (∫ x, φ (L x) • f x) = ∫ y, φ y • (c • f (L.symm y))
  rw [← hm,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact smul_comm c (φ y) _

lemma memSobolevLoc_linear (n : ℕ) (L : E ≃L[ℝ] E) {U : Set E} {u : 𝓢'(E,F)}
    (hu : HilbertSobolev.MemSobolevLoc U n u) :
    HilbertSobolev.MemSobolevLoc (L.symm ⁻¹' U) n (linearDistribution L u) := by
  intro g hg hgU
  let q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L g
  have hq : HasCompactSupport (q : E → ℂ) := hg.comp_homeomorph L.toHomeomorph
  have hqU : tsupport q ⊆ U := by
    have he : tsupport q = L ⁻¹' tsupport g := tsupport_comp_eq_preimage g L.toHomeomorph
    rw [he]
    intro x hx
    have h := hgU hx
    simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using h
  have h := memSobolev_nat_linear n L (hu q hq hqU)
  rw [linearDistribution_product] at h
  have he : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm q = g := by
    ext x
    simp only [q,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rwa [he] at h

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
