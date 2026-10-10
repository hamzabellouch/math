import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

def localPiolaFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) (y : E) : E := by
  classical
  exact if y ∈ X.target then
    |(fderiv ℝ X (X.symm y)).det|⁻¹ • fderiv ℝ X (X.symm y) (F (X.symm y))
  else 0

lemma localPiolaFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) :
    Function.support (localPiolaFlux X F) ⊆ X '' (Function.support F ∩ X.source) := by
  intro y hy
  by_cases hyt : y ∈ X.target
  · refine ⟨X.symm y, ⟨?_, X.map_target hyt⟩, X.right_inv hyt⟩
    intro hz
    exact hy (by simp [localPiolaFlux, hyt, hz])
  · exact False.elim (hy (by simp [localPiolaFlux, hyt]))

lemma localPiolaFlux_hasCompactSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) (hF : HasCompactSupport F)
    (hs : tsupport F ⊆ X.source) : HasCompactSupport (localPiolaFlux X F) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hF.image_of_continuousOn (X.continuousOn.mono hs))
  exact (localPiolaFlux_support X F).trans (image_mono (fun _ hx => subset_closure hx.1))

lemma localPiolaFlux_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) (hF : HasCompactSupport F)
    (hs : tsupport F ⊆ X.source) : tsupport (localPiolaFlux X F) ⊆ X.target := by
  have hc : IsClosed (X '' tsupport F) :=
    (hF.image_of_continuousOn (X.continuousOn.mono hs)).isClosed
  exact (closure_minimal ((localPiolaFlux_support X F).trans
    (image_mono (fun _ hx => subset_closure hx.1))) hc).trans
      (by rintro y ⟨x, hx, rfl⟩; exact X.map_source (hs hx))

lemma local_fderiv_symm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target) {x : E} (hx : x ∈ X.source) :
    (fderiv ℝ X.symm (X x)).comp (fderiv ℝ X x) = ContinuousLinearMap.id ℝ E := by
  have hd := (hX x hx).differentiableAt (X.open_source.mem_nhds hx)
  have hdi := (hXi _ (X.map_source hx)).differentiableAt
    (X.open_target.mem_nhds (X.map_source hx))
  rw [← fderiv_comp x hdi hd]
  have he : (X.symm ∘ X) =ᶠ[𝓝 x] id := by
    filter_upwards [X.open_source.mem_nhds hx] with y hy
    exact X.left_inv hy
  rw [he.fderiv_eq, fderiv_id]

lemma local_fderiv_det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target) {x : E} (hx : x ∈ X.source) :
    (fderiv ℝ X x).det ≠ 0 := by
  have he := congrArg (fun L : E →L[ℝ] E => L.det) (local_fderiv_symm_comp X hX hXi hx)
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_id, LinearMap.det_comp, LinearMap.det_id] at he
  exact right_ne_zero_of_mul_eq_one he

lemma integral_eq_setIntegral_of_zero_off {E V : Type*} [MeasurableSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure E) (s : Set E)
    (f : E → V) (hf : ∀ x ∉ s, f x = 0) : (∫ x, f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_univ]
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ s) (fun x hx => hf x hx.2))

theorem localPiolaFlux_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hdet : ∀ x ∈ X.source, (fderiv ℝ X x).det ≠ 0)
    (F : E → E) (hF : Function.support F ⊆ X.source)
    (ψ : E → ℝ) (hψ : Differentiable ℝ ψ) :
    (∫ y, fderiv ℝ ψ y (localPiolaFlux X F y) ∂μ) =
      ∫ x, fderiv ℝ (ψ ∘ X) x (F x) ∂μ := by
  rw [integral_eq_setIntegral_of_zero_off μ X.target _ (by
    intro y hy; simp [localPiolaFlux, hy])]
  have hs : X '' X.source = X.target := X.image_source_eq_target
  rw [← hs, integral_image_eq_integral_abs_det_fderiv_smul μ
    X.open_source.measurableSet
    (fun x hx => ((hX x hx).differentiableAt (X.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt)
    X.injOn]
  rw [integral_eq_setIntegral_of_zero_off μ X.source
    (fun x => fderiv ℝ (ψ ∘ X) x (F x)) (by
      intro x hx
      have hz : F x = 0 := Function.notMem_support.mp (notMem_subset hF hx)
      simp [hz])]
  apply setIntegral_congr_fun X.open_source.measurableSet
  intro x hx
  simp only [localPiolaFlux, ite_eq_left (X.map_source hx), X.left_inv hx,
    map_smul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr (hdet x hx)), one_mul]
  rw [fderiv_comp x (hψ _) ((hX x hx).differentiableAt (X.open_source.mem_nhds hx))]
  rfl

end ScalarConductivity

end

end OAI
