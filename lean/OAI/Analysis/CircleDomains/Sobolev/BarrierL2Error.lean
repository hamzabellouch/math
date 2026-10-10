import OAI.Analysis.CircleDomains.Sobolev.BarrierDifferentialError
import OAI.Analysis.CircleDomains.Sobolev.L2ThreeTermBound

namespace OAI

/-! The manuscript's three-term barrier estimate, including the energy
on the altered horizontal support. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem barrier_L2_error
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace X]
    {μ : Measure X} (S : Set X) (hS : MeasurableSet S)
    (A H : X → F) (DA DH : X → E →L[ℝ] F) (Φ : F → ℝ)
    {M₁ M₂ e : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hbound : ∀ y, ‖fderiv ℝ Φ y‖ ≤ M₁)
    (hlip : ∀ y z, ‖fderiv ℝ Φ y-fderiv ℝ Φ z‖ ≤ M₂*‖y-z‖)
    (hclose : ∀ x ∉ S, ‖A x-H x‖ ≤ e)
    (hD : AEStronglyMeasurable (fun x =>
      (fderiv ℝ Φ (A x)).comp (DA x)-(fderiv ℝ Φ (H x)).comp (DH x)) μ)
    (herror : MemLp (fun x => DA x-DH x) 2 μ) (hH : MemLp DH 2 μ) :
    let D := fun x => (fderiv ℝ Φ (A x)).comp (DA x)-(fderiv ℝ Φ (H x)).comp (DH x)
    MemLp D 2 μ ∧ (eLpNorm D 2 μ).toReal ≤
      M₁*(eLpNorm (fun x => ‖DA x-DH x‖) 2 μ).toReal +
      (M₂*e)*(eLpNorm (fun x => ‖DH x‖) 2 μ).toReal +
      (2*M₁)*(eLpNorm (S.indicator (fun x => ‖DH x‖)) 2 μ).toReal := by
  apply l2_three_term_bound hM₁ (mul_nonneg hM₂ he) (mul_nonneg (by norm_num) hM₁)
    hD herror.norm hH.norm (hH.norm.indicator hS)
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => norm_nonneg _))
  · exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · simpa only [indicator_of_mem hx] using norm_nonneg (DH x)
      · simp only [indicator_of_notMem hx, le_refl]
  · exact Eventually.of_forall fun x => by
      have h := barrier_differential_error S A H DA DH Φ hM₁ hM₂ he hbound hlip hclose x
      by_cases hx : x ∈ S
      · simpa only [indicator_of_mem hx, mul_assoc] using h
      · simpa only [indicator_of_notMem hx, mul_assoc] using h

end CircleDomainRigidity

end

end OAI
