import OAI.MeasureTheory.Falconer.Angular.CircleAngularBins
import OAI.MeasureTheory.Falconer.Angular.AngularTransformSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def AngularLabelEligible (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℂ) (n j : ℕ) : Prop :=
  ∃ ω ∈ tsupport (circleAngularBin n j), ¬ ∀ᵐ x ∂ρ.restrict X, b x ω = 0

theorem ineligible_symbol_zero_ae {ρ : Measure Plane} {X : Set Plane}
    {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : ¬ AngularLabelEligible ρ X b n j) {ω : UnitCircle}
    (hω : ω ∈ tsupport (circleAngularBin n j)) :
    ∀ᵐ x ∂ρ.restrict X, b x ω = 0 := by
  by_contra hh
  exact h ⟨ω,hω,hh⟩

theorem ineligible_transform_zero {ρ : Measure Plane} {X : Set Plane}
    {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : ¬ AngularLabelEligible ρ X b n j) (M r : ℝ) (ω : UnitCircle) :
    (circleAngularBin n j ω : ℂ) * sourceAngularTransform ρ X M b r ω = 0 := by
  by_cases hω : circleAngularBin n j ω = 0
  · simp [hω]
  · have he := ineligible_symbol_zero_ae h (subset_closure hω)
    have hi : (∫ x in X, Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (ω : Plane) x : ℂ))*b x ω ∂ρ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [he] with x hx
      simp [hx]
    simp only [sourceAngularTransform, hi, smul_zero, mul_zero]

theorem eligible_label_witness {ρ : Measure Plane} {X : Set Plane}
    (hX : MeasurableSet X) {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : AngularLabelEligible ρ X b n j) (G : Plane → UnitCircle → Prop)
    (hG : ∀ ω, ∀ᵐ x ∂ρ.restrict X, b x ω ≠ 0 → G x ω) :
    ∃ ω ∈ tsupport (circleAngularBin n j), ∃ x ∈ X, b x ω ≠ 0 ∧ G x ω := by
  classical
  obtain ⟨ω,hω,hnon⟩ := h
  refine ⟨ω,hω,?_⟩
  by_contra hh
  apply hnon
  filter_upwards [ae_restrict_mem hX, hG ω] with x hx hg
  by_contra hb
  exact hh ⟨x,hx,hb,hg hb⟩

theorem eligible_label_good_direction {ρ : Measure Plane} {X : Set Plane}
    (hX : MeasurableSet X) {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : AngularLabelEligible ρ X b n j) (G : Set UnitCircle)
    (hG : ∀ x ∈ X, ∀ ω, b x ω ≠ 0 → ω ∈ G) :
    ∃ ω ∈ tsupport (circleAngularBin n j), ω ∈ G := by
  obtain ⟨ω,hω,x,hx,hb,hgood⟩ := eligible_label_witness hX h (fun _ ω => ω ∈ G)
    (fun ω => by filter_upwards [ae_restrict_mem hX] with x hx; exact hG x hx ω)
  exact ⟨ω,hω,hgood⟩

end PlanarFalconer

end OAI
