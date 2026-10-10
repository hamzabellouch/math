import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! A precise deterministic published input for boundary extensions.
Rohde–Schramm, *Basic properties of SLE*, Annals of Mathematics 161 (2005),
Theorem 4.1, pp. 898–899. A continuous Loewner driver whose tip limits form
a continuous trace has inverse maps continuous on the closed half-plane.
The input below keeps only this conclusion, composed with the continuous
inclusion into the one-point compactification. It has no stochastic or
uniform ribbon estimate. -/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

def PublishedLoewnerBoundaryExtension : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
    Continuous U → IsCapacityTwoWitness U γ G F →
    ∀ t : ℝ≥0, ∃ Fbar : ℂ → OnePoint ℂ,
      ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} ∧
      (∀ z ∈ upperHalfPlane, Fbar z = (F t z : OnePoint ℂ)) ∧
      Fbar (U t : ℂ) = (γ t : OnePoint ℂ)

theorem normalized_capacity_inverse_boundary_extension
    (hpublished : PublishedLoewnerBoundaryExtension)
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    ∃ Fbar : ℂ → OnePoint ℂ,
      ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} ∧
      (∀ z ∈ upperHalfPlane,
        Fbar z = (F t ((U t : ℂ) + (c : ℂ) * z) : OnePoint ℂ)) ∧
      Fbar 0 = (γ t : OnePoint ℂ) := by
  obtain ⟨Fb, hFb, hext, htip⟩ := hpublished U γ G F hU hw t
  let A : ℂ → ℂ := fun z => (U t : ℂ) + (c : ℂ) * z
  have hA : Continuous A := continuous_const.add (continuous_const.mul continuous_id)
  have him : ∀ z, (A z).im = c * z.im := by intro z; simp [A]
  refine ⟨Fb ∘ A, hFb.comp hA.continuousOn (fun z hz => ?_), ?_, ?_⟩
  · change 0 ≤ (A z).im
    rw [him]
    exact mul_nonneg hc.le hz
  · intro z hz
    exact hext (A z) (by change 0 < (A z).im; rw [him]; exact mul_pos hc hz)
  · simpa only [Function.comp_apply, A, mul_zero, add_zero] using htip

end SLEExactGauge

end

end OAI
