import OAI.Geometry.RCD.Harmonic.ProductProjectionSmallFactor

namespace OAI

/-! # Full-dimensional product approximations give actual coordinates

The modulus depends only on the dimension and requested error. No ambient
Euclidean approximation or residual-factor geometry is assumed.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.product_projection_of_packing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Z : Type*) (dZ : MetricSpace Z), letI := dZ
      ∀ (p : X) (z₀ : Z) (r : ℝ), 0 < r → -1 ≤ K*(4*r)^2 →
      ∀ f : X → WithLp 2 (Euclidean n × Z),
        IsPointedApproximation p (WithLp.toLp 2 (0,z₀)) r 1 ε f →
        IsPointedApproximation p 0 r (1/16) η (fun x => (f x).fst) := by
  let a := η/4
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨δ,hδ,hfactor⟩ := hX.residual_factor_small hn ha
  let ε := min δ (min (1/16) (η/12))
  have he : 0 < ε := lt_min hδ (lt_min (by norm_num) (by positivity))
  have heδ : ε ≤ δ := min_le_left _ _
  have he16 : ε ≤ 1/16 := (min_le_right _ _).trans (min_le_left _ _)
  have heη : ε ≤ η/12 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,he,?_⟩
  intro Z dZ p z₀ r hr hcurv f hf
  have hsmall := hfactor Z dZ p z₀ r hr hcurv f (hf.mono_error heδ)
  apply (product_projection_small_factor hr he.le he16 ha.le hf hsmall).mono_error
  dsimp only [a]
  linarith

end RegularPointCoordinates

end

end OAI
