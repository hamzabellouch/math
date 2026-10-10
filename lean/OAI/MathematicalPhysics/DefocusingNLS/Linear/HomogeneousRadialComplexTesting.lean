import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialTesting

namespace OAI

/-! # Complex radial integration by parts on the Schwartz core -/

open MeasureTheory Set LineDeriv
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- The complex bilinear form of radial integration by parts. -/
theorem schwartz_radial_integral_mul_by_parts (N : ℕ) (ψ : 𝓢(ℝ, ℂ))
    (f : 𝓢(E, ℂ)) (ω : PhysicalUnitSphere) :
    (∫ r : ℝ, ψ r *
      (∑ j : Fin N → Fin 12, (radialTensorCoefficient N j ω : ℂ) *
        homogeneousOrderedDerivative N j f (r • ω.1))) =
      (-1 : ℂ) ^ N * ∫ r : ℝ,
        ((∂^{fun _ : Fin N => (1 : ℝ)} ψ) r) * f (r • ω.1) := by
  have hibp (M : ℕ) (v : Fin M → ℝ) (φ g : 𝓢(ℝ, ℂ)) :
      (∫ r : ℝ, φ r * ((∂^{v} g) r)) =
        (-1 : ℂ) ^ M * ∫ r : ℝ, ((∂^{fun i => v (Fin.rev i)} φ) r) * g r := by
    induction M generalizing φ g with
    | zero => simp
    | succ M ih =>
        rw [iteratedLineDerivOp_succ_left]
        have h := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
          (μ := (volume : Measure ℝ)) φ (∂^{Fin.tail v} g)
          (ContinuousLinearMap.mul ℝ ℂ) (v 0)
        change (∫ r : ℝ, φ r * ((∂_{v 0} (∂^{Fin.tail v} g)) r)) =
          -(∫ r : ℝ, ((∂_{v 0} φ) r) * ((∂^{Fin.tail v} g) r)) at h
        rw [h, ih (Fin.tail v) (∂_{v 0} φ) g]
        have ht : (∂^{fun i => v (Fin.rev i)} φ) =
            ∂^{fun i => Fin.tail v (Fin.rev i)} (∂_{v 0} φ) := by
          rw [iteratedLineDerivOp_succ_right]
          simp only [Fin.rev_last]
          congr 1
          funext i
          simp only [Fin.init_def, Fin.tail_def, Fin.rev_castSucc]
        rw [ht, pow_succ]
        ring
  have h := hibp N (fun _ : Fin N => (1 : ℝ)) ψ (schwartzRadialRestriction ω f)
  have hj (r : ℝ) : (∂^{fun _ : Fin N => (1 : ℝ)}
      (schwartzRadialRestriction ω f)) r =
      ∑ j : Fin N → Fin 12, (radialTensorCoefficient N j ω : ℂ) *
        homogeneousOrderedDerivative N j f (r • ω.1) := by
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    change iteratedDeriv N (fun t : ℝ => f (t • ω.1)) r = _
    exact schwartz_radial_iteratedDeriv N f ω r
  simpa only [hj, schwartzRadialRestriction_apply] using h


end DefocusingNLS

end OAI
