import OAI.Geometry.RCD.Sobolev.HarmonicScaledEnergy
import OAI.Geometry.RCD.Harmonic.HomogeneousAffineImprovement

namespace OAI

/-! # Interior gradient bounds at the actual coordinate normalization -/

open Set Metric Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_harmonic_scaled_energy_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S R M : ℝ} (hS : 0<S) (hR : 0≤R) (hRS : R<S) (hM : 0<M)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*r k^2)
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤M) :
    ∃ B : ℝ, 0≤B ∧ ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤B := by
  let μ := hausdorff n X
  let v := fun k => M⁻¹ • w k
  have hv (k : ℕ) : harmonicTargetNorm hX (p k) (S*r k) (v k)≤1 := by
    rw [harmonicTargetNorm_smul,abs_of_pos (inv_pos.mpr hM)]
    exact (mul_le_mul_of_nonneg_left (hnorm k) (inv_pos.mpr hM).le).trans_eq
      (inv_mul_cancel₀ hM.ne')
  obtain ⟨B,hB,hb⟩ := hX.harmonic_scaled_energy_bound hn hS hR hRS p r hr hcurv v
    (fun k => (hw k).smul μ hX.quadratic M⁻¹) hv
  refine ⟨M^2*B,mul_nonneg (sq_nonneg _) hB,?_⟩
  intro k
  filter_upwards [hb k,
    ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic M⁻¹ (w k) (M⁻¹ • w k)),
    ae_restrict_of_ae (localGamma_smul_right μ hX.quadratic M⁻¹ (w k) (w k))] with x hx hl hr'
  change r k^2*localGamma μ hX.quadratic (M⁻¹ • w k) (M⁻¹ • w k) x≤B at hx
  rw [hl,hr'] at hx
  calc _ = M^2*(r k^2*(M⁻¹*(M⁻¹*localGamma μ hX.quadratic (w k) (w k) x))) := by field_simp; rfl
       _ ≤ M^2*B := mul_le_mul_of_nonneg_left hx (sq_nonneg _)

end RegularPointCoordinates

end

end OAI
