import OAI.MeasureTheory.Falconer.Angular.SharedAngular
import OAI.MeasureTheory.Falconer.Fourier.EndpointTransform

namespace OAI

/-! # Terminal independent angular energies in every dimension

Only the sup norm of the actual endpoint symbols and the two original
cell masses enter the stopping estimate. The radial shell measure is
normalized, so its total mass has no frequency factor.
-/

namespace Falconer
open MeasureTheory Set

theorem independentAngularEnergy_bound {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V ≤
      (2:ℝ)^((d:ℝ)*(v-a)) * (C^2*D^2*(sphereMeasure d).real univ^2) *
        (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hb : ∀ r, ‖sphereMoment U r*sphereMoment V r‖ ≤
      C^2*D^2*(sphereMeasure d).real univ^2 := by
    intro r
    rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))]
    calc
      _ ≤ (C^2*(sphereMeasure d).real univ)*(D^2*(sphereMeasure d).real univ) :=
        mul_le_mul (sphereMoment_le U hC hbU r) (sphereMoment_le V hD hbV r)
          (sphereMoment_nonneg V r) (by positivity)
      _ = _ := by ring
  unfold independentAngularEnergy
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := PlanarFalconer.sourceAngularShellMeasure v Ψ) (Filter.Eventually.of_forall hb)
  have hn : 0 ≤ ∫ r, sphereMoment U r*sphereMoment V r
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ :=
    integral_nonneg (fun r => mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))
  rw [Real.norm_eq_abs,abs_of_nonneg hn] at hnorm
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (by ring)

theorem endpoint_angular_terminal {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    {W B ℓ R : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hΨsupport : ∀ t, 4 < t → Ψ t = 0) (hB : 0 ≤ B) (hR : 0 < R)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hm₁ : μ.real univ/M₁ ≤ R^ℓ) (hm₂ : ν.real univ/M₂ ≤ R^ℓ)
    (b c : Space d → Sphere d → ℂ)
    (hb : ∀ x w, ‖b x w‖ ≤ B) (hc : ∀ x w, ‖c x w‖ ≤ B) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform μ M₁ b z.1 z.2)
      (fun z => endpointTransform ν M₂ c z.1 z.2) ≤
    (4*W*B^4*(sphereMeasure d).real univ^2)*
      (2:ℝ)^((d:ℝ)*(v-a))*R^(4*ℓ) := by
  let := PlanarFalconer.sourceAngularShellMeasure_finite v Ψ hW hΨW hΨsupport
  have hbound₁ (z : ℝ × Sphere d) : ‖endpointTransform μ M₁ b z.1 z.2‖ ≤ B*R^ℓ := by
    exact (endpointTransform_norm_le μ hM₁ b hb z.1 z.2).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm₁ hB)
  have hbound₂ (z : ℝ × Sphere d) : ‖endpointTransform ν M₂ c z.1 z.2‖ ≤ B*R^ℓ := by
    exact (endpointTransform_norm_le ν hM₂ c hc z.1 z.2).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm₂ hB)
  have h := independentAngularEnergy_bound a v Ψ _ _
    (mul_nonneg hB (Real.rpow_nonneg hR.le _))
    (mul_nonneg hB (Real.rpow_nonneg hR.le _)) hbound₁ hbound₂
  apply h.trans
  calc
    _ ≤ (2:ℝ)^((d:ℝ)*(v-a)) *
        ((B*R^ℓ)^2*(B*R^ℓ)^2*(sphereMeasure d).real univ^2)*(4*W) :=
      mul_le_mul_of_nonneg_left
        (PlanarFalconer.sourceAngularShellMeasure_real_mass_le v Ψ hW hΨW hΨsupport)
        (by positivity)
    _ = _ := by
      have hr : (R^ℓ)^4 = R^(4*ℓ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
        congr 1
        ring
      calc
        _ = (4*W*B^4*(sphereMeasure d).real univ^2)*
            (2:ℝ)^((d:ℝ)*(v-a))*(R^ℓ)^4 := by ring
        _ = _ := by rw [hr]

end Falconer

end OAI
