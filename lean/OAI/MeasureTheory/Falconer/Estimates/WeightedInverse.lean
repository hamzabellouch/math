import OAI.MeasureTheory.Falconer.Estimates.InverseScale
import OAI.MeasureTheory.Falconer.Fourier.StationaryWeightCancellation

namespace OAI

/-! # The stationary inverse with the original distance weight

After multiplication by `‖z‖^(-(d-1)/2)`, the only spatial powers in
the finite expansion have integer exponents. These are exactly the
powers handled by the spatial Fourier separation.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

noncomputable def weightedInverseDisplacementSum (m J : ℕ) (r : ℝ)
    (z : Space (m+3)) (B : Space (m+3) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (J+1),
    ((r^(((m+2 : ℕ) : ℝ)/2)*(r^j)⁻¹*(‖z‖^j)⁻¹ : ℝ) : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space (m+3)) z : ℂ))*
          localInverseAmplitude m B j w ∂sphereMeasure (m+3)

theorem weightedInverseDisplacementSum_eq (m J : ℕ) {r : ℝ}
    (hr : 0 < r) (z : Space (m+3)) (hz : z ≠ 0) (B : Space (m+3) → ℂ) :
    weightedInverseDisplacementSum m J r z B =
      ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ) *
        (((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) *
          inverseDisplacementSum m J r z B := by
  unfold weightedInverseDisplacementSum inverseDisplacementSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc,← Complex.ofReal_mul,← Complex.ofReal_mul,
    stationary_weighted_inverse_power (m+2) j hr (norm_pos_iff.mpr hz)]

theorem exists_weighted_displacement_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ r : ℝ, 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖weightedInverseDisplacementSum m J r z B -
          ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        ‖z‖^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T) := by
  obtain ⟨J,A,hA,hb⟩ := exists_displacement_inverse_order hgnomonic hquadratic m hκ
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDR z hz he B hB C hC hBD r hr hratio
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrp : 0 < r := (mul_pos_iff_of_pos_right hzp).mp (zero_lt_one.trans_le hr)
  rw [weightedInverseDisplacementSum_eq m J hrp z hz B]
  have heq :
      ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
          (((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
        ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
          Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z) =
      ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
        ((((r*‖z‖)^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*inverseDisplacementSum m J r z B -
          Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)) := by ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hzp _)]
  exact (mul_le_mul_of_nonneg_left
    (hb R D hR hD hDR z hz he B hB C hC hBD r hr hratio)
    (Real.rpow_pos_of_pos hzp _).le).trans_eq (by ring)

end Falconer

end OAI
