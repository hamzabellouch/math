import OAI.MeasureTheory.Falconer.Estimates.WeightedInverse

namespace OAI

/-! # The inverse expansion at the actual cell scale

Only the distance weight is rescaled. The oscillatory phase still uses the
original displacement and original radial frequency. The integer inverse
powers therefore match the spatial Fourier separation at the cell scale.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

noncomputable def scaledWeightedInverseSum (m J : ℕ) (s r : ℝ)
    (z : Space (m+3)) (B : Space (m+3) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (J+1),
    (((r*s)^(((m+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹*((‖z‖/s)^j)⁻¹ : ℝ) : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space (m+3)) z : ℂ))*
          localInverseAmplitude m B j w ∂sphereMeasure (m+3)

theorem scaled_weighted_inverse_coefficient (h : ℝ) (j : ℕ)
    {s r t : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (r*s)^h*((r*s)^j)⁻¹*((t/s)^j)⁻¹ =
      s^h*(r^h*(r^j)⁻¹*(t^j)⁻¹) := by
  rw [Real.mul_rpow hr.le hs.le,mul_pow,div_pow,mul_inv_rev,inv_div]
  have hsj : s^j ≠ 0 := pow_ne_zero _ hs.ne'
  calc
    _ = (s^j)⁻¹*s^j*(s^h*(r^h*(r^j)⁻¹*(t^j)⁻¹)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hsj,one_mul]

theorem scaledWeightedInverseSum_eq (m J : ℕ) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (z : Space (m+3)) (B : Space (m+3) → ℂ) :
    scaledWeightedInverseSum m J s r z B =
      ((s^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*weightedInverseDisplacementSum m J r z B := by
  unfold scaledWeightedInverseSum weightedInverseDisplacementSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [scaled_weighted_inverse_coefficient _ j hs hr,Complex.ofReal_mul]
  ring

theorem scaled_weighted_inverse_distance {h s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    s^h*t^(-h) = (t/s)^(-h) := by
  rw [Real.div_rpow ht.le hs.le,Real.rpow_neg hs.le,div_inv_eq_mul]
  ring

theorem exists_scaled_weighted_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ R D : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 →
      ∀ (z : Space (m+3)), z ≠ 0 →
      ‖normalize z-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 →
      ∀ B : Space (m+3) → ℂ, ContDiff ℝ ∞ B →
      ∀ C : ℝ, 0 ≤ C →
      (∀ j ≤ 2*(J+1)+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ s r : ℝ, 0 < s → 1 ≤ r*‖z‖ → D^2/(r*‖z‖) ≤ R^(-κ) →
      ‖scaledWeightedInverseSum m J s r z B -
          (((‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)‖ ≤
        (‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2))*A*C*R^(-T) := by
  obtain ⟨J,A,hA,hbound⟩ := exists_weighted_displacement_inverse_order
    hgnomonic hquadratic m hκ
  refine ⟨J,A,hA,?_⟩
  intro R D hR hD hDR z hz hnear B hB C hC hBD s r hs hfreq hratio
  have hzpos := norm_pos_iff.mpr hz
  have hr : 0 < r := (mul_pos_iff_of_pos_right hzpos).mp (zero_lt_one.trans_le hfreq)
  have he := hbound R D hR hD hDR z hz hnear B hB C hC hBD r hfreq hratio
  have hp : 0 ≤ s^(((m+2 : ℕ) : ℝ)/2) := Real.rpow_nonneg hs.le _
  have heq : scaledWeightedInverseSum m J s r z B -
      (((‖z‖/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
        Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z) =
      ((s^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*
        (weightedInverseDisplacementSum m J r z B -
          ((‖z‖^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
            Complex.exp (Complex.I*((r*‖z‖ : ℝ) : ℂ))*B (normalize z)) := by
    rw [scaledWeightedInverseSum_eq m J hs hr,
      ← scaled_weighted_inverse_distance hs hzpos,Complex.ofReal_mul]
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left he hp).trans_eq (by
    rw [← mul_assoc,← mul_assoc,← mul_assoc,scaled_weighted_inverse_distance hs hzpos])

end Falconer

end OAI
