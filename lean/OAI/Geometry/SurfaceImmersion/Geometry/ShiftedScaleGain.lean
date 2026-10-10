import OAI.Geometry.SurfaceImmersion.Correction.ShiftedSmoothingBounds

namespace OAI

/-! Inherited derivatives gain a scale ratio above the fixed prefix. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reducing the scale preserves the unweighted prefix and contracts all
higher weighted derivatives by at least `τ/t`. -/
theorem ShiftedBound.shrink_with_prefix {q m : ℕ} {t τ A C : ℝ} {f : Base → V}
    (hb : ShiftedBound q 0 t A f) (hc : ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ShiftedBound q m τ (A + (τ / t) * C) f := by
  intro j hj x
  by_cases hjq : j ≤ q
  · have h := hb j (by omega) x
    simp only [Nat.sub_eq_zero_of_le hjq, pow_zero, one_mul] at h ⊢
    exact h.trans (le_add_of_nonneg_right (mul_nonneg (div_nonneg hτ ht.le) hC))
  · have hp : (τ / t) ^ (j - q) ≤ τ / t := by
      simpa only [pow_one] using pow_le_pow_of_le_one (div_nonneg hτ ht.le)
        ((div_le_one ht).mpr hτt) (show 1 ≤ j - q by omega)
    calc
      _ ≤ τ ^ (j - q) * (C / t ^ (j - q)) :=
        mul_le_mul_of_nonneg_left (hc.deriv_le ht hj x) (pow_nonneg hτ _)
      _ = (τ / t) ^ (j - q) * C := by rw [div_pow]; ring
      _ ≤ (τ / t) * C := mul_le_mul_of_nonneg_right hp hC
      _ ≤ _ := le_add_of_nonneg_left hA

/-- Adding the actual increment adds its shifted derivative budget. -/
theorem ShiftedBound.add {q m : ℕ} {s A B : ℝ} {f g : Base → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hs : 0 ≤ s)
    (hb : ShiftedBound q m s A f) (hc : ShiftedBound q m s B g) :
    ShiftedBound q m s (A + B) (f + g) := by
  intro j hj x
  rw [iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt
    (hg.of_le (by simp)).contDiffAt]
  calc
    _ ≤ s ^ (j - q) * (‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hs _)
    _ = s ^ (j - q) * ‖iteratedFDeriv ℝ j f x‖ +
        s ^ (j - q) * ‖iteratedFDeriv ℝ j g x‖ := by ring
    _ ≤ _ := add_le_add (hb j hj x) (hc j hj x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
