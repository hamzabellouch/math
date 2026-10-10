import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymbolBound
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! # Symbol estimates after normalization of a physical annulus

These estimates use the actual decay order `2 * a` of the profile.  The scale
factors cancel in every derivative, before applying a fixed annular cutoff.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def normalizedPhysicalProfile (a R : ℝ) (Q : E → ℂ) : E → ℂ :=
  fun x => (R ^ (2 * a) : ℝ) • Q (R • x)

theorem normalizedPhysicalProfile_contDiff (a R : ℝ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) : ContDiff ℝ ∞ (normalizedPhysicalProfile a R Q) := by
  have hin : ContDiff ℝ ∞ (fun x : E => Q (R • x)) :=
    hQ.comp (contDiff_id.const_smul R)
  exact hin.const_smul (R ^ (2 * a))

theorem normalizedPhysicalProfile_jet_norm (a R : ℝ) (hR : 0 < R)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (normalizedPhysicalProfile a R Q) x‖ =
      R ^ (2 * a) * R ^ n * ‖iteratedFDeriv ℝ n Q (R • x)‖ := by
  have hin : ContDiff ℝ ∞ (fun x : E => Q (R • x)) :=
    hQ.comp (contDiff_id.const_smul R)
  unfold normalizedPhysicalProfile
  rw [iteratedFDeriv_const_smul_apply' ((hin.of_le (by simp)).contDiffAt)]
  rw [iteratedFDeriv_comp_const_smul R (hQ.of_le (by simp))]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hR.le _),
    abs_of_nonneg (pow_nonneg hR.le n)]
  ring

theorem normalizedPhysicalProfile_symbol_bound (a R D : ℝ) (hR : 0 < R)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : ℕ) (x : E) (hx : x ≠ 0)
    (hD : ‖iteratedFDeriv ℝ n Q (R • x)‖ ≤
      D * ‖R • x‖ ^ (-2 * a - (n : ℝ))) :
    ‖iteratedFDeriv ℝ n (normalizedPhysicalProfile a R Q) x‖ ≤
      D * ‖x‖ ^ (-2 * a - (n : ℝ)) := by
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcancel : R ^ (2 * a) * R ^ n * ‖R • x‖ ^ (-2 * a - (n : ℝ)) =
      ‖x‖ ^ (-2 * a - (n : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      Real.mul_rpow hR.le hxp.le, ← Real.rpow_natCast]
    calc
      _ = (R ^ (2 * a) * R ^ (n : ℝ) * R ^ (-2 * a - (n : ℝ))) *
          ‖x‖ ^ (-2 * a - (n : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hR, ← Real.rpow_add hR]
        have he : 2 * a + (n : ℝ) + (-2 * a - (n : ℝ)) = 0 := by ring
        rw [he, Real.rpow_zero, one_mul]
  rw [normalizedPhysicalProfile_jet_norm a R hR Q hQ n x]
  calc
    _ ≤ R ^ (2 * a) * R ^ n * (D * ‖R • x‖ ^ (-2 * a - (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hD (mul_nonneg (Real.rpow_nonneg hR.le _) (pow_nonneg hR.le n))
    _ = D * (R ^ (2 * a) * R ^ n * ‖R • x‖ ^ (-2 * a - (n : ℝ))) := by ring
    _ = _ := by rw [hcancel]

theorem normalizedPhysicalProfile_annulus_bound (a R D : ℝ) (ha : 0 < a)
    (hR : 0 < R) (hD : 0 ≤ D) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (N n : ℕ) (hn : n ≤ N) (x : E) (hx : (1 / 2 : ℝ) ≤ ‖x‖)
    (hsymbol : ‖iteratedFDeriv ℝ n Q (R • x)‖ ≤
      D * ‖R • x‖ ^ (-2 * a - (n : ℝ))) :
    ‖iteratedFDeriv ℝ n (normalizedPhysicalProfile a R Q) x‖ ≤
      D * (1 / 2 : ℝ) ^ (-2 * a - (N : ℝ)) := by
  have hxp : 0 < ‖x‖ := by linarith
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hp : ‖x‖ ^ (-2 * a - (n : ℝ)) ≤ (1 / 2 : ℝ) ^ (-2 * a - (N : ℝ)) := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ (-2 * a - (n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx
          (by have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _; linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (by linarith)
  exact (normalizedPhysicalProfile_symbol_bound a R D hR Q hQ n x
    (norm_pos_iff.mp hxp) hsymbol).trans (mul_le_mul_of_nonneg_left hp hD)

end DefocusingNLS

end OAI
