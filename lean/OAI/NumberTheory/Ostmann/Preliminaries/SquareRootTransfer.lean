import OAI.NumberTheory.Ostmann.Preliminaries.HRefinement

namespace OAI

namespace Ostmann.Preliminaries
open Filter

theorem sqrtCutoff_tendsto : Tendsto (fun X : ℕ => Nat.sqrt X + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (n ^ 2)] with X hX
  have hn := Nat.le_sqrt'.mpr hX
  omega

theorem eventually_sqrt_upper_of_square (S : Set ℕ) {C : ℝ} (hC : 0 < C)
    (hsquare : ∀ᶠ Q : ℕ in atTop,
      (countUpTo S (Q ^ 2) : ℝ) ≤ C * Q * Real.log (Q : ℝ) ^ 2) :
    ∀ᶠ X : ℕ in atTop,
      (countUpTo S X : ℝ) ≤ (2 * C) * Real.sqrt X * Real.log (X : ℝ) ^ 2 := by
  filter_upwards [sqrtCutoff_tendsto.eventually hsquare, eventually_ge_atTop 2] with X hsq hX
  let Q := Nat.sqrt X + 1
  have hQbound : X ≤ Q ^ 2 := (Nat.lt_succ_sqrt' X).le
  have hQpos : 0 < Q := by dsimp [Q]; omega
  have hQX : Q ≤ X := by have := Nat.sqrt_lt_self (show 1 < X by omega); dsimp [Q]; omega
  have hxr : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hroot : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := by
    have hn : (0 : ℝ) ≤ Nat.sqrt X := by positivity
    have hs := Real.sqrt_nonneg (X : ℝ)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ X by positivity)
    have hn2 : (Nat.sqrt X : ℝ) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
    nlinarith
  have hsqrt1 := Real.one_le_sqrt.mpr hxr
  have hQsqrt : (Q : ℝ) ≤ 2 * Real.sqrt X := by dsimp [Q]; push_cast; linarith
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ Q by omega))
  have hlogle : Real.log (Q : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQX)
  have hcount : (countUpTo S X : ℝ) ≤ countUpTo S (Q ^ 2) := by
    exact_mod_cast countUpTo_mono S hQbound
  apply (hcount.trans hsq).trans
  calc
    C * (Q : ℝ) * Real.log (Q : ℝ) ^ 2 ≤ C * (2 * Real.sqrt X) * Real.log (X : ℝ) ^ 2 := by
      gcongr
    _ = _ := by ring

theorem eventually_sqrt_lower_of_upper (d : Decomposition) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ᶠ X : ℕ in atTop,
      (countUpTo d.B X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ) ^ 2) :
    ∀ᶠ X : ℕ in atTop,
      (Real.log 2 / (2 * C)) * Real.sqrt X / Real.log (X : ℝ) ^ 3 ≤ countUpTo d.A X := by
  filter_upwards [eventually_count_product_lower d, hupper, eventually_ge_atTop 2] with X hprod hupper hX
  have hxr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hxr
  have hsqrtSq := Real.sq_sqrt hxr.le
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hA : (0 : ℝ) ≤ countUpTo d.A X := by positivity
  have hmain := (div_le_iff₀ hl).mp (hprod.trans (mul_le_mul_of_nonneg_left hupper hA))
  nth_rw 1 [← hsqrtSq] at hmain
  have hcore : (Real.log 2 / 2) * Real.sqrt X ≤
      (countUpTo d.A X : ℝ) * C * Real.log (X : ℝ) ^ 3 := by
    apply (mul_le_mul_iff_right₀ hsqrt).mp
    nlinarith [hmain]
  apply (div_le_iff₀ (pow_pos hl 3)).mpr
  have hid : (Real.log 2 / (2 * C)) * Real.sqrt X =
      ((Real.log 2 / 2) * Real.sqrt X) / C := by ring
  rw [hid]
  exact (div_le_iff₀ hC).mpr (by nlinarith [hcore])

end Ostmann.Preliminaries

end OAI
