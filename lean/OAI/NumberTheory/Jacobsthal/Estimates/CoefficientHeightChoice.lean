import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

noncomputable def boxHeight (M N : ℕ) : ℕ := ⌈(M : ℝ)^((N : ℝ)⁻¹)⌉₊

theorem boxHeight_pos {M N : ℕ} (hM : 0 < M) : 0 < boxHeight M N := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast hM) _

theorem boxHeight_card_strict {M N : ℕ} (hN : 0 < N) : M < (boxHeight M N+1)^N := by
  have hle : (M : ℝ)^((N : ℝ)⁻¹) ≤ (boxHeight M N : ℝ) := Nat.le_ceil _
  have hlt : (M : ℝ)^((N : ℝ)⁻¹) < (boxHeight M N : ℝ)+1 := by linarith
  have h := (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg M)
    (by positivity : (0 : ℝ) ≤ (boxHeight M N : ℝ)+1)
    (by exact_mod_cast hN : (0 : ℝ) < (N : ℝ))).mp hlt
  rw [Real.rpow_natCast] at h
  exact_mod_cast h

theorem boxHeight_le_twice_root {M N : ℕ} (hM : 0 < M) :
    (boxHeight M N : ℝ) ≤ 2*(M : ℝ)^((N : ℝ)⁻¹) := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hM)
  have hroot : (1 : ℝ) ≤ (M : ℝ)^((N : ℝ)⁻¹) := Real.one_le_rpow hM1 (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg M) (N : ℝ)⁻¹)
  change (boxHeight M N : ℝ) < (M : ℝ)^((N : ℝ)⁻¹)+1 at hc
  linarith

theorem boxHeight_log_bound {M N : ℕ} (hM : 0 < M) (_hN : 0 < N) :
    Real.log (2*(boxHeight M N : ℝ)) ≤ Real.log 4+Real.log (M : ℝ)/(N : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hH : (0 : ℝ) < (boxHeight M N : ℝ) := by exact_mod_cast boxHeight_pos (N := N) hM
  have hr : (0 : ℝ) < (M : ℝ)^((N : ℝ)⁻¹) := Real.rpow_pos_of_pos hM0 _
  have hb := boxHeight_le_twice_root (N := N) hM
  calc
    _ ≤ Real.log (4*((M : ℝ)^((N : ℝ)⁻¹))) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 4+Real.log ((M : ℝ)^((N : ℝ)⁻¹)) := Real.log_mul (by norm_num) hr.ne'
    _ = Real.log 4+Real.log (M : ℝ)/(N : ℝ) := by rw [Real.log_rpow hM0]; ring

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
