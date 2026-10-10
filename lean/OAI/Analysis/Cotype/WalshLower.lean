import OAI.Analysis.Cotype.WalshNorm

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_single {n : ℕ} (p : Cube n) (x : X) :
    cubeL2 X (fun u => if u = p then x else 0) =
      Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) * ‖x‖ := by
  unfold cubeL2 average
  simp only [smul_eq_mul, apply_ite, norm_zero, ite_pow, zero_pow (by omega : 2 ≠ 0),
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg x)]

theorem operatorWalsh_single {n : ℕ} (T : X →L[ℝ] Y) (p v : Cube n) (x : X) :
    operatorWalsh T (fun u => if u = p then x else 0) v =
      ((Fintype.card (Cube n) : ℝ)⁻¹ * character v p) • T x := by
  simp [operatorWalsh, vectorWalsh, average, apply_ite, smul_smul]

theorem operatorWalsh_single_L2 {n : ℕ} (T : X →L[ℝ] Y) (p : Cube n) (x : X) :
    cubeL2 Y (operatorWalsh T (fun u => if u = p then x else 0)) =
      (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ := by
  have hn (v : Cube n) : ‖operatorWalsh T (fun u => if u = p then x else 0) v‖ =
      (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ := by
    rw [operatorWalsh_single, norm_smul, Real.norm_eq_abs, abs_mul, abs_character,
      abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹), mul_one]
  have he : cubeL2 Y (operatorWalsh T (fun u => if u = p then x else 0)) =
      cubeL2 ℝ (fun _ : Cube n => (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖) := by
    simp only [cubeL2, hn, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖)]
  rw [he, cubeL2_const, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem walshNorm_lower (n : ℕ) (T : X →L[ℝ] Y) :
    Real.sqrt ((2 : ℝ)⁻¹ ^ n) * ‖T‖ ≤ walshNorm n T := by
  let q : ℝ := Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹)
  have hq : 0 < q := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := Cube n))))
  have hq2 : q^2 = (Fintype.card (Cube n) : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hop : ‖T‖ ≤ walshNorm n T / q := by
    apply T.opNorm_le_bound (div_nonneg (walshNorm_nonneg n T) hq.le)
    intro x
    have h := operatorWalsh_le_walshNorm T (fun u : Cube n => if u = (fun _ => false) then x else 0)
    rw [operatorWalsh_single_L2, cubeL2_single] at h
    change (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ ≤ walshNorm n T * (q * ‖x‖) at h
    rw [← hq2] at h
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hop hq.le
  have he : q = Real.sqrt ((2 : ℝ)⁻¹ ^ n) := by simp [q, Cube, inv_pow]
  rw [show q * (walshNorm n T / q) = walshNorm n T by field_simp] at hh
  simpa [he] using hh

theorem walshNorm_pos (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) : 0 < walshNorm n T :=
  (mul_pos (Real.sqrt_pos.mpr (by positivity)) (norm_pos_iff.mpr hT)).trans_le (walshNorm_lower n T)

end Cotype

end

end OAI
