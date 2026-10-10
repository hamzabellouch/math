import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem norm_sq_le_inner_of_square_ge
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hsquare : ∀ x : E, ⟪x, T x⟫ ≤ ⟪T x, T x⟫)
    (x : E) (hx : ∀ y : E, T y = 0 → ⟪y, x⟫ = 0) :
    ‖x‖ ^ 2 ≤ ⟪x, T x⟫ := by
  classical
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (b i) = ev i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hunit (i : Fin (Module.finrank ℝ E)) : ⟪b i, b i⟫ = 1 :=
    by rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have hevpos (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i := by
    simpa only [hbe, inner_smul_right, hunit, mul_one] using hpos (b i)
  have hevsquare (i : Fin (Module.finrank ℝ E)) : ev i ≤ (ev i) ^ 2 := by
    simpa only [hbe, inner_smul_left, inner_smul_right, hunit, mul_one,
      RCLike.conj_to_real, pow_two] using hsquare (b i)
  rw [← b.sum_sq_inner_right x, ← b.sum_inner_mul_inner x (T x)]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪b i, T x⟫ = ev i * ⟪b i, x⟫ := by
    rw [← hT (b i) x, hbe, inner_smul_left]
    simp
  have hcomm : ⟪x, b i⟫ = ⟪b i, x⟫ := real_inner_comm _ _
  rw [hcoord, hcomm]
  by_cases he : ev i = 0
  · have hz : ⟪b i, x⟫ = 0 := hx (b i) (by simp [hbe, he])
    simp [hz]
  · have hone : 1 ≤ ev i := by
      have hp := hevpos i
      have hs := hevsquare i
      have hp' : 0 < ev i := lt_of_le_of_ne hp (Ne.symm he)
      nlinarith
    nlinarith [sq_nonneg ⟪b i, x⟫]

theorem norm_apply_le_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {r : ℝ} (hr : 0 ≤ r)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hbound : ∀ x : E, ⟪x, T x⟫ ≤ r * ‖x‖ ^ 2)
    (x : E) : ‖T x‖ ≤ r * ‖x‖ := by
  classical
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (b i) = ev i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hunit (i : Fin (Module.finrank ℝ E)) : ⟪b i, b i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have hev (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i ∧ ev i ≤ r := by
    constructor
    · simpa only [hbe, inner_smul_right, hunit, mul_one] using hpos (b i)
    · simpa only [hbe, inner_smul_right, hunit, mul_one, b.orthonormal.1 i,
        one_pow] using hbound (b i)
  have hsq : ‖T x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_inner_right (T x), ← b.sum_sq_inner_right x,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hcoord : ⟪b i, T x⟫ = ev i * ⟪b i, x⟫ := by
      rw [← hT (b i) x, hbe, inner_smul_left]
      simp
    rw [hcoord, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hev i).1 (hev i).2 2
  nlinarith [norm_nonneg (T x), norm_nonneg x, mul_nonneg hr (norm_nonneg x)]

omit [FiniteDimensional ℝ E] in

theorem norm_iterate_le
    (T : E →ₗ[ℝ] E) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ x : E, ‖T x‖ ≤ r * ‖x‖) (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ r ^ t * ‖x‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖T ((T : E → E)^[t] x)‖ ≤ r * ‖(T : E → E)^[t] x‖ := hbound _
        _ ≤ r * (r ^ t * ‖x‖) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (t + 1) * ‖x‖ := by ring

theorem norm_iterate_le_exp_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hgap : ∀ x : E, ⟪x, T x⟫ ≤ (1 - γ) * ‖x‖ ^ 2)
    (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
  have hr : 0 ≤ 1 - γ := sub_nonneg.mpr hγ
  calc
    ‖(T : E → E)^[t] x‖ ≤ (1 - γ) ^ t * ‖x‖ :=
      norm_iterate_le T hr (norm_apply_le_of_inner_bounds T hT hr hpos hgap) t x
    _ ≤ (Real.exp (-γ)) ^ t * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact pow_le_pow_left₀ hr (Real.one_sub_le_exp_neg γ) t
    _ = Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

end Problem315.Analytic

end

end OAI
