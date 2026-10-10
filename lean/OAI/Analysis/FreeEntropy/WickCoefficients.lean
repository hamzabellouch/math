import OAI.Analysis.FreeEntropy.SeriesSummability

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

def vectorReverse (d : ℕ) : List.Vector α d ≃ List.Vector α d where
  toFun v := v.reverse
  invFun v := v.reverse
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

omit [DecidableEq α] in
theorem degreeNorm_reverse [DecidableEq α] (f : Series α) (d : ℕ) : degreeNorm (fun w => f w.reverse) d = degreeNorm f d := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  rw [degreeNorm_sq, degreeNorm_sq]
  exact (vectorReverse (α := α) d).sum_comp (fun v => ‖f v.val‖^2)

omit [DecidableEq α] in
theorem degreeNorm_conj [DecidableEq α] (f : Series α) (d : ℕ) : degreeNorm (fun w => conj (f w)) d = degreeNorm f d := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  simp [degreeNorm_sq]

def wickCoefficients (f : Series α) (u : ℝ) : Series α :=
  fun js => conj (f js.reverse) / (Real.sqrt u : ℂ)^js.length

omit [DecidableEq α] [Fintype α] in
theorem wickCoefficients_cancel [DecidableEq α] [Fintype α] (f : Series α) (u : ℝ) (hu : 0 < u) (js : List α) :
    conj (wickCoefficients f u js) * (Real.sqrt u : ℂ)^js.length = f js.reverse := by
  have hr : (Real.sqrt u : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hu).ne'
  simp [wickCoefficients, hr]
 theorem wickCoefficients_degree_sq (f : Series α) (u : ℝ) (hu : 0 ≤ u) (d : ℕ) :
    degreeNorm (wickCoefficients f u) d ^ 2 = u⁻¹^d * degreeNorm f d ^ 2 := by
  have he : degreeNorm (wickCoefficients f u) d =
      degreeNorm ((Real.sqrt u : ℂ)⁻¹^d • (fun w => conj (f w.reverse) : Series α)) d := by
    apply degreeNorm_congr
    intro w hw
    simp [wickCoefficients, hw, div_eq_mul_inv, mul_comm]
  rw [he, degreeNorm_smul, degreeNorm_conj, degreeNorm_reverse, mul_pow]
  congr 1
  have hsq : (Real.sqrt u ^ d)^2 = u^d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul, Real.sq_sqrt hu]
  simp [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u), hsq]
 theorem residual_degree (R : Series α) (v : α → ℝ) (i : α) (d : ℕ) (hd : 2 ≤ d) :
    degreeNorm (residual R v i) d = degreeNorm (FreeSeries.deriv i R) d := by
  apply degreeNorm_congr
  intro w hw
  exact residual_long R v i w (by omega)
 theorem residual_degree_short {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (i : α) (d : ℕ) (hd : d < 2) : degreeNorm (residual R v i) d = 0 := by
  apply (degreeNorm_congr (g := 0) d ?_).trans (degreeNorm_zero d)
  intro w hw
  exact residual_short hc hv i w (by omega)
 theorem residual_degree_sum {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0) (d : ℕ) :
    ∑ i : α, degreeNorm (residual R v i) d ^ 2 =
      if 2 ≤ d then degreeNorm R (d+1)^2 else 0 := by
  by_cases hd : 2 ≤ d
  · simp only [ite_eq_left hd, residual_degree R v _ _ hd]
    exact (degreeNorm_succ_sq R d).symm
  · have hz (i : α) : degreeNorm (residual R v i) d = 0 :=
      residual_degree_short hc hv i d (by omega)
    simp [hd, hz]
 theorem wickCoefficients_degree_sum {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (u : ℝ) (hu : 0 ≤ u) (d : ℕ) :
    ∑ i : α, degreeNorm (wickCoefficients (residual R v i) u) d^2 =
      if 2 ≤ d then u⁻¹^d * degreeNorm R (d+1)^2 else 0 := by
  simp_rw [wickCoefficients_degree_sq _ u hu]
  rw [← mul_sum, residual_degree_sum hc hv]
  split_ifs <;> simp
end FiniteEntropySeparation.FreeSeries

end

end OAI
