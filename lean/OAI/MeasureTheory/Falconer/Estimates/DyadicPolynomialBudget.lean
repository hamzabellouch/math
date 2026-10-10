import OAI.MeasureTheory.Falconer.Geometry.ProjectionPowerBudget

namespace OAI

/-! Every fixed polynomial loss in the dyadic depth fits the available
positive exponent. This is used for the finitely many scale-product steps. -/
namespace Falconer

theorem dyadic_polynomial_loss {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) (p : ℕ) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*((N:ℝ)+1)^p ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  let a := η*Real.log 2
  have ha : 0 < a := mul_pos hη (Real.log_pos (by norm_num))
  have hfac : 0 < ((p+1).factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1
    (C*2^p*((p+1).factorial:ℝ)/a^(p+1)))
  have hN01 : (1:ℝ) ≤ N0 := (le_max_left _ _).trans hN0.le
  refine ⟨N0,by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN01),?_⟩
  intro N hN
  have hNN : (N0:ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN1 : (1:ℝ) ≤ N := hN01.trans hNN
  have hscale : C*2^p*((p+1).factorial:ℝ) ≤ a^(p+1)*(N:ℝ) := by
    have hh := (le_max_right _ _).trans (hN0.le.trans hNN)
    exact (div_le_iff₀ (pow_pos ha _)).mp hh |>.trans_eq (mul_comm _ _)
  have hmult := mul_le_mul_of_nonneg_right hscale (pow_nonneg (Nat.cast_nonneg N) p)
  have hpoly : C*(2*(N:ℝ))^p ≤ (a*(N:ℝ))^(p+1)/((p+1).factorial:ℝ) := by
    apply (le_div_iff₀ hfac).2
    convert hmult using 1 <;> simp only [mul_pow,pow_succ] <;> ring
  calc
    _ ≤ C*(2*(N:ℝ))^p := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hN1]) p) hC
    _ ≤ (a*(N:ℝ))^(p+1)/((p+1).factorial:ℝ) := hpoly
    _ ≤ Real.exp (a*(N:ℝ)) := Real.pow_div_factorial_le_exp (a*(N:ℝ)) (by positivity) (p+1)
    _ = _ := by congr 1; dsimp [a]; ring

theorem dyadic_scale_loss_transfer {τ lam ξ : ℝ} (hτ : 0 < τ)
    (hlam : 0 ≤ lam) (hξ : 0 ≤ ξ) {N D : ℕ}
    (hD : τ*(N:ℝ) ≤ D) :
    (2:ℝ)^((2*lam+ξ)*(N:ℝ)) ≤ (2:ℝ)^(((2*lam+ξ)/τ)*(D:ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ (2*lam+ξ)/τ by positivity)
  convert hh using 1; field_simp

end Falconer

end OAI
