import OAI.MeasureTheory.Falconer.Estimates.ScalarDivideCoefficient
import OAI.MeasureTheory.Falconer.Estimates.ScalarScaleAlignment

namespace OAI

/-! Fixed-integer coefficient normalization costs only a fixed power of the
weak scalar projection constant. -/
namespace Falconer

noncomputable def scalarDivideConstant (M m : ℕ) : ℝ :=
  (3584*(4*(M:ℝ)+11))*(1+5*(m+3:ℝ)*2^(m+1))^8

 theorem scalarDivideConstant_pos (M m : ℕ) : 0 < scalarDivideConstant M m := by
  unfold scalarDivideConstant
  positivity

 theorem scalar_divide_budget_bound (M m : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    scalarDivideBudget M m K ≤ scalarDivideConstant M m*K^(8*(m+1)) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hp : K ≤ K^(m+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ m+1 by omega)
  have hi : K+5*(m+3:ℝ)*(2*K)^(m+1) ≤
      (1+5*(m+3:ℝ)*2^(m+1))*K^(m+1) := by
    rw [mul_pow]
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ K+5*(m+3:ℝ)*(2*K)^(m+1)) hi 8
  have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3584*(4*(M:ℝ)+11))
  calc
    _ ≤ (3584*(4*(M:ℝ)+11))*((1+5*(m+3:ℝ)*2^(m+1))*K^(m+1))^8 := hh
    _ = _ := by
      rw [mul_pow,← pow_mul]
      dsimp [scalarDivideConstant]
      rw [show (m+1)*8 = 8*(m+1) by omega]
      ring

 theorem scalar_divide_budget_absorption {η : ℝ} (hη : 0 < η) (M m : ℕ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      scalarDivideBudget M m (Real.exp (ε*(N:ℝ)*Real.log 2)) ≤
        Real.exp (η*(N:ℝ)*Real.log 2) := by
  let p : ℕ := 8*(m+1)
  have hp : 0 < (p:ℝ) := by dsimp [p]; positivity
  let ε := η/(4*p)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε ≤ η := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).2
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by dsimp [p]; omega)
    nlinarith
  obtain ⟨N0,hN0,hbound⟩ := scalar_fixed_losses hη (scalarDivideConstant_pos M m) zero_lt_one
  refine ⟨ε,N0,hε,hεη,hN0,?_⟩
  intro N hN
  have hW : 1 ≤ Real.exp (ε*(N:ℝ)*Real.log 2) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hh := scalar_divide_budget_bound M m hW
  have he : Real.exp (ε*(N:ℝ)*Real.log 2)^p =
      Real.exp ((η/4)*(N:ℝ)*Real.log 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [ε]
    field_simp
  change scalarDivideBudget M m (Real.exp (ε*(N:ℝ)*Real.log 2)) ≤
    scalarDivideConstant M m*Real.exp (ε*(N:ℝ)*Real.log 2)^p at hh
  exact hh.trans (by rw [he]; exact (hbound N hN).1)

end Falconer

end OAI
