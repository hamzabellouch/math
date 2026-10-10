import OAI.MeasureTheory.Falconer.Geometry.ProjectionPowerBudget
import OAI.MeasureTheory.Falconer.Estimates.SampledRowCardinality

namespace OAI

/-! Reserve a uniform positive exponent for the two pencil-size cases of
the regular-scale estimate. All fixed constants are absorbed at large depth. -/
namespace Falconer

theorem normalized_regular_gain_budget {κ θ A : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) (hθ : 0 < θ) (hA : 0 ≤ A) :
    ∃ ε γ η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < γ ∧ 0 < η ∧ 0 < N0 ∧
      γ*(κ/2) = 4*η ∧ ∀ n : ℕ, N0 ≤ n+2 →
        let δ := 1/(2:ℝ)^(2*n)
        let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
        let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
        K ≤ E ∧ δ^(-(γ+η)) ≤ E ∧ 2*A*K^3 ≤ δ^(-3*η) := by
  let γ := θ/8
  let η := γ*κ/8
  let ε := min (min θ 1) (η/20)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hε : 0 < ε := lt_min (lt_min hθ zero_lt_one) (by positivity)
  have hεθ : ε ≤ θ := (min_le_left _ _).trans (min_le_left _ _)
  have hεsmall : 3*ε ≤ η := by
    have he : ε ≤ η/20 := min_le_right _ _
    linarith only [he,hη]
  have hηlow : γ+η ≤ θ/2 := by
    dsimp [γ,η]
    nlinarith only [hκ1,hθ]
  obtain ⟨N1,hN1,hconst⟩ := dyadic_quadratic_loss hη (show 0 ≤ 2*A by positivity)
  refine ⟨ε,γ,η,max 4 N1,hε,(min_le_left _ _).trans (min_le_right _ _),hγ,hη,
    lt_of_lt_of_le (by norm_num : 0 < 4) (le_max_left _ _),?_,?_⟩
  · dsimp [η]
    ring
  intro n hn
  dsimp only
  have hn1 : 1 ≤ n := by have := (le_max_left 4 N1).trans hn; omega
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hmR : 0 ≤ ((n+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
      Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by gcongr
  have hE : (1/(2:ℝ)^(2*n))^(-(γ+η)) ≤
      Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by
    rw [show (1/(2:ℝ)^(2*n)) = (1/(2:ℝ))^(2*n) by rw [div_pow,one_pow],half_power_rpow_exp]
    apply Real.exp_le_exp.mpr
    push_cast
    have hg := mul_le_mul_of_nonneg_right hηlow (show 0 ≤ 2*(n:ℝ) by positivity)
    apply mul_le_mul_of_nonneg_right _ hlog
    nlinarith only [hg,hθ]
  refine ⟨hK,hE,?_⟩
  have hfixed : 2*A ≤ Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply le_trans _ (hconst (n+2) ((le_max_right _ _).trans hn))
    have hsq : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by linarith only [hmR])
    nlinarith only [hsq,hA]
  have hexp : (Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2))^3 =
      Real.exp ((3*ε)*((n+2:ℕ):ℝ)*Real.log 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ ≤ Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2)*
        Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) := by
      apply mul_le_mul hfixed _ (Real.exp_pos _).le (Real.exp_pos _).le
      gcongr
    _ = Real.exp ((2*η)*((n+2:ℕ):ℝ)*Real.log 2) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ (1/(2:ℝ)^(2*n))^(-3*η) := by
      rw [show (1/(2:ℝ)^(2*n)) = (1/(2:ℝ))^(2*n) by rw [div_pow,one_pow],half_power_rpow_exp]
      apply Real.exp_le_exp.mpr
      push_cast
      apply mul_le_mul_of_nonneg_right _ hlog
      have hnR1 : (1:ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hnR1)]

end Falconer

end OAI
