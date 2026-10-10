import OAI.MeasureTheory.Falconer.Geometry.ScalarNormalizedProjection

namespace OAI

/-! Logarithmic bounds for the fixed number of scalar coefficient operations.
 They keep the normalization cost polynomial in both numerical parameters. -/
namespace Falconer

 theorem scalar_coefficient_radius_bound (M n : ℕ) :
    (scalarCoefficientRadius M n:ℝ)+4 ≤ ((M:ℝ)+8)^(3^n) := by
  induction n with
  | zero => simp [scalarCoefficientRadius]; linarith
  | succ n ih =>
    let r : ℝ := scalarCoefficientRadius M n
    have hr : 0 ≤ r := Nat.cast_nonneg _
    have hpoly : 2*r^2+4 ≤ (r+4)^3 := by nlinarith [pow_nonneg hr 3]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ r+4) ih 3
    calc
      _ = 2*r^2+4 := by simp only [scalarCoefficientRadius,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,r]
      _ ≤ (r+4)^3 := hpoly
      _ ≤ (((M:ℝ)+8)^(3^n))^3 := hh
      _ = _ := by rw [← pow_mul,pow_succ]

 theorem scalar_coefficient_radius_log (M n : ℕ) :
    Real.log ((scalarCoefficientRadius M n:ℝ)+4) ≤ (3:ℝ)^n*Real.log ((M:ℝ)+8) := by
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (scalarCoefficientRadius M n:ℝ)+4)
    (scalar_coefficient_radius_bound M n)
  rw [Real.log_pow] at hh
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

 theorem scalar_coefficient_log_budget (n : ℕ) :
    ∃ c p : ℝ, 0 ≤ c ∧ 0 ≤ p ∧ ∀ M : ℕ, ∀ K : ℝ, 1 ≤ K →
      Real.log (scalarCoefficientBudget M K n) ≤
        c+p*Real.log ((M:ℝ)+8)+(8:ℝ)^n*Real.log K := by
  induction n with
  | zero => exact ⟨0,0,le_rfl,le_rfl,fun M K _ => by simp [scalarCoefficientBudget]⟩
  | succ n ih =>
    obtain ⟨c,p,hc,hp,ih⟩ := ih
    refine ⟨Real.log 32768+8*c,(3:ℝ)^n+8*p,by positivity,by positivity,?_⟩
    intro M K hK
    have hKB : 0 < scalarCoefficientBudget M K n :=
      lt_of_lt_of_le (by norm_num) (scalarCoefficientBudget_one_le M hK n)
    have hr := scalar_coefficient_radius_log M n
    have hb := ih M K hK
    change Real.log (32768*((scalarCoefficientRadius M n:ℝ)+4)*
      (scalarCoefficientBudget M K n)^8) ≤ _
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,pow_succ]
    norm_num only [Nat.cast_ofNat]
    nlinarith

end Falconer

end OAI
