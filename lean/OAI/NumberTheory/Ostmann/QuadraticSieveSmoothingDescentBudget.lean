import OAI.NumberTheory.Ostmann.QuadraticSieveCutoffScalesAlgebra

namespace OAI

namespace Ostmann.QuadraticSieve

theorem smoothing_descent_scalar_budget {M K P D C ξ δ α : ℝ} (R : ℕ)
    (hM : 0<M) (hK : 0≤K) (hP : 1≤P) (hD : 1≤D) (hC : 0≤C)
    (hD5 : D^5≤32*P^α) (hexp : δ*(R:ℝ)≤α) :
    (C*P^δ)^R*(3*M*D+(R:ℝ)*D^5*(M+Real.sqrt M*K^(ξ-1/2))) ≤
      (32*C^R*(3+(R:ℝ)))*P^(2*α)*(M+Real.sqrt M*K^(ξ-1/2)) := by
  have hPp : 0<P := by linarith
  have hcore0 : 0≤M+Real.sqrt M*K^(ξ-1/2) := by positivity
  have hMcore : M≤M+Real.sqrt M*K^(ξ-1/2) := le_add_of_nonneg_right (by positivity)
  have hDD : D≤D^5 := by
    calc
      D=D^1 := by ring
      _ ≤ D^5 := pow_le_pow_right₀ hD (by decide)
  have hbase : 3*M*D+(R:ℝ)*D^5*(M+Real.sqrt M*K^(ξ-1/2)) ≤
      (3+(R:ℝ))*D^5*(M+Real.sqrt M*K^(ξ-1/2)) := by
    have hh := mul_le_mul hDD hMcore hM.le (by positivity : 0≤D^5)
    nlinarith
  have hpow : (C*P^δ)^R≤C^R*P^α := by
    rw [mul_pow,← Real.rpow_mul_natCast hPp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hexp) (by positivity)
  calc
    _ ≤ (C^R*P^α)*((3+(R:ℝ))*D^5*(M+Real.sqrt M*K^(ξ-1/2))) := by gcongr
    _ ≤ (C^R*P^α)*((3+(R:ℝ))*(32*P^α)*(M+Real.sqrt M*K^(ξ-1/2))) := by gcongr
    _ = (32*C^R*(3+(R:ℝ)))*(P^α*P^α)*(M+Real.sqrt M*K^(ξ-1/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hPp]; congr 2; congr 1; ring

end Ostmann.QuadraticSieve

end OAI
