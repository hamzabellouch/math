import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Ostmann.QuadraticSieve

theorem leading_bootstrap_power_budget {P K Δ N δ : ℝ}
    (hP : 1≤P) (hK0 : 0≤K) (hΔ0 : 0≤Δ) (hN0 : 0≤N)
    (hK : K≤P^3) (hΔ : Δ≤P) (hN : N≤P) (hδ : 0≤δ) :
    N^δ*(K*Δ^2*N)^δ ≤ P^(7*δ) := by
  have hP0 : 0≤P := by linarith
  rw [← Real.mul_rpow hN0 (by positivity)]
  have hb : N*(K*Δ^2*N) ≤ P^7 := by
    calc
      _ ≤ P*(P^3*P^2*P) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (P^7)^δ := Real.rpow_le_rpow (by positivity) hb hδ
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hP0]; norm_num

theorem leading_bootstrap_scalar_budget {M K Δ N ξ : ℝ}
    (hM : 0<M) (hK : 0<K) (hΔ : 1≤Δ) (hξ : ξ≤2)
    (hsqrt : Real.sqrt (M/K)*N≤M) :
    Real.sqrt (M/K)*((K*Δ^2)^ξ+N) ≤
      Δ^4*(M+Real.sqrt M*K^(ξ-1/2)) := by
  have hΔ0 : 0≤Δ := by linarith
  have hΔp : 0<Δ := by linarith
  have hΔpow : Δ^(2*ξ)≤Δ^4 := by
    calc
      _ ≤ Δ^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le hΔ (by linarith)
      _ = _ := Real.rpow_natCast Δ 4
  have hΔ4 : 1≤Δ^4 := by nlinarith [sq_nonneg (Δ^2-1)]
  have hid : Real.sqrt (M/K)*(K*Δ^2)^ξ =
      (Real.sqrt M*K^(ξ-1/2))*Δ^(2*ξ) := by
    rw [Real.mul_rpow hK.le (sq_nonneg Δ), Real.sqrt_div hM.le]
    have hD : (Δ^2)^ξ=Δ^(2*ξ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hΔ0]
    have hKpow : K^ξ/Real.sqrt K=K^(ξ-1/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hK]
    rw [hD, ← hKpow]
    ring
  calc
    _ = Real.sqrt (M/K)*(K*Δ^2)^ξ+Real.sqrt (M/K)*N := by ring
    _ ≤ (Real.sqrt M*K^(ξ-1/2))*Δ^(2*ξ)+M := by rw [hid]; gcongr
    _ ≤ (Real.sqrt M*K^(ξ-1/2))*Δ^4+M := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hΔ4 hM.le]

end Ostmann.QuadraticSieve

end OAI
