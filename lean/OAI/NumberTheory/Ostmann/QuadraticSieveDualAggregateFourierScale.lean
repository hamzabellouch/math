import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateGrowth

namespace OAI

namespace Ostmann.QuadraticSieve

theorem dual_fourier_ambient_scale_le {P M : ℝ} {K N e D j : ℕ}
    (hP : 1 ≤ P) (hM : 0 < M) (hMP : M ≤ P) (he : 0 < e)
    (hNP : (N : ℝ) ≤ P) (hKP : (K : ℝ) ≤ P^3)
    (hD : D ≤ N^2) (hj : (2^j : ℕ) ≤ K) :
    (((2*D : ℕ) : ℝ)*Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e)) ≤
      2*Real.sqrt 2*P^4 := by
  have hP0 : 0 ≤ P := by linarith
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hm : M/e ≤ P := (div_le_self hM.le he1).trans hMP
  have hb : ((2^j : ℕ) : ℝ) ≤ P^3 := (by exact_mod_cast hj : ((2^j : ℕ) : ℝ) ≤ K) |>.trans hKP
  have hd : (D : ℝ) ≤ P^2 := by
    exact (by exact_mod_cast hD : (D : ℝ) ≤ (N : ℝ)^2).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg N) hNP 2)
  have hr : Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e) ≤ Real.sqrt 2*P^2 := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2*(2^j : ℕ))]
    have hp : 2*(2^j : ℕ)*(M/e) ≤ 2*P^4 := by
      have hh := mul_le_mul hb hm (by positivity : 0 ≤ M/(e : ℝ)) (by positivity : 0 ≤ P^3)
      nlinarith
    have hh := Real.sqrt_le_sqrt hp
    rwa [show (2 : ℝ)*P^4 = 2*(P^2)^2 by ring, Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sqrt_sq (sq_nonneg P)] at hh
  calc
    _ = (2*(D : ℝ))*(Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e)) := by push_cast; ring
    _ ≤ (2*P^2)*(Real.sqrt 2*P^2) := by gcongr
    _ = _ := by ring

theorem dual_fourier_ambient_boundary_scale_le {P M : ℝ} {K N e j : ℕ}
    (hP : 1 ≤ P) (hM : 0 < M) (hMP : M ≤ P) (he : 0 < e)
    (hN : 0 < N) (hNP : (N : ℝ) ≤ P) (hKP : (K : ℝ) ≤ P^3)
    (hj : (2^j : ℕ) ≤ K) :
    Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e) ≤ 2*Real.sqrt 2*P^4 := by
  have hh := dual_fourier_ambient_scale_le (D := 1) hP hM hMP he hNP hKP
    (by nlinarith : 1 ≤ N^2) hj
  norm_num only [Nat.mul_one, Nat.cast_ofNat] at hh
  have hp : 0 ≤ Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e) := by positivity
  nlinarith

end Ostmann.QuadraticSieve

end OAI
