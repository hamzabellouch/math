import OAI.NumberTheory.CubicMoment.Estimates.GaussianDerivativeFactors

namespace OAI

/-! Explicit polynomial-times-Gaussian bounds at the original computational limits. -/
noncomputable section
namespace CubicFirstMoment

lemma gaussian_power_bound {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r^k*Real.exp (-a*r^2) ≤ C := by
  let C := 1+(k.factorial:ℝ)/a^k
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩
  intro r hr
  have he : Real.exp (-a*r^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg r))
  by_cases hr1 : r ≤ 1
  · have hk : r^k ≤ 1 := pow_le_one₀ hr hr1
    exact (show r^k*Real.exp (-a*r^2) ≤ 1 from
      (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le).trans (by simpa using he)).trans hC
  · have hr1 : 1 ≤ r := (lt_of_not_ge hr1).le
    have hpow : r^k ≤ r^(2*k) := by
      apply pow_le_pow_right₀ hr1
      omega
    have hs := Real.pow_div_factorial_le_exp (a*r^2) (mul_nonneg ha.le (sq_nonneg r)) k
    have hfac : 0 < (k.factorial:ℝ) := by positivity
    have hs' := (div_le_iff₀ hfac).mp hs
    have hm := mul_le_mul_of_nonneg_right hs' (Real.exp_pos (-a*r^2)).le
    have hp : (a*r^2)^k = a^k*r^(2*k) := by rw [mul_pow,pow_mul]
    have hex : Real.exp (a*r^2)*Real.exp (-a*r^2) = 1 := by
      rw [← Real.exp_add,show a*r^2 + -a*r^2 = 0 by ring,Real.exp_zero]
    have hb : r^(2*k)*Real.exp (-a*r^2) ≤ (k.factorial:ℝ)/a^k := by
      apply (le_div_iff₀ (pow_pos ha k)).mpr
      have heq : Real.exp (a*r^2)*(k.factorial:ℝ)*Real.exp (-a*r^2) = k.factorial := by
        calc
          _ = (k.factorial:ℝ)*(Real.exp (a*r^2)*Real.exp (-a*r^2)) := by ring
          _ = _ := by rw [hex,mul_one]
      rw [hp,heq] at hm
      convert hm using 1
      ring
    exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans
      (hb.trans (by dsimp [C]; linarith))

lemma gaussian_polynomial_bound {a : ℝ} (ha : 0 < a) (k d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      r^k*(1+r)^d*Real.exp (-a*r^2) ≤ C := by
  obtain ⟨C,hC,hb⟩ := gaussian_power_bound ha (k+d)
  refine ⟨2^d*C,by positivity,?_⟩
  intro r hr
  have he : Real.exp (-a*r^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg r))
  by_cases hr1 : r ≤ 1
  · have hk : r^k ≤ 1 := pow_le_one₀ hr hr1
    have hd : (1+r)^d ≤ (2:ℝ)^d := pow_le_pow_left₀ (by positivity) (by linarith) d
    have hm := mul_le_mul hk hd (by positivity) zero_le_one
    calc
      _ ≤ 2^d*1 := mul_le_mul (by simpa using hm) he (Real.exp_pos _).le (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)
  · have hr1 : 1 ≤ r := (lt_of_not_ge hr1).le
    have hd : (1+r)^d ≤ (2*r)^d := pow_le_pow_left₀ (by positivity) (by linarith) d
    calc
      _ ≤ r^k*(2*r)^d*Real.exp (-a*r^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (pow_nonneg hr k)) (Real.exp_pos _).le
      _ = 2^d*(r^(k+d)*Real.exp (-a*r^2)) := by rw [mul_pow,pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb r hr) (by positivity)

end CubicFirstMoment

end

end OAI
