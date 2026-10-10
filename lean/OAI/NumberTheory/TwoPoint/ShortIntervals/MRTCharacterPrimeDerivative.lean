import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogDerivative
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowers

namespace OAI

/-! The logarithmic derivative of an arbitrary Dirichlet L-series is its
prime logarithmic series up to an absolute higher-prime-power correction.
The correction is bounded uniformly as the real part tends to one. -/

namespace TwoPointCorrelations

open scoped Classical LSeries.notation

noncomputable def mrtCharacterPrimeLogTerm {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  if n.Prime then χ n*(Real.log (n:ℝ):ℂ)/(n:ℂ)^s else 0

noncomputable def mrtCharacterPrimePowerCoefficient {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ n*(halaszPrimePowerWeight n:ℂ)

lemma mrt_character_prime_power_term_bound {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1≤s.re) (n : ℕ) :
    ‖LSeries.term (mrtCharacterPrimePowerCoefficient χ) s n‖≤
      halaszPrimePowerWeight n/(n:ℝ) := by
  calc
    _ ≤ ‖LSeries.term (mrtCharacterPrimePowerCoefficient χ) (1:ℂ) n‖ :=
      LSeries.norm_term_le_of_re_le_re _ hs n
    _ ≤ ‖LSeries.term (fun n => (halaszPrimePowerWeight n:ℂ)) (1:ℂ) n‖ := by
      apply LSeries.norm_term_le
      rw [mrtCharacterPrimePowerCoefficient,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    _ = _ := by
      rw [LSeries.norm_term_eq]
      by_cases hn : n=0
      · simp [hn]
      · simp only [hn,ite_false,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (halaszPrimePowerWeight_nonneg n),Complex.one_re,Real.rpow_one]

lemma mrt_character_prime_power_summable {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1≤s.re) :
    LSeriesSummable (mrtCharacterPrimePowerCoefficient χ) s := by
  exact halaszPrimePowerWeight_summable.of_norm_bounded
    (mrt_character_prime_power_term_bound χ hs)

lemma mrt_character_prime_power_LSeries_bound {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1≤s.re) :
    ‖L (mrtCharacterPrimePowerCoefficient χ) s‖≤halaszPrimePowerConstant := by
  apply (norm_tsum_le_tsum_norm (mrt_character_prime_power_summable χ hs).norm).trans
  exact (mrt_character_prime_power_summable χ hs).norm.tsum_le_tsum
    (mrt_character_prime_power_term_bound χ hs) halaszPrimePowerWeight_summable

lemma mrt_character_mangoldt_term_split {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    LSeries.term (↗χ*↗ArithmeticFunction.vonMangoldt) s n =
      mrtCharacterPrimeLogTerm χ s n+
        LSeries.term (mrtCharacterPrimePowerCoefficient χ) s n := by
  by_cases hn : n=0
  · simp [hn,mrtCharacterPrimeLogTerm]
  · rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn]
    by_cases hp : n.Prime
    · simp [mrtCharacterPrimeLogTerm,hp,mrtCharacterPrimePowerCoefficient,
        halaszPrimePowerWeight,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [mrtCharacterPrimeLogTerm,hp,mrtCharacterPrimePowerCoefficient,
        halaszPrimePowerWeight]

lemma mrt_character_prime_log_summable {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    Summable (mrtCharacterPrimeLogTerm χ s) := by
  have hm := χ.LSeriesSummable_twist_vonMangoldt hs
  have hp := mrt_character_prime_power_summable χ hs.le
  change Summable (LSeries.term (↗χ*↗ArithmeticFunction.vonMangoldt) s) at hm
  change Summable (LSeries.term (mrtCharacterPrimePowerCoefficient χ) s) at hp
  refine (hm.sub hp).congr ?_
  intro n
  rw [mrt_character_mangoldt_term_split]
  ring

theorem mrt_character_logDerivative_prime_series {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    -logDeriv (L ↗χ) s =
      (∑' n : ℕ, mrtCharacterPrimeLogTerm χ s n)+
        L (mrtCharacterPrimePowerCoefficient χ) s := by
  have hm := χ.LSeries_twist_vonMangoldt_eq hs
  rw [neg_div] at hm
  change L (↗χ*↗ArithmeticFunction.vonMangoldt) s = -logDeriv (L ↗χ) s at hm
  rw [← hm]
  change (∑' n, LSeries.term (↗χ*↗ArithmeticFunction.vonMangoldt) s n) = _
  simp_rw [mrt_character_mangoldt_term_split]
  exact (mrt_character_prime_log_summable χ hs).tsum_add
    (mrt_character_prime_power_summable χ hs.le)

theorem mrt_character_logDerivative_prime_error {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    ‖-logDeriv (L ↗χ) s-(∑' n : ℕ, mrtCharacterPrimeLogTerm χ s n)‖≤
      halaszPrimePowerConstant := by
  rw [mrt_character_logDerivative_prime_series χ hs,add_sub_cancel_left]
  exact mrt_character_prime_power_LSeries_bound χ hs.le

theorem mrt_character_logDerivative_real_prime_error {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    |-(logDeriv (L ↗χ) s).re-
      (∑' n : ℕ, mrtCharacterPrimeLogTerm χ s n).re|≤halaszPrimePowerConstant := by
  simpa only [Complex.sub_re,Complex.neg_re] using
    (Complex.abs_re_le_norm (-logDeriv (L ↗χ) s-
      (∑' n : ℕ, mrtCharacterPrimeLogTerm χ s n))).trans
      (mrt_character_logDerivative_prime_error χ hs)

lemma mrt_character_logDerivative_upper_of_prime_lower {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) {B : ℝ}
    (hprime : -B≤(∑' n : ℕ, mrtCharacterPrimeLogTerm χ s n).re) :
    (logDeriv (L ↗χ) s).re≤B+halaszPrimePowerConstant := by
  have he := (abs_le.mp (mrt_character_logDerivative_real_prime_error χ hs)).1
  linarith

/-- A lower bound on the smoothed prime logarithmic series throughout
the sigma segment suffices for the character L-value ratio. All
prime-power terms cost just one absolute constant. -/
theorem mrt_character_LSeries_sigma_lower_of_prime_sum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hq : 0<q) (t : ℝ)
    {Y X : ℕ} (hY : 1≤Real.log (Y:ℝ)) (hYX : Y≤X)
    {K : ℝ} (hK : 0≤K)
    (hprime : ∀ σ ∈ Set.Ioo (1+1/Real.log (X:ℝ)) (1+1/Real.log (Y:ℝ)),
      -(K*Real.log (Y:ℝ))≤
        (∑' n : ℕ, mrtCharacterPrimeLogTerm χ ((σ:ℂ)-(t:ℂ)*Complex.I) n).re) :
    -K-halaszPrimePowerConstant≤
      Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
      Real.log ‖L ↗χ (1+(1/Real.log (Y:ℝ):ℝ)-(t:ℂ)*Complex.I)‖ := by
  have hY0 : (0:ℝ)<Y :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg Y)).mp (by linarith))
  have hlog : Real.log (Y:ℝ)≤Real.log (X:ℝ) :=
    Real.log_le_log hY0 (by exact_mod_cast hYX)
  have hLX : 0<Real.log (X:ℝ) := by linarith
  have hh := mrt_character_LSeries_sigma_lower χ hq t hY hYX
    (add_nonneg hK halaszPrimePowerConstant_nonneg) (K := K+halaszPrimePowerConstant)
    (by
      intro σ hσ
      have hs : 1<((σ:ℂ)-(t:ℂ)*Complex.I).re := by
        have ha : 1<1+1/Real.log (X:ℝ) := by linarith [one_div_pos.mpr hLX]
        simpa using ha.trans hσ.1
      have hb := mrt_character_logDerivative_upper_of_prime_lower χ hs (hprime σ hσ)
      have hc := mul_le_mul_of_nonneg_left hY halaszPrimePowerConstant_nonneg
      nlinarith)
  linarith

end TwoPointCorrelations

end OAI
