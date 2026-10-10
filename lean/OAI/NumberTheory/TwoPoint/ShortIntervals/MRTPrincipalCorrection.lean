import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterZeroTerms
import Mathlib.Analysis.Calculus.LogDeriv

namespace OAI

/-! The principal character differs from zeta by the Euler factors at
primes dividing its modulus. Their total logarithmic derivative has norm
at most log(q), uniformly on Re(s)>=1. -/

namespace TwoPointCorrelations

open Complex Finset Filter
open scoped Classical Topology

noncomputable def mrtPrincipalEulerFactor (p : ℕ) (s : ℂ) : ℂ :=
  1-(p:ℂ)^(-s)

lemma mrt_principal_factor_cpow_norm {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) : ‖(p:ℂ)^(-s)‖≤1/(p:ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
  calc
    _ ≤ (p:ℝ)^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hp.one_le) (by linarith)
    _ = _ := by rw [Real.rpow_neg_one,one_div]

lemma mrt_principal_factor_norm_ge {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) : (1/2:ℝ)≤‖mrtPrincipalEulerFactor p s‖ := by
  have hh := norm_sub_norm_le (1:ℂ) ((p:ℂ)^(-s))
  have hb := mrt_principal_factor_cpow_norm hp hs
  have hi : 1/(p:ℝ)≤1/2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)
  simp only [norm_one] at hh
  change _≤‖1-(p:ℂ)^(-s)‖
  linarith

lemma mrt_principal_factor_ne_zero {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) : mrtPrincipalEulerFactor p s≠0 := by
  have hh := mrt_principal_factor_norm_ge hp hs
  intro he
  rw [he,norm_zero] at hh
  norm_num at hh

lemma mrt_principal_factor_hasDeriv {p : ℕ} (hp : p≠0) (s : ℂ) :
    HasDerivAt (mrtPrincipalEulerFactor p) ((p:ℂ)^(-s)*Complex.log p) s := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp
  have hh := (hasDerivAt_id s).neg.const_cpow (c := (p:ℂ)) (Or.inl hpC)
  change HasDerivAt (fun z => 1-(p:ℂ)^(-z)) _ s
  convert hh.const_sub (1:ℂ) using 1 <;> simp

lemma mrt_principal_factor_logderiv_norm {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) :
    ‖logDeriv (mrtPrincipalEulerFactor p) s‖≤Real.log (p:ℝ) := by
  have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlog : ‖Complex.log (p:ℂ)‖=Real.log (p:ℝ) := by
    rw [← Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg p),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl]
  have hd := mrt_principal_factor_norm_ge hp hs
  have hn := mrt_principal_factor_cpow_norm hp hs
  have hi : 1/(p:ℝ)≤‖mrtPrincipalEulerFactor p s‖ :=
    (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)).trans hd
  rw [logDeriv_apply,(mrt_principal_factor_hasDeriv hp.ne_zero s).deriv,
    norm_div,norm_mul,hlog]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hd)).mpr
  calc
    _ ≤ (1/(p:ℝ))*Real.log (p:ℝ) := mul_le_mul_of_nonneg_right hn hl
    _ ≤ ‖mrtPrincipalEulerFactor p s‖*Real.log (p:ℝ) :=
      mul_le_mul_of_nonneg_right hi hl
    _ = _ := by ring

lemma mrt_prime_factor_log_sum {q : ℕ} (hq : q≠0) :
    (∑ p∈q.primeFactors,Real.log (p:ℝ))≤Real.log (q:ℝ) := by
  have hp (p : ℕ) (hp : p∈q.primeFactors) : (0:ℝ)<p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hprod : (0:ℝ)<∏ p∈q.primeFactors,(p:ℝ) := prod_pos hp
  have hle : (∏ p∈q.primeFactors,(p:ℝ))≤(q:ℝ) := by
    have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) q.prod_primeFactors_dvd
    simpa only [Nat.cast_prod] using
      (Nat.cast_le.mpr hh : ((∏ p∈q.primeFactors,p : ℕ):ℝ)≤(q:ℝ))
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  exact Real.log_le_log hprod hle

theorem mrt_principal_logderiv {q : ℕ} [NeZero q] {s : ℂ} (hs : 1<s.re) :
    logDeriv (DirichletCharacter.LFunction (1:DirichletCharacter ℂ q)) s =
      (∑ p∈q.primeFactors,logDeriv (mrtPrincipalEulerFactor p) s)+
        logDeriv riemannZeta s := by
  let e : ℂ→ℂ := fun z => ∏ p∈q.primeFactors,mrtPrincipalEulerFactor p z
  have he (p : ℕ) (hp : p∈q.primeFactors) : mrtPrincipalEulerFactor p s≠0 :=
    mrt_principal_factor_ne_zero (Nat.prime_of_mem_primeFactors hp) hs.le
  have hd (p : ℕ) (hp : p∈q.primeFactors) :
      DifferentiableAt ℂ (mrtPrincipalEulerFactor p) s :=
    (mrt_principal_factor_hasDeriv (Nat.prime_of_mem_primeFactors hp).ne_zero s).differentiableAt
  have hene : e s≠0 := prod_ne_zero_iff.mpr he
  have hed : DifferentiableAt ℂ e s := DifferentiableAt.fun_finsetProd hd
  have hs1 : s≠1 := by intro h; rw [h] at hs; norm_num at hs
  have heq : DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      fun z => e z*riemannZeta z := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz
  have hh := (logDeriv_congr_nhds heq).self_of_nhds
  rw [logDeriv_fun_mul s hene (riemannZeta_ne_zero_of_one_le_re hs.le)
    hed (differentiableAt_riemannZeta hs1)] at hh
  have hprod : logDeriv e s=∑ p∈q.primeFactors,logDeriv (mrtPrincipalEulerFactor p) s :=
    logDeriv_fun_prod he hd
  rw [hprod] at hh
  exact hh

theorem mrt_principal_logderiv_error {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1<s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (1:DirichletCharacter ℂ q)) s-
      logDeriv riemannZeta s‖≤Real.log (q:ℝ) := by
  rw [mrt_principal_logderiv hs,add_sub_cancel_right]
  calc
    _ ≤ ∑ p∈q.primeFactors,‖logDeriv (mrtPrincipalEulerFactor p) s‖ := norm_sum_le _ _
    _ ≤ ∑ p∈q.primeFactors,Real.log (p:ℝ) :=
      sum_le_sum (fun p hp => mrt_principal_factor_logderiv_norm
        (Nat.prime_of_mem_primeFactors hp) hs.le)
    _ ≤ _ := mrt_prime_factor_log_sum (NeZero.ne q)

end TwoPointCorrelations

end OAI
