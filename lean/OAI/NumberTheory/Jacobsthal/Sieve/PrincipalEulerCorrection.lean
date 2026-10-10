import OAI.NumberTheory.Jacobsthal.Estimates.NonquadraticZeroFree

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

noncomputable def localEulerFactor (alpha : ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  1-alpha*(p:ℂ)^(-s)

lemma prime_cpow_neg_norm_le_half {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p:ℂ)^(-s)‖ ≤ 1/2 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (p:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1/(p:ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hpR

lemma localEulerFactor_ne_zero {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 1 ≤ s.re) : localEulerFactor alpha p s ≠ 0 := by
  have hu : ‖alpha*(p:ℂ)^(-s)‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using prime_cpow_neg_norm_le_half hp hs)
  intro hz
  have he : alpha*(p:ℂ)^(-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [he, norm_one] at hu
  norm_num at hu

lemma localEulerFactor_differentiable {p : ℕ} (hp : p.Prime) (alpha : ℂ) :
    Differentiable ℂ (localEulerFactor alpha p) := by
  unfold localEulerFactor
  fun_prop (disch := exact Or.inl (by exact_mod_cast hp.ne_zero))

lemma localEulerFactor_deriv {p : ℕ} (hp : p.Prime) (alpha s : ℂ) :
    deriv (localEulerFactor alpha p) s =
      (Real.log (p:ℝ):ℂ) * (alpha*(p:ℂ)^(-s)) := by
  have hn : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd := ((((hasDerivAt_id s).neg).const_cpow (c := (p:ℂ)) (Or.inl hn)).const_mul alpha).const_sub 1
  simp only [Pi.neg_apply, id_eq] at hd
  convert! hd.deriv using 1
  rw [← Complex.natCast_log]
  ring

lemma norm_logDeriv_localEulerFactor {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 1 ≤ s.re) :
    ‖logDeriv (localEulerFactor alpha p) s‖ ≤ Real.log (p:ℝ) := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
  have hu : ‖alpha*(p:ℂ)^(-s)‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using prime_cpow_neg_norm_le_half hp hs)
  have hden : ‖alpha*(p:ℂ)^(-s)‖ ≤ ‖localEulerFactor alpha p s‖ := by
    have h := norm_sub_norm_le (1:ℂ) (alpha*(p:ℂ)^(-s))
    rw [norm_one] at h
    change 1-‖alpha*(p:ℂ)^(-s)‖ ≤ ‖localEulerFactor alpha p s‖ at h
    linarith
  rw [logDeriv_apply, localEulerFactor_deriv hp, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact (div_le_iff₀ (norm_pos_iff.mpr (localEulerFactor_ne_zero hp ha hs))).mpr
    (mul_le_mul_of_nonneg_left hden hlog)

lemma sum_log_primeFactors_le_log (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log (p:ℝ) ≤ Real.log (q:ℝ) := by
  have hpos : 0 < ∏ p ∈ q.primeFactors, (p:ℝ) :=
    Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log hpos
  have h : (((∏ p ∈ q.primeFactors, p : ℕ):ℕ):ℝ) ≤ (q:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
  simpa only [Nat.cast_prod] using! h

theorem norm_euler_log_correction_le_log (q : ℕ) [NeZero q] (S : Finset ℕ)
    (hS : S ⊆ q.primeFactors) (alpha : ℕ → ℂ) (ha : ∀ p ∈ S, ‖alpha p‖ ≤ 1)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑ p ∈ S, logDeriv (localEulerFactor (alpha p) p) s‖ ≤ Real.log (q:ℝ) := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun p hp => norm_logDeriv_localEulerFactor
    (Nat.prime_of_mem_primeFactors (hS hp)) (ha p hp) hs)).trans
  apply (Finset.sum_le_sum_of_subset_of_nonneg hS (fun p hp _ =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))).trans
  exact sum_log_primeFactors_le_log q

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

noncomputable def modulusEulerProduct (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, localEulerFactor 1 p s

lemma principal_log_derivative_eq (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunctionTrivChar q) s = logDeriv riemannZeta s +
      ∑ p ∈ q.primeFactors, logDeriv (localEulerFactor 1 p) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have he : DirichletCharacter.LFunctionTrivChar q =ᶠ[𝓝 s]
      (fun z => modulusEulerProduct q z * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    simpa only [modulusEulerProduct, localEulerFactor, one_mul] using
      (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hz)
  have hf (p:ℕ) (hp : p ∈ q.primeFactors) : localEulerFactor 1 p s ≠ 0 :=
    localEulerFactor_ne_zero (Nat.prime_of_mem_primeFactors hp) (by simp) hs.le
  have hd (p:ℕ) (hp : p ∈ q.primeFactors) : DifferentiableAt ℂ (localEulerFactor 1 p) s :=
    (localEulerFactor_differentiable (Nat.prime_of_mem_primeFactors hp) 1).differentiableAt
  have hprod : modulusEulerProduct q s ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  have hdiff : DifferentiableAt ℂ (modulusEulerProduct q) s := DifferentiableAt.fun_finsetProd hd
  have hld : logDeriv (DirichletCharacter.LFunctionTrivChar q) s =
      logDeriv (fun z => modulusEulerProduct q z * riemannZeta z) s := by
    simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
  rw [hld, logDeriv_fun_mul s hprod (riemannZeta_ne_zero_of_one_le_re hs.le) hdiff
    (differentiableAt_riemannZeta hs1)]
  have hsum : logDeriv (modulusEulerProduct q) s =
      ∑ p ∈ q.primeFactors, logDeriv (localEulerFactor 1 p) s := logDeriv_fun_prod hf hd
  rw [hsum, add_comm]

theorem norm_principal_log_derivative_difference (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunctionTrivChar q) s - logDeriv riemannZeta s‖ ≤
      Real.log (q:ℝ) := by
  rw [principal_log_derivative_eq q hs, add_sub_cancel_left]
  exact norm_euler_log_correction_le_log q q.primeFactors (Finset.Subset.refl _)
    (fun _ => 1) (by intro p hp; simp) hs.le

theorem principal_neg_real_log_derivative_le (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    (-logDeriv (DirichletCharacter.LFunctionTrivChar q) s).re ≤
      (-logDeriv riemannZeta s).re + Real.log (q:ℝ) := by
  have h := (Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunctionTrivChar q) s -
    logDeriv riemannZeta s))).trans
    (by simpa only [norm_neg] using norm_principal_log_derivative_difference q hs)
  simp only [Complex.neg_re, Complex.sub_re] at h ⊢
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
