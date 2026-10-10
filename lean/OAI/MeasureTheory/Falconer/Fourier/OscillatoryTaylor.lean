import OAI.MeasureTheory.Falconer.Angular.InheritedCircleRegularity
import Mathlib.Analysis.Calculus.Taylor

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def imaginaryExponential (t : ℝ) : ℂ := Complex.exp (Complex.I*(t:ℂ))

 theorem imaginaryExponential_contDiff : ContDiff ℝ ∞ imaginaryExponential := by
  unfold imaginaryExponential
  have hf : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

 theorem imaginaryExponential_hasDerivAt (t : ℝ) :
    HasDerivAt imaginaryExponential (Complex.I*imaginaryExponential t) t := by
  unfold imaginaryExponential
  convert (((hasDerivAt_id t).ofReal_comp.const_mul Complex.I).cexp) using 1 <;>
    simp [mul_comm]

 theorem imaginaryExponential_iteratedDeriv (n : ℕ) :
    iteratedDeriv n imaginaryExponential = fun t => Complex.I^n * imaginaryExponential t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [((imaginaryExponential_hasDerivAt t).const_mul (Complex.I^n)).deriv,pow_succ]
    ring

 theorem imaginaryExponential_derivative_norm (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n imaginaryExponential t‖ = 1 := by
  rw [imaginaryExponential_iteratedDeriv]
  simp [imaginaryExponential,Complex.norm_exp,Complex.mul_re]

noncomputable def imaginaryTaylor (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), ((k.factorial:ℝ)⁻¹*t^k) • (Complex.I^k)

 theorem imaginaryExponential_taylor_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖imaginaryExponential t - imaginaryTaylor n t‖ ≤ t^(n+1)/(n.factorial:ℝ) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [imaginaryTaylor,imaginaryExponential,zero_pow_eq]
  have hd : UniqueDiffOn ℝ (Icc 0 t) := uniqueDiffOn_Icc ht
  have hs (k : ℕ) : ContDiff ℝ k imaginaryExponential :=
    imaginaryExponential_contDiff.of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
  have hh := taylor_mean_remainder_bound ht.le (hs (n+1)).contDiffOn
    (show t ∈ Icc 0 t from ⟨ht.le,le_rfl⟩) (C := 1) (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hd (hs (n+1)).contDiffAt hy,
        imaginaryExponential_derivative_norm])
  have he : taylorWithinEval imaginaryExponential n (Icc 0 t) 0 t = imaginaryTaylor n t := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv hd (hs k).contDiffAt (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht.le⟩),
      imaginaryExponential_iteratedDeriv]
    simp [imaginaryExponential]
  simpa only [he,sub_zero,one_mul] using hh

end PlanarFalconer

end OAI
