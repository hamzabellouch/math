import Mathlib
import OAI.Probability.SKValue.Evolution.HeatContinuity
import OAI.Probability.SKValue.Equations.JetAlgebra

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def logCoshTerminal (M x : ℝ) : ℝ := Real.log (2*Real.cosh (M*x))/M

lemma logCoshTerminal_smooth (M : ℝ) : ContDiff ℝ ∞ (logCoshTerminal M) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))
  · intro x
    exact (mul_pos (by norm_num) (Real.cosh_pos (M*x))).ne'

lemma logCoshTerminal_hasDerivAt {M : ℝ} (hM : M≠0) (x : ℝ) :
    HasDerivAt (logCoshTerminal M) (Real.tanh (M*x)) x := by
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := ((hc.const_mul 2).log (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos (M*x))).ne').div_const M
  convert! hd using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [Function.comp_apply, mul_one]
  field_simp

lemma tanh_scaled_hasDerivAt (M x : ℝ) :
    HasDerivAt (fun x ↦ Real.tanh (M*x)) (M*(1-(Real.tanh (M*x))^2)) x := by
  have hs := (Real.hasDerivAt_sinh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := hs.div hc (Real.cosh_pos (M*x)).ne'
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  convert! hd using 1
  simp only [Function.comp_apply, mul_one]
  field_simp [(Real.cosh_pos (M*x)).ne']

namespace JetExpr
noncomputable def fieldJet (σ : ℕ → JetExpr) (e : JetExpr) : ℕ → JetExpr
  | 0 => e
  | n+1 => D σ (fieldJet σ e n)

lemma iteratedDeriv_fieldJet {R : ℕ → ℝ → ℝ} {σ : ℕ → JetExpr}
    (hd : ∀ j x, HasDerivAt (R j) (eval (fun i ↦ R i x) (σ j)) x) (e : JetExpr) (n : ℕ) :
    iteratedDeriv n (fun x ↦ eval (fun j ↦ R j x) e)=
      fun x ↦ eval (fun j ↦ R j x) (fieldJet σ e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (hasDerivAt_eval (fun j ↦ hd j x) _).deriv
end JetExpr

lemma logCoshTerminal_jets {M : ℝ} (hM : M≠0) :
    BoundedSmooth (deriv (logCoshTerminal M)) := by
  refine ⟨(contDiff_infty_iff_deriv.mp (logCoshTerminal_smooth M)).2,?_⟩
  intro n
  let σ : ℕ → JetExpr := fun _ ↦ JetExpr.mul (JetExpr.const M)
    (JetExpr.add (JetExpr.const 1) (JetExpr.mul (JetExpr.const (-1)) (JetExpr.mul (JetExpr.coord 0) (JetExpr.coord 0))))
  let R : ℕ → ℝ → ℝ := fun _ x ↦ Real.tanh (M*x)
  have hd : ∀ j x, HasDerivAt (R j) (JetExpr.eval (fun i ↦ R i x) (σ j)) x := by
    intro j x
    convert! tanh_scaled_hasDerivAt M x using 1
    dsimp [σ,JetExpr.eval,R]
    ring
  have he : deriv (logCoshTerminal M)=fun x ↦ JetExpr.eval (fun j ↦ R j x) (JetExpr.coord 0) := by
    funext x
    exact (logCoshTerminal_hasDerivAt hM x).deriv
  rw [he,JetExpr.iteratedDeriv_fieldJet hd]
  exact JetExpr.uniform_bound (fun _ ↦ ⟨1,by norm_num,fun x ↦ (Real.abs_tanh_lt_one (M*x)).le⟩) _

lemma logCoshTerminal_smoothTerminal {M : ℝ} (hM : 0<M) : SmoothTerminal (logCoshTerminal M) := by
  have hs := logCoshTerminal_smooth M
  refine ⟨?_,hs,logCoshTerminal_jets hM.ne'⟩
  apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)))
  intro x
  have he := (logCoshTerminal_hasDerivAt hM.ne' x).deriv
  rw [he]
  exact_mod_cast (Real.abs_tanh_lt_one (M*x)).le

lemma logCoshTerminal_even (M x : ℝ) : logCoshTerminal M (-x)=logCoshTerminal M x := by
  simp only [logCoshTerminal,mul_neg,Real.cosh_neg]

lemma log_two_cosh_bounds (z : ℝ) : |z|≤Real.log (2*Real.cosh z) ∧
    Real.log (2*Real.cosh z)≤|z|+Real.log 2 := by
  have he : 2*Real.cosh z=Real.exp z+Real.exp (-z) := by rw [Real.cosh_eq]; ring
  have h1 : Real.exp |z|≤Real.exp z+Real.exp (-z) := by
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
      linarith [Real.exp_pos (-z)]
    · rw [abs_of_nonpos hz]
      linarith [Real.exp_pos z]
  have h2 : Real.exp z+Real.exp (-z)≤2*Real.exp |z| := by
    have hh1 := Real.exp_le_exp.mpr (le_abs_self z)
    have hh2 := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  constructor
  · have hh := Real.log_le_log (Real.exp_pos |z|) h1
    simpa only [←he,Real.log_exp] using hh
  · have hh := Real.log_le_log (add_pos (Real.exp_pos z) (Real.exp_pos (-z))) h2
    rw [Real.log_mul (by norm_num) (Real.exp_pos |z|).ne',Real.log_exp,←he] at hh
    linarith

lemma logCoshTerminal_uniform_error {M : ℝ} (hM : 0<M) (x : ℝ) :
    |logCoshTerminal M x - abs x| ≤ Real.log 2/M := by
  obtain ⟨hl,hu⟩ := log_two_cosh_bounds (M*x)
  rw [abs_mul,abs_of_pos hM] at hl hu
  have hl' : |x|≤logCoshTerminal M x := by
    apply (le_div_iff₀ hM).mpr
    simpa only [mul_comm] using hl
  rw [abs_of_nonneg (sub_nonneg.mpr hl')]
  apply (sub_le_iff_le_add).mpr
  change Real.log (2*Real.cosh (M*x))/M≤_+|x|
  apply (div_le_iff₀ hM).mpr
  field_simp
  nlinarith

end SKValue

end

end OAI
