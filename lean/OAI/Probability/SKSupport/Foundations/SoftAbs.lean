import Mathlib
import OAI.Probability.SKSupport.Foundations.BoundedSmooth

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma boundedSmooth_of_polynomial_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {C : ℝ≥0} (hC : ∀ x, |f x| ≤ C) (P : Polynomial ℝ)
    (hD : ∀ x, deriv f x = P.eval (f x)) : BoundedSmooth f := by
  have hrepr : ∀ n : ℕ, ∃ Q : Polynomial ℝ, iteratedDeriv n f = fun x => Q.eval (f x) := by
    intro n
    induction n with
    | zero => exact ⟨Polynomial.X, by funext x; simp⟩
    | succ n IH =>
      obtain ⟨Q,hQ⟩ := IH
      refine ⟨Q.derivative*P, ?_⟩
      rw [iteratedDeriv_succ, hQ]
      funext x
      have hd := (Q.hasDerivAt (f x)).comp x ((hf.differentiable (by simp) x).hasDerivAt)
      simpa only [Function.comp_def, hD, Polynomial.eval_mul] using hd.deriv
  refine ⟨hf, fun n => ?_⟩
  obtain ⟨Q,hQ⟩ := hrepr n
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(C:ℝ)) C)).bddAbove_image
    Q.continuous.abs.continuousOn
  refine ⟨Real.toNNReal R, fun x => ?_⟩
  rw [hQ]
  have hb : |Q.eval (f x)| ≤ R := hR ⟨f x, abs_le.mp (hC x), rfl⟩
  exact hb.trans (Real.le_coe_toNNReal R)

lemma contDiff_tanh : ContDiff ℝ ∞ Real.tanh := by
  have he : Real.tanh = fun x => Real.sinh x/Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => ne_of_gt (Real.cosh_pos x))

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1-(Real.tanh x)^2) x := by
  have hne := ne_of_gt (Real.cosh_pos x)
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hne
  have he : Real.tanh = fun y => Real.sinh y/Real.cosh y := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  convert hd using 1
  field_simp

lemma boundedSmooth_tanh_mul (M : ℝ) : BoundedSmooth (fun x => Real.tanh (M*x)) := by
  apply boundedSmooth_of_polynomial_deriv
    (contDiff_tanh.comp (contDiff_const.mul contDiff_id))
    (C := 1) (fun x => (Real.abs_tanh_lt_one (M*x)).le)
    (Polynomial.C M*(1-Polynomial.X^2))
  intro x
  have hd := (hasDerivAt_tanh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  simp only [Function.comp_def, mul_one] at hd
  convert hd.deriv using 1 <;> try rfl
  all_goals
    try simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X,
      Function.comp_def, id_eq]
    ring

def softAbs (M : ℝ) (x : ℝ) := Real.log (2*Real.cosh (M*x))/M

lemma hasDerivAt_softAbs {M : ℝ} (hM : M ≠ 0) (x : ℝ) :
    HasDerivAt (softAbs M) (Real.tanh (M*x)) x := by
  have hn : 2*Real.cosh (M*x) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt (Real.cosh_pos _))
  have hd := ((((Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)).const_mul 2).log hn).div_const M
  simp only [Function.comp_def, mul_one] at hd
  convert hd using 1 <;> try rfl
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hM, ne_of_gt (Real.cosh_pos (M*x))]

lemma regularDatum_softAbs {M : ℝ} (hM : M ≠ 0) : RegularDatum (softAbs M) := by
  constructor
  · exact ((contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))).log
      (fun x => mul_ne_zero (by norm_num) (ne_of_gt (Real.cosh_pos _)))).div_const M
  · have he : deriv (softAbs M) = fun x => Real.tanh (M*x) := funext (fun x => (hasDerivAt_softAbs hM x).deriv)
    rw [he]
    exact boundedSmooth_tanh_mul M

lemma softAbs_lipschitz {M : ℝ} (hM : M ≠ 0) : LipschitzWith 1 (softAbs M) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_softAbs hM x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one, (hasDerivAt_softAbs hM x).deriv] using
    (Real.abs_tanh_lt_one (M*x)).le

lemma softAbs_even (M : ℝ) : Function.Even (softAbs M) := by
  intro x
  simp [softAbs, Real.cosh_neg]

lemma exp_abs_bounds (y : ℝ) :
    Real.exp |y| ≤ Real.exp y+Real.exp (-y) ∧
      Real.exp y+Real.exp (-y) ≤ 2*Real.exp |y| := by
  constructor
  · by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hy)]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  · have h₁ := Real.exp_le_exp.mpr (le_abs_self y)
    have h₂ := Real.exp_le_exp.mpr (neg_le_abs y)
    linarith

lemma softAbs_bounds {M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 ≤ softAbs M x-|x| ∧ softAbs M x-|x| ≤ Real.log 2/M := by
  have hb := exp_abs_bounds (M*x)
  have habs : |M*x| = M*|x| := by rw [abs_mul, abs_of_nonneg hM.le]
  rw [habs] at hb
  have hc : 2*Real.cosh (M*x) = Real.exp (M*x)+Real.exp (-(M*x)) := by rw [Real.cosh_eq]; ring
  have hlo := Real.log_le_log (Real.exp_pos _) hb.1
  have hhi := Real.log_le_log (add_pos (Real.exp_pos _) (Real.exp_pos _)) hb.2
  rw [Real.log_exp] at hlo
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hhi
  dsimp only [softAbs]
  rw [hc]
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hM).mpr
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hM).mpr
    field_simp
    nlinarith

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma semigroup_add {g : ℝ → ℝ} (h k : ℝ≥0) (x : ℝ)
    (hg : Integrable (fun y => g (x+y)) (gaussianReal 0 (h+k))) :
    semigroup (h+k) g x = semigroup h (semigroup k g) x := by
  have he : gaussianReal 0 (h+k) = (gaussianReal 0 h) ∗ (gaussianReal 0 k) := by
    simpa only [zero_add] using (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0)
      (v₁ := h) (v₂ := k)).symm
  rw [he] at hg
  have hh := integral_conv hg
  simpa only [← he, semigroup, add_assoc] using hh

lemma logSemigroup_add {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c : ℝ) (h k : ℝ≥0) (x : ℝ) :
    logSemigroup c (h+k) f x = logSemigroup c h (logSemigroup c k f) x := by
  by_cases hc : c = 0
  · subst c
    have he : logSemigroup 0 k f = semigroup k f := by funext z; simp [logSemigroup]
    simp only [logSemigroup, ↓reduceIte, he]
    exact semigroup_add h k x (integrable_translate_of_lipschitz hf (h+k) x)
  · have he : (fun z => Real.exp (c*logSemigroup c k f z)) =
        semigroup k (fun z => Real.exp (c*f z)) := by
      funext z
      simp only [logSemigroup, hc, ↓reduceIte]
      rw [mul_div_cancel₀ _ hc, Real.exp_log (semigroup_exp_pos hf c k z)]
    rw [logSemigroup, ite_eq_right hc, logSemigroup, ite_eq_right hc, he]
    rw [semigroup_add h k x (integrable_exp_translate_of_lipschitz hf c (h+k) x)]

lemma logSemigroup_terminal_domination {f g : ℝ → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {c : ℝ} (hc : 0 ≤ c)
    {δ : ℝ} (hδ : ∀ z, f z ≤ g z+δ) (h : ℝ≥0) (x : ℝ) :
    logSemigroup c h f x ≤ logSemigroup c h g x+δ := by
  by_cases hc0 : c = 0
  · subst c
    simp only [logSemigroup, ↓reduceIte]
    have hh := integral_mono (integrable_translate_of_lipschitz hf h x)
      ((integrable_translate_of_lipschitz hg h x).add (integrable_const δ)) (fun y => hδ (x+y))
    change (∫ y, f (x+y) ∂gaussianReal 0 h) ≤ (∫ y, g (x+y)+δ ∂gaussianReal 0 h) at hh
    rw [integral_add (integrable_translate_of_lipschitz hg h x) (integrable_const δ)] at hh
    simpa [semigroup, integral_const, Measure.real] using hh
  · have hcp := lt_of_le_of_ne hc (Ne.symm hc0)
    have hE : semigroup h (fun z => Real.exp (c*f z)) x ≤
        Real.exp (c*δ)*semigroup h (fun z => Real.exp (c*g z)) x := by
      unfold semigroup
      rw [← integral_const_mul]
      apply integral_mono (integrable_exp_translate_of_lipschitz hf c h x)
        ((integrable_exp_translate_of_lipschitz hg c h x).const_mul _)
      intro y
      change Real.exp (c*f (x+y)) ≤ Real.exp (c*δ)*Real.exp (c*g (x+y))
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hδ (x+y)]
    have hh := Real.log_le_log (semigroup_exp_pos hf c h x) hE
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (semigroup_exp_pos hg c h x)), Real.log_exp] at hh
    simp only [logSemigroup, hc0, ↓reduceIte]
    apply (div_le_iff₀ hcp).mpr
    field_simp
    nlinarith

lemma logSemigroup_terminal_stability {f g : ℝ → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {c : ℝ} (hc : 0 ≤ c)
    {δ : ℝ} (hδ : ∀ z, |f z-g z| ≤ δ) (h : ℝ≥0) (x : ℝ) :
    |logSemigroup c h f x-logSemigroup c h g x| ≤ δ := by
  have h₁ := logSemigroup_terminal_domination hf hg hc (δ := δ)
    (fun z => by linarith [(abs_le.mp (hδ z)).2]) h x
  have h₂ := logSemigroup_terminal_domination hg hf hc (δ := δ)
    (fun z => by linarith [(abs_le.mp (hδ z)).1]) h x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
