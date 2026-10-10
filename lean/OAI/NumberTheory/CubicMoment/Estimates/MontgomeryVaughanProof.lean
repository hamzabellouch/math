import OAI.NumberTheory.CubicMoment.Estimates.MeanValueGaussianEnergy

namespace OAI

/-! The required ordinary mean value bound, proved by a Gaussian majorant. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def ordinaryMeanValueConstant : ℝ :=
  Real.exp 1*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ))))

lemma integerNormPolynomial_continuous (Z : ℕ) (v : ℕ → ℂ) :
    Continuous (integerNormPolynomial Z v) := by
  unfold integerNormPolynomial mellinPhase
  fun_prop

lemma gaussian_interval_majorant {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b)
    (ha : -L ≤ a) (hb : b ≤ L) (Z : ℕ) (v : ℕ → ℂ) :
    (∫ t in a..b, ‖integerNormPolynomial Z v t‖^2) ≤
      Real.exp 1*(∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) := by
  let f := fun t : ℝ => ‖integerNormPolynomial Z v t‖^2
  let g := fun t : ℝ => meanValueGaussianWeight L t*f t
  have hf : IntervalIntegrable f volume a b :=
    ((integerNormPolynomial_continuous Z v).norm.pow 2).intervalIntegrable _ _
  have hg : Integrable g := meanValueGaussian_integrable hL Z v
  have hgI : IntervalIntegrable g volume a b := hg.intervalIntegrable
  have hbound : ∀ t ∈ Set.Icc a b, f t ≤ Real.exp 1*g t := by
    intro t ht
    have htL : |t| ≤ L := abs_le.mpr ⟨ha.trans ht.1,ht.2.trans hb⟩
    have hratio : |t/L| ≤ 1 := by
      rw [abs_div,abs_of_pos hL]
      exact (div_le_one hL).mpr htL
    have hsq : (t/L)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hratio
    have he : 1 ≤ Real.exp 1*meanValueGaussianWeight L t := by
      rw [meanValueGaussianWeight,← Real.exp_add]
      calc
        1 = Real.exp 0 := Real.exp_zero.symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    calc
      f t = 1*f t := by ring
      _ ≤ (Real.exp 1*meanValueGaussianWeight L t)*f t :=
        mul_le_mul_of_nonneg_right he (sq_nonneg _)
      _ = _ := by dsimp [g]; ring
  calc
    _ ≤ ∫ t in a..b, Real.exp 1*g t :=
      intervalIntegral.integral_mono_on hab hf (hgI.const_mul _) hbound
    _ = Real.exp 1*(∫ t in a..b, g t) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral hg (Filter.Eventually.of_forall
        (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))

lemma integerNormPolynomial_translate (Z : ℕ) (v : ℕ → ℂ) (t c : ℝ) :
    integerNormPolynomial Z v (t+c) =
      integerNormPolynomial Z (fun n => v n*mellinPhase c (n:ℝ)) t := by
  unfold integerNormPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [mellinPhase_add]
  ring

lemma ordinaryMeanValueConstant_pos : 0 < ordinaryMeanValueConstant := by
  unfold ordinaryMeanValueConstant
  have he : Real.exp (-(1/4:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  positivity

/-- The ordinary Dirichlet-polynomial mean-square bound. -/
theorem montgomeryVaughanBound_proved : MontgomeryVaughanBound ordinaryMeanValueConstant := by
  intro Z v a b hab
  by_cases hZ : Z = 0
  · subst Z
    simp [integerNormPolynomial]
  have hZpos : (0:ℝ) < Z := by exact_mod_cast Nat.pos_of_ne_zero hZ
  let L : ℝ := b-a+Z
  let c : ℝ := (a+b)/2
  let w : ℕ → ℂ := fun n => v n*mellinPhase c (n:ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hZL : (Z:ℝ) ≤ L := by dsimp [L]; linarith
  have he : (∫ t in a..b, ‖integerNormPolynomial Z v t‖^2) =
      ∫ t in a-c..b-c, ‖integerNormPolynomial Z w t‖^2 := by
    have hs := intervalIntegral.integral_comp_add_right
      (a := a-c) (b := b-c) (fun t => ‖integerNormPolynomial Z v t‖^2) c
    simp only [sub_add_cancel] at hs
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖integerNormPolynomial Z v (t+c)‖^2 = ‖integerNormPolynomial Z w t‖^2
    rw [integerNormPolynomial_translate]
  have henergy : (∑ n ∈ Finset.Icc 1 Z, ‖w n‖^2) =
      ∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
    simp only [w,norm_mul,mellinPhase_norm,mul_one]
  rw [he]
  calc
    _ ≤ Real.exp 1*(∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z w t‖^2) :=
      gaussian_interval_majorant hL (by linarith) (by dsimp [L,c]; linarith)
        (by dsimp [L,c]; linarith) Z w
    _ ≤ Real.exp 1*((L*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ)))))*
        ∑ n ∈ Finset.Icc 1 Z, ‖w n‖^2) :=
      mul_le_mul_of_nonneg_left (integerNormPolynomial_gaussian_meanSquare hL hZL w)
        (Real.exp_pos _).le
    _ = _ := by rw [henergy]; unfold ordinaryMeanValueConstant; dsimp [L]; ring

end CubicFirstMoment

end

end OAI
