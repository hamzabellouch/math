import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! The conformal series and its logarithmic derivative. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

def term (p k : ℕ) (w : ℂ) : ℂ := w ^ (2*k+1) / ((2*k+1 : ℕ) : ℂ)^p
def series (p : ℕ) (w : ℂ) : ℂ := ∑' k, term p k w
def F (w : ℂ) : ℂ := (8 / (Real.pi : ℂ)^2) * series 2 w
def H (w : ℂ) : ℂ := series 1 w

lemma odd_cast_ne (k : ℕ) : ((2*k+1 : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (show 2*k+1 ≠ 0 by omega)

lemma term_bound (p k : ℕ) (w : ℂ) :
    ‖term p k w‖ ≤ ‖w‖ ^ (2*k+1) := by
  rw [term, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  apply div_le_self (by positivity)
  exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ 2*k+1 by omega))

theorem summable_series {w : ℂ} (hw : ‖w‖ < 1) (p : ℕ) :
    Summable (fun k => term p k w) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).comp_injective
      (show Function.Injective (fun k : ℕ => 2*k+1) by intro a b h; dsimp at h; omega))
  intro k
  exact term_bound p k w

lemma series_zero (p : ℕ) : series p 0 = 0 := by
  simp [series, term]

lemma term_deriv_one (k : ℕ) (w : ℂ) :
    HasDerivAt (term 1 k) (w^(2*k)) w := by
  have hd := (hasDerivAt_pow (2*k+1) w).div_const (((2*k+1 : ℕ) : ℂ)^1)
  change HasDerivAt (term 1 k) _ w at hd
  convert hd using 1
  simp only [Nat.add_sub_cancel, pow_one]
  field_simp [odd_cast_ne k]
  exact (mul_div_cancel_right₀ _ (odd_cast_ne k)).symm

lemma term_deriv_two (k : ℕ) (w : ℂ) :
    HasDerivAt (term 2 k) (w^(2*k) / ((2*k+1 : ℕ) : ℂ)) w := by
  have hd := (hasDerivAt_pow (2*k+1) w).div_const (((2*k+1 : ℕ) : ℂ)^2)
  change HasDerivAt (term 2 k) _ w at hd
  convert hd using 1
  simp only [Nat.add_sub_cancel]
  field_simp [odd_cast_ne k]

lemma derivative_bound (k : ℕ) {w : ℂ} {r : ℝ} (_hr : 0 ≤ r) (hw : ‖w‖ < r) :
    ‖w^(2*k) / ((2*k+1 : ℕ) : ℂ)‖ ≤ r^(2*k) := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  exact (div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ 2*k+1 by omega))).trans
    (pow_le_pow_left₀ (norm_nonneg _) hw.le _)

theorem hasDerivAt_series_two {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (series 2) (∑' k : ℕ, w^(2*k) / ((2*k+1 : ℕ) : ℂ)) w := by
  obtain ⟨r, hwr, hr⟩ := exists_between hw
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
  have hu : Summable (fun k : ℕ => r^(2*k)) := by
    exact (summable_geometric_of_lt_one hr0.le hr).comp_injective
      (by intro a b h; omega)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun k z _ => term_deriv_two k z)
    (fun k z hz => derivative_bound k hr0.le (by simpa using hz))
    (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)
    (by simp [term]) (by simpa using hwr)

theorem hasDerivAt_H {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt H (1-w^2)⁻¹ w := by
  obtain ⟨r, hwr, hr⟩ := exists_between hw
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
  have hu : Summable (fun k : ℕ => r^(2*k)) :=
    (summable_geometric_of_lt_one hr0.le hr).comp_injective (by intro a b h; omega)
  have hd : HasDerivAt H (∑' k : ℕ, w^(2*k)) w :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_ball
      (convex_ball (0 : ℂ) r).isPreconnected
      (fun k z _ => term_deriv_one k z)
      (fun k z hz => by
        change ‖z^(2*k)‖ ≤ r^(2*k)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (show ‖z‖ ≤ r from (show ‖z‖ < r by simpa using hz).le) _)
      (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)
      (by simp [term]) (by simpa using hwr)
  have hw2 : ‖w^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hs : (∑' k : ℕ, w^(2*k)) = (1-w^2)⁻¹ := by
    simpa only [pow_mul] using tsum_geometric_of_norm_lt_one hw2
  rwa [hs] at hd

lemma one_sub_ne {w : ℂ} (hw : ‖w‖ < 1) : 1-w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hw

lemma one_add_ne {w : ℂ} (hw : ‖w‖ < 1) : 1+w ≠ 0 := by
  simpa using one_sub_ne (w := -w) (by simpa using hw)

lemma one_sub_sq_ne {w : ℂ} (hw : ‖w‖ < 1) : 1-w^2 ≠ 0 := by
  apply one_sub_ne
  rw [norm_pow]
  nlinarith [norm_nonneg w]

def cayley (w : ℂ) : ℂ := (1+w)/(1-w)

/-- The branch-domain assertion for the logarithmic derivative. -/
theorem cayley_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  have hn : w.re*w.re+w.im*w.im < 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  rw [cayley, Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr (one_sub_ne hw))
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.sub_im, Complex.one_im]
  nlinarith

lemma hasDerivAt_log_cayley {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (fun z => Complex.log (cayley z)) (2*(1-w^2)⁻¹) w := by
  have hq := ((hasDerivAt_const w (1 : ℂ)).add (hasDerivAt_id w)).div
    ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)) (one_sub_ne hw)
  have hd := (Complex.hasDerivAt_log (Or.inl (cayley_re_pos hw))).comp w hq
  change HasDerivAt (fun z => Complex.log (cayley z)) _ w at hd
  convert hd using 1
  dsimp [cayley]
  field_simp [one_sub_ne hw, one_add_ne hw, one_sub_sq_ne hw]
  ring

/-- Auxiliary logarithm identity, established without assuming a logarithmic series. -/
theorem two_H_eq_log {w : ℂ} (hw : ‖w‖ < 1) :
    2 * H w = Complex.log (cayley w) := by
  have h₁ : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun t => 2*H t) (2*(1-z^2)⁻¹) z := by
    intro z hz
    exact (hasDerivAt_H (by simpa using hz)).const_mul 2
  have h₂ : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun t => Complex.log (cayley t)) (2*(1-z^2)⁻¹) z := by
    intro z hz
    exact hasDerivAt_log_cayley (by simpa using hz)
  exact isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) 1).isPreconnected
    (fun z hz => (h₁ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h₂ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h₁ z hz).deriv.trans (h₂ z hz).deriv.symm)
    (show (0 : ℂ) ∈ ball 0 1 by simp)
    (by simp [H, series_zero, cayley]) (by simpa using hw)

def D (w : ℂ) : ℂ := ∑' k : ℕ, w^(2*k) / ((2*k+1 : ℕ) : ℂ)

lemma w_mul_D (w : ℂ) : w * D w = H w := by
  unfold D H series term
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [pow_succ]
  ring

lemma D_zero : D 0 = 1 := by
  unfold D
  rw [tsum_eq_single 0]
  · norm_num
  · intro k hk
    have hp : 2*k ≠ 0 := by omega
    simp [zero_pow hp]

lemma pi_cast_ne : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- Termwise differentiation of the conformal series. -/
theorem hasDerivAt_F_series {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt F ((8/(Real.pi : ℂ)^2) * D w) w :=
  (hasDerivAt_series_two hw).const_mul _

/-- Holomorphicity on the open unit disk. -/
theorem differentiableOn_F : DifferentiableOn ℂ F (ball 0 1) := by
  intro w hw
  exact (hasDerivAt_F_series (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem F_zero : F 0 = 0 := by simp [F, series_zero]

/-- The removable value of the derivative at zero. -/
theorem hasDerivAt_F_zero : HasDerivAt F (8/(Real.pi : ℂ)^2) 0 := by
  simpa [D_zero] using hasDerivAt_F_series (w := 0) (by norm_num)

/-- The derivative formula away from zero, with the principal logarithm. -/
theorem hasDerivAt_F_log {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    HasDerivAt F (4/((Real.pi : ℂ)^2*w) * Complex.log ((1+w)/(1-w))) w := by
  have he : (8/(Real.pi : ℂ)^2) * D w =
      4/((Real.pi : ℂ)^2*w) * Complex.log ((1+w)/(1-w)) := by
    rw [show Complex.log ((1+w)/(1-w)) = 2*H w from (two_H_eq_log hw).symm, ← w_mul_D]
    field_simp
    ring
  exact he ▸ hasDerivAt_F_series hw

lemma log_cayley_ne_zero {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    Complex.log (cayley w) ≠ 0 := by
  intro h
  have hq0 : cayley w ≠ 0 := div_ne_zero (one_add_ne hw) (one_sub_ne hw)
  have he : cayley w = 1 := by rw [← Complex.exp_log hq0, h, Complex.exp_zero]
  have hl : 1+w = 1-w := (div_eq_one_iff_eq (one_sub_ne hw)).mp he
  apply hw0
  linear_combination (1/2 : ℂ) * hl

/-- Nonvanishing of the derivative. -/
theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_F_zero.deriv]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ pi_cast_ne)
  · rw [(hasDerivAt_F_log hw hw0).deriv]
    exact mul_ne_zero
      (div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ pi_cast_ne) hw0))
      (log_cayley_ne_zero hw hw0)

/-- Convergence to the normalized conformal series. -/
theorem hasSum_F {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => (8/(Real.pi : ℂ)^2) *
      (w^(2*k+1) / ((2*k+1 : ℕ) : ℂ)^2)) (F w) :=
  (summable_series hw 2).hasSum.mul_left _

/-- Oddness of the conformal map. -/
theorem F_odd (w : ℂ) : F (-w) = -F w := by
  have ht : ∀ k, term 2 k (-w) = -term 2 k w := by
    intro k
    simp [term, pow_add, pow_mul, neg_div]
  simp only [F, series, ht, tsum_neg, mul_neg]

/-- Conjugation symmetry of the conformal map. -/
theorem F_conj (w : ℂ) : F (starRingEnd ℂ w) = starRingEnd ℂ (F w) := by
  simp only [F, series, term, map_mul, map_div₀, map_pow, map_ofNat,
    map_natCast, Complex.conj_ofReal, Complex.conj_tsum]

/-- The logarithmic derivative formula has a removable limit at zero. -/
theorem log_formula_limit_zero :
    Filter.Tendsto (fun w : ℂ =>
      4/((Real.pi : ℂ)^2*w) * Complex.log ((1+w)/(1-w)))
      (𝓝[≠] 0) (𝓝 (8/(Real.pi : ℂ)^2)) := by
  have hh : Filter.Tendsto (fun w : ℂ => H w / w) (𝓝[≠] 0) (𝓝 1) := by
    simpa [H, series_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using (hasDerivAt_H (w := 0) (by simp)).tendsto_slope_zero
  have hl : Filter.Tendsto (fun w : ℂ => (8/(Real.pi : ℂ)^2) * (H w/w))
      (𝓝[≠] 0) (𝓝 (8/(Real.pi : ℂ)^2)) := by
    simpa using tendsto_const_nhds.mul hh
  have hdisk : ∀ᶠ w : ℂ in 𝓝[≠] 0, ‖w‖ < 1 := by
    have hb : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (by simp)
    exact Filter.mem_of_superset (nhdsWithin_le_nhds hb) (by intro w hw; simpa using hw)
  apply hl.congr'
  filter_upwards [hdisk] with w hw
  rw [show Complex.log ((1+w)/(1-w)) = 2*H w from (two_H_eq_log hw).symm]
  field_simp
  ring

/-- The conformal series, its derivative including zero,
nonvanishing, and the logarithm branch domain. -/
theorem conformal_series_main (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => (8/(Real.pi : ℂ)^2) *
      (w^(2*k+1) / ((2*k+1 : ℕ) : ℂ)^2)) (F w) ∧
    HasDerivAt F (if w = 0 then 8/(Real.pi : ℂ)^2
      else 4/((Real.pi : ℂ)^2*w) * Complex.log ((1+w)/(1-w))) w ∧
    deriv F w ≠ 0 ∧ 0 < ((1+w)/(1-w)).re := by
  refine ⟨hasSum_F hw, ?_, deriv_F_ne_zero hw, cayley_re_pos hw⟩
  by_cases h : w = 0
  · subst w
    simpa using hasDerivAt_F_zero
  · simpa [h] using hasDerivAt_F_log hw h

end MahlerConformal

end

end OAI
