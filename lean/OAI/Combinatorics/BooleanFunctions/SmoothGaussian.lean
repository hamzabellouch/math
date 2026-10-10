import Mathlib

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothGaussian

/-- A continuous probability of passing a rare interval test. It vanishes
outside the interval, and is rounded to deterministic tests on each finite
input alphabet before constructing any final observation. -/
def tent (a h x : ℝ) : ℝ := max 0 (1 - |x-a| / h)

@[fun_prop] theorem continuous_tent (a h : ℝ) : Continuous (tent a h) := by
  unfold tent
  fun_prop

theorem tent_nonneg (a h x : ℝ) : 0 ≤ tent a h x := le_max_left _ _

theorem tent_le_one {h : ℝ} (hh : 0 < h) (a x : ℝ) : tent a h x ≤ 1 := by
  apply max_le zero_le_one
  have := div_nonneg (abs_nonneg (x-a)) hh.le
  linarith

theorem tent_eq_zero {a h x : ℝ} (hh : 0 < h) (hx : h ≤ |x-a|) :
    tent a h x = 0 := by
  unfold tent
  apply max_eq_left
  have : 1 ≤ |x-a|/h := (one_le_div hh).mpr hx
  linarith

theorem tent_ne_zero_iff {a h x : ℝ} (hh : 0 < h) :
    tent a h x ≠ 0 ↔ |x-a| < h := by
  constructor
  · intro hn
    exact lt_of_not_ge (fun hx => hn (tent_eq_zero hh hx))
  · intro hx
    apply ne_of_gt
    apply lt_of_lt_of_le _ (le_max_right _ _)
    have := (div_lt_one hh).mpr hx
    linarith

theorem tent_support {a h : ℝ} (hh : 0 < h) :
    Function.support (tent a h) ⊆ Set.Icc (a-h) (a+h) := by
  intro x hx
  have he := (tent_ne_zero_iff hh).mp hx
  rw [abs_lt] at he
  constructor <;> linarith

theorem tent_compactSupport {a h : ℝ} (hh : 0 < h) : HasCompactSupport (tent a h) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a-h) (b := a+h))
  intro x hx
  by_contra hn
  exact hx (tent_support hh hn)

theorem tent_half {a h x : ℝ} (hh : 0 < h) (hx : |x-a| ≤ h/2) :
    1/2 ≤ tent a h x := by
  apply le_trans _ (le_max_right _ _)
  have : |x-a|/h ≤ 1/2 := (div_le_iff₀ hh).mpr (by linarith)
  linarith

theorem integrable_tent_mul {a h : ℝ} (hh : 0 < h) (p : ℝ → ℝ) (hp : Continuous p)
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] :
    Integrable (fun x => tent a h x * p x) μ := by
  apply ((continuous_tent a h).mul hp).integrable_of_hasCompactSupport
  exact (tent_compactSupport hh).mul_right

theorem pdf_lower {A x : ℝ} (hx : |x| ≤ A) :
    (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(A^2)/2) ≤ gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have : x^2 ≤ A^2 := by nlinarith [abs_nonneg x, sq_abs x]
  linarith

theorem beta_lower {a h : ℝ} (hh : 0 < h) :
    h/2 * ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2)) ≤
      ∫ x, tent a h x ∂gaussianReal 0 1 := by
  let c := (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha := integrable_tent_mul (a := a) hh (gaussianPDFReal 0 1) (by
    unfold gaussianPDFReal; fun_prop) volume
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  change h/2*c ≤ ∫ x, gaussianPDFReal 0 1 x * tent a h x
  have hi : Integrable (fun x => gaussianPDFReal 0 1 x * tent a h x) volume := by
    simpa only [mul_comm] using ha
  have hset : ∫ x in Set.Icc (a-h/2) (a+h/2), c/2 ≤
      ∫ x in Set.Icc (a-h/2) (a+h/2), gaussianPDFReal 0 1 x * tent a h x := by
    apply integral_mono_ae (integrable_const _) hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hab : |x-a| ≤ h/2 := abs_le.mpr (by constructor <;> linarith [hx.1,hx.2])
    have hp : c ≤ gaussianPDFReal 0 1 x := by
      apply pdf_lower
      calc |x| = |(x-a)+a| := by congr 1; ring
        _ ≤ |x-a|+|a| := abs_add_le _ _
        _ ≤ |a|+h := by linarith
    have hw := tent_half hh hab
    calc c/2 = c * (1/2) := by ring
      _ ≤ gaussianPDFReal 0 1 x * tent a h x :=
        mul_le_mul hp hw (by norm_num) (gaussianPDFReal_nonneg ..)
  have hs : ∫ x in Set.Icc (a-h/2) (a+h/2), gaussianPDFReal 0 1 x * tent a h x ≤
      ∫ x, gaussianPDFReal 0 1 x * tent a h x := by
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun x => mul_nonneg (gaussianPDFReal_nonneg ..) (tent_nonneg ..))) hi
  apply le_trans _ (hset.trans hs)
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ a+h/2-(a-h/2))]
  ring_nf
  exact le_rfl



def mass (μ : Measure ℝ) (w : ℝ → ℝ) : ℝ := ∫ x, w x ∂μ

def mean (μ : Measure ℝ) (w : ℝ → ℝ) : ℝ := (∫ x, w x * x ∂μ) / mass μ w

def variance (μ : Measure ℝ) (w : ℝ → ℝ) : ℝ :=
  (∫ x, w x * x^2 ∂μ) / mass μ w - mean μ w ^ 2

theorem integral_weight_sub_sq (μ : Measure ℝ) (w : ℝ → ℝ)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x * x) μ)
    (h2 : Integrable (fun x => w x * x^2) μ) (c : ℝ) :
    (∫ x, w x * (x-c)^2 ∂μ) = (∫ x, w x * x^2 ∂μ) -
      2*c*(∫ x, w x * x ∂μ) + c^2*mass μ w := by
  have he : (fun x => w x * (x-c)^2) = fun x =>
      w x * x^2 - (2*c)*(w x*x) + c^2*w x := by funext x; ring
  rw [he, integral_add (f := fun x => w x*x^2-(2*c)*(w x*x))
    (g := fun x => c^2*w x) (h2.sub (h1.const_mul (2*c))) (h0.const_mul (c^2)),
    integral_sub h2 (h1.const_mul (2*c)), integral_const_mul, integral_const_mul]
  rfl

theorem mean_mul_mass (μ : Measure ℝ) (w : ℝ → ℝ) (hb : mass μ w ≠ 0) :
    mean μ w * mass μ w = ∫ x, w x * x ∂μ := by
  simp [mean, hb]

theorem variance_mul_mass (μ : Measure ℝ) (w : ℝ → ℝ)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x * x) μ)
    (h2 : Integrable (fun x => w x * x^2) μ) (hb : mass μ w ≠ 0) :
    variance μ w * mass μ w = ∫ x, w x * (x-mean μ w)^2 ∂μ := by
  rw [integral_weight_sub_sq μ w h0 h1 h2]
  have hm := mean_mul_mass μ w hb
  rw [← hm]
  unfold variance
  field_simp [hb]
  ring

theorem weighted_interval_bounds (μ : Measure ℝ) (w : ℝ → ℝ) {a h : ℝ}
    (hh : 0 ≤ h) (hw : ∀ x, 0 ≤ w x)
    (hs : ∀ x, w x ≠ 0 → |x-a| ≤ h)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x*x) μ)
    (h2 : Integrable (fun x => w x*x^2) μ) (hb : 0 < mass μ w) :
    |mean μ w-a| ≤ h ∧ 0 ≤ variance μ w ∧ variance μ w ≤ h^2 := by
  have hlo : (a-h)*mass μ w ≤ ∫ x, w x*x ∂μ := by
    rw [mass, ← integral_const_mul]
    apply integral_mono (h0.const_mul _) h1
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have ht := (abs_le.mp (hs x hx)).1
      nlinarith [mul_nonneg (hw x) (show 0 ≤ x-(a-h) by linarith)]
  have hhi : (∫ x, w x*x ∂μ) ≤ (a+h)*mass μ w := by
    rw [mass, ← integral_const_mul]
    apply integral_mono h1 (h0.const_mul _)
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have ht := (abs_le.mp (hs x hx)).2
      nlinarith [mul_nonneg (hw x) (show 0 ≤ (a+h)-x by linarith)]
  have hm := mean_mul_mass μ w hb.ne'
  have hmean : |mean μ w-a| ≤ h := by
    rw [abs_le]
    constructor <;> nlinarith
  have hv := variance_mul_mass μ w h0 h1 h2 hb.ne'
  have hv0 : 0 ≤ variance μ w := by
    have hn : 0 ≤ ∫ x, w x*(x-mean μ w)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg (x-mean μ w)))
    rw [← hv] at hn
    exact nonneg_of_mul_nonneg_left hn hb
  have hsq : ∫ x, w x*(x-a)^2 ∂μ ≤ h^2*mass μ w := by
    rw [mass, ← integral_const_mul]
    have he : Integrable (fun x => w x*(x-a)^2) μ := by
      convert! (h2.sub (h1.const_mul (2*a))).add (h0.const_mul (a^2)) using 1
      funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
    apply integral_mono he (h0.const_mul _)
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have ht : (x-a)^2 ≤ h^2 := by nlinarith [sq_abs (x-a),hs x hx, abs_nonneg (x-a)]
      nlinarith [mul_nonneg (hw x) (sub_nonneg.mpr ht)]
  rw [integral_weight_sub_sq μ w h0 h1 h2] at hsq
  have hmoment : (∫ x, w x*x^2 ∂μ) = (variance μ w + mean μ w^2)*mass μ w := by
    dsimp [variance]
    field_simp [hb.ne']
    ring
  have hvar : variance μ w ≤ h^2 := by
    have he := mul_nonneg hb.le (sq_nonneg (mean μ w-a))
    rw [hmoment, ← hm] at hsq
    nlinarith
  exact ⟨hmean,hv0,hvar⟩

theorem tent_mass_pos {a h : ℝ} (hh : 0 < h) :
    0 < mass (gaussianReal 0 1) (tent a h) := by
  apply lt_of_lt_of_le _ (beta_lower hh)
  positivity

theorem tent_moments {a h : ℝ} (hh : 0 < h) :
    |mean (gaussianReal 0 1) (tent a h)-a| ≤ h ∧
    0 ≤ variance (gaussianReal 0 1) (tent a h) ∧
    variance (gaussianReal 0 1) (tent a h) ≤ h^2 := by
  apply weighted_interval_bounds (gaussianReal 0 1) (tent a h) hh.le (tent_nonneg a h)
  · intro x hx
    exact le_of_lt ((tent_ne_zero_iff hh).mp hx)
  · simpa using integrable_tent_mul (a := a) hh (fun _ => 1) continuous_const (gaussianReal 0 1)
  · exact integrable_tent_mul hh id continuous_id (gaussianReal 0 1)
  · exact integrable_tent_mul hh (fun x => x^2) (by fun_prop) (gaussianReal 0 1)
  · exact tent_mass_pos hh

end SmoothGaussian
end SquareRootDegree

end

end OAI
