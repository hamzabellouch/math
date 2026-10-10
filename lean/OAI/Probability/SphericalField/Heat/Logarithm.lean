import Mathlib
import OAI.Probability.SphericalField.Heat.Average

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
def heatLog (s : ℝ≥0) (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  if d = 0 then gaussianAverage s f x else (d : ℝ)⁻¹ * Real.log (gaussianAverage s (expBCF d f) x)

lemma heatLog_abs_le (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : |heatLog s d f x| ≤ ‖f‖ := by
  unfold heatLog
  split_ifs with hd
  · exact gaussianAverage_abs_le s f x
  have hd' : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  obtain ⟨hlo,hhi⟩ := gaussianAverage_exp_bounds s d d.coe_nonneg f x
  have hz := gaussianAverage_exp_pos s d f x
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hu := Real.log_le_log hz hhi
  rw [Real.log_exp] at hl hu
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hd'.le),
    mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hd'.le), inv_mul_cancel₀ hd'.ne']

lemma heatLog_continuous (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : Continuous (heatLog s d f) := by
  change Continuous (fun x => heatLog s d f x)
  by_cases hd : d = 0
  · simpa [heatLog, hd] using gaussianAverage_continuous s f
  · have hh := (gaussianAverage_continuous s (expBCF d f)).log (fun x => (gaussianAverage_exp_pos s d f x).ne')
    simpa only [heatLog, hd, ↓reduceIte] using hh.const_mul (d : ℝ)⁻¹

def heatLogBCF (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨heatLog s d f, heatLog_continuous s d f⟩
    (2*‖f‖) (by
      intro x y; change |heatLog s d f x - heatLog s d f y| ≤ 2 * ‖f‖
      exact (abs_sub _ _).trans (by linarith [heatLog_abs_le s d f x, heatLog_abs_le s d f y]))

@[simp] lemma heatLogBCF_coe (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (heatLogBCF s d f : ℝ → ℝ) = heatLog s d f := rfl

lemma exp_heatLog (s d : ℝ≥0) (hd : d ≠ 0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (d * heatLog s d f x) = gaussianAverage s (expBCF d f) x := by
  simp only [heatLog, hd, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hd), one_mul,
    Real.exp_log (gaussianAverage_exp_pos s d f x)]

lemma heatLog_zero (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : heatLog 0 d f x = f x := by
  by_cases hd : d = 0
  · simp [heatLog, hd]
  · simp [heatLog, hd]

lemma heatLog_semigroup (s t d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    heatLog s d (heatLogBCF t d f) x = heatLog (s+t) d f x := by
  by_cases hd : d = 0
  · subst d
    have he : heatLogBCF t 0 f = gaussianAverageBCF t f := by ext z; simp [heatLog]
    simp only [heatLog, ↓reduceIte, he]
    exact gaussianAverage_semigroup s t f x
  · have he : expBCF d (heatLogBCF t d f) = gaussianAverageBCF t (expBCF d f) := by
      ext z
      exact exp_heatLog t d hd f z
    simp only [heatLog, hd, ↓reduceIte, he, gaussianAverage_semigroup]

structure Jet3 where
  f : ℝ →ᵇ ℝ
  d1 : ℝ →ᵇ ℝ
  d2 : ℝ →ᵇ ℝ
  d3 : ℝ →ᵇ ℝ
  has1 : ∀ x, HasDerivAt (f : ℝ → ℝ) (d1 x) x
  has2 : ∀ x, HasDerivAt (d1 : ℝ → ℝ) (d2 x) x
  has3 : ∀ x, HasDerivAt (d2 : ℝ → ℝ) (d3 x) x

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv
lemma Jet3.deriv2_eq (g : Jet3) : iteratedDeriv 2 (g.f : ℝ → ℝ) = g.d2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, g.deriv_eq]
  exact funext fun x => (g.has2 x).deriv
lemma Jet3.deriv3_eq (g : Jet3) : iteratedDeriv 3 (g.f : ℝ → ℝ) = g.d3 := by
  rw [iteratedDeriv_succ, g.deriv2_eq]
  exact funext fun x => (g.has3 x).deriv

lemma Jet3.contDiff (g : Jet3) : ContDiff ℝ 3 (g.f : ℝ → ℝ) := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has1 x).differentiableAt, by norm_num, ?_⟩
  rw [g.deriv_eq, show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has2 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d1 : ℝ → ℝ) = g.d2 from funext fun x => (g.has2 x).deriv,
    show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has3 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d2 : ℝ → ℝ) = g.d3 from funext fun x => (g.has3 x).deriv]
  exact contDiff_zero.mpr g.d3.continuous

def Jet3.gaussianAverage (s : ℝ≥0) (g : Jet3) : Jet3 where
  f := gaussianAverageBCF s g.f
  d1 := gaussianAverageBCF s g.d1
  d2 := gaussianAverageBCF s g.d2
  d3 := gaussianAverageBCF s g.d3
  has1 := gaussianAverage_hasDerivAt s g.f g.d1 g.has1
  has2 := gaussianAverage_hasDerivAt s g.d1 g.d2 g.has2
  has3 := gaussianAverage_hasDerivAt s g.d2 g.d3 g.has3

lemma Jet3.gaussianAverage_norms (s : ℝ≥0) (g : Jet3) :
    ‖(g.gaussianAverage s).f‖ ≤ ‖g.f‖ ∧ ‖(g.gaussianAverage s).d1‖ ≤ ‖g.d1‖ ∧
    ‖(g.gaussianAverage s).d2‖ ≤ ‖g.d2‖ ∧ ‖(g.gaussianAverage s).d3‖ ≤ ‖g.d3‖ := by
  have hh (f : ℝ →ᵇ ℝ) : ‖gaussianAverageBCF s f‖ ≤ ‖f‖ := by
    rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
    intro x; exact gaussianAverage_abs_le s f x
  exact ⟨hh _,hh _,hh _,hh _⟩

def Jet3.exp (d : ℝ) (g : Jet3) : Jet3 where
  f := expBCF d g.f
  d1 := d • (expBCF d g.f * g.d1)
  d2 := expBCF d g.f * (d^2 • (g.d1^2) + d • g.d2)
  d3 := expBCF d g.f * (d^3 • (g.d1^3) + (3*d^2) • (g.d1*g.d2) + d • g.d3)
  has1 x := by
    convert! ((g.has1 x).const_mul d).exp using 1
    dsimp [expBCF]
    ring
  has2 x := by
    have he := ((g.has1 x).const_mul d).exp
    have h := (he.mul (g.has2 x)).const_mul d
    convert! h using 1
    dsimp [expBCF]; ring
  has3 x := by
    have he := ((g.has1 x).const_mul d).exp
    have h := he.mul (((g.has2 x).pow 2).const_mul (d^2) |>.add ((g.has3 x).const_mul d))
    convert! h using 1
    dsimp [expBCF]; ring

end SphericalPerceptron
end
end

end OAI
