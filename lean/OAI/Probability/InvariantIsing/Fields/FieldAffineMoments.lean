import OAI.Probability.InvariantIsing.Fields.FieldAffineAverageDerivative
import OAI.Probability.InvariantIsing.Fields.FieldShiftMoments

namespace OAI

/-! Polynomial integrability under the actual affine-noise law. These
bounds remain uniform when the spatial bias changes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma field_integrable_of_quadratic_bound (ν : Measure ℝ)
    (hq : Integrable (fun u : ℝ => (1 + |u|) ^ 2) ν)
    {A : ℝ → ℝ} (hA : Measurable A) (C : ℝ)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|) ^ 2) : Integrable A ν := by
  apply (hq.const_mul C).mono' hA.aestronglyMeasurable
  exact ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hB u

lemma field_integral_abs_le_quadratic_bound (ν : Measure ℝ)
    (hq : Integrable (fun u : ℝ => (1 + |u|) ^ 2) ν)
    {A : ℝ → ℝ} (hA : Measurable A) (C : ℝ)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|) ^ 2) :
    |∫ u, A u ∂ν| ≤ C * ∫ u : ℝ, (1 + |u|) ^ 2 ∂ν := by
  have hi := field_integrable_of_quadratic_bound ν hq hA C hB
  calc
    _ ≤ ∫ u, |A u| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, C * (1 + |u|) ^ 2 ∂ν := integral_mono hi.abs (hq.const_mul C) hB
    _ = _ := integral_const_mul _ _

namespace FieldSmoothFamily

variable {I : Set ℝ} (F : FieldSmoothFamily I)

def affineLaw (a v ζ : ℝ) (p : ℝ × ℝ) : Measure ℝ :=
  (gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u)

lemma affineLaw_probability (a v ζ : ℝ) (p : ℝ × ℝ) :
    IsProbabilityMeasure (F.affineLaw a v ζ p) := by
  apply isProbabilityMeasure_tilted
  exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
    (F.mU.comp (by fun_prop)) ((F.growth p.1).add_left p.2 |>.scale_argument
      (Real.sqrt (a + v * p.1))) ζ

lemma affineLaw_quadratic_moment (a v ζ : ℝ) (p : ℝ × ℝ) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2) (F.affineLaw a v ζ p) ∧
      (∫ u : ℝ, (1 + |u|) ^ 2 ∂F.affineLaw a v ζ p) ≤
        fieldGaussianMomentCap (|ζ| * F.KX * Real.sqrt (a + v * p.1)) := by
  simpa only [affineLaw, affineShift, abs_of_nonneg (Real.sqrt_nonneg _)] using
    F.shifted_second_moment p.1 p.2 (Real.sqrt (a + v * p.1)) ζ
      (Real.sqrt (a + v * p.1)) (by rw [abs_of_nonneg (Real.sqrt_nonneg _)])

def affineMomentCap (ζ V : ℝ) : ℝ :=
  1 + |fieldGaussianMomentCap (|ζ| * F.KX * Real.sqrt V)|

lemma affineMomentCap_pos (ζ V : ℝ) : 0 < F.affineMomentCap ζ V := by
  unfold affineMomentCap
  positivity

lemma affineLaw_moment_le (a v ζ : ℝ) (p : ℝ × ℝ) {V : ℝ}
    (hV : a + v * p.1 ≤ V) :
    (∫ u : ℝ, (1 + |u|) ^ 2 ∂F.affineLaw a v ζ p) ≤ F.affineMomentCap ζ V := by
  have h := F.shifted_second_moment p.1 p.2 (Real.sqrt (a + v * p.1)) ζ
    (Real.sqrt V) (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt hV)
  exact h.2.trans ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))

lemma affineLaw_integral_bound (a v ζ : ℝ) (p : ℝ × ℝ) {V : ℝ}
    (hV : a + v * p.1 ≤ V) {A : ℝ → ℝ} (hA : Measurable A)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ u, |A u| ≤ C * (1 + |u|) ^ 2) :
    |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C * F.affineMomentCap ζ V :=
  (field_integral_abs_le_quadratic_bound _ (F.affineLaw_quadratic_moment a v ζ p).1
    hA C hB).trans (mul_le_mul_of_nonneg_left (F.affineLaw_moment_le a v ζ p hV) hC)

lemma affineLaw_linear_integrable (a v ζ : ℝ) (p : ℝ × ℝ)
    {A : ℝ → ℝ} (hA : Measurable A) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|)) : Integrable A (F.affineLaw a v ζ p) := by
  apply field_integrable_of_quadratic_bound _ (F.affineLaw_quadratic_moment a v ζ p).1 hA C
  intro u
  exact (hB u).trans (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hC)

lemma affineLaw_bounded_integrable (a v ζ : ℝ) (p : ℝ × ℝ)
    {A : ℝ → ℝ} (hA : Measurable A) (C : ℝ) (hB : ∀ u, |A u| ≤ C) :
    Integrable A (F.affineLaw a v ζ p) := by
  have := F.affineLaw_probability a v ζ p
  exact Integrable.of_bound hA.aestronglyMeasurable C
    (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hB u)

end FieldSmoothFamily
end InvariantIsing

end

end OAI
