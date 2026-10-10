import Mathlib
import OAI.Probability.SKGap.Terminal.GibbsLExpectation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKGapCutoff

noncomputable def gibbsEventProbability {n : ℕ}
    (E : Spin n → Set (GaussianCoordinates n)) : GaussianCoordinates n → ℝ≥0∞ :=
  gibbsLExpectation (fun g x => (E x).indicator (fun _ => 1) g)

lemma measurable_gibbsEventProbability {n : ℕ} (E : Spin n → Set (GaussianCoordinates n))
    (hE : ∀ x, MeasurableSet (E x)) : Measurable (gibbsEventProbability E) :=
  measurable_gibbsLExpectation _ (fun x => measurable_const.indicator (hE x))

lemma planted_gibbsEventProbability_bound (β : ℝ) {n : ℕ} (hn : 0 < n)
    (E : Spin n → Set (GaussianCoordinates n)) (hE : ∀ x, MeasurableSet (E x))
    (a : ℝ≥0∞) (ha : ∀ x, singleSpinPlantedLaw β x (E x) ≤ a) :
    (∫⁻ g, gibbsEventProbability E g ∂plantedDisorderLaw β n) ≤ a := by
  rw [gibbsEventProbability, planted_gibbs_lintegral β hn _
    (fun x => measurable_const.indicator (hE x))]
  have hI (x : Spin n) :
      (∫⁻ g, (E x).indicator (fun _ => (1:ℝ≥0∞)) g ∂singleSpinPlantedLaw β x) =
        singleSpinPlantedLaw β x (E x) := lintegral_indicator_one (hE x)
  simp_rw [hI]
  calc
    _ ≤ ENNReal.ofReal (((2:ℝ)^n)⁻¹) * ∑ _x : Spin n, a :=
      mul_le_mul' le_rfl (Finset.sum_le_sum (fun x _ => ha x))
    _ = a := by
      simp only [Finset.sum_const, Finset.card_univ, card_spin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc]
      have he : ENNReal.ofReal (((2:ℝ)^n)⁻¹) * (2:ℝ≥0∞)^n = 1 := by
        have hpow : ENNReal.ofReal ((2:ℝ)^n) = (2:ℝ≥0∞)^n := by
          rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
        rw [← hpow, ← ENNReal.ofReal_mul (by positivity)]
        simp
      rw [he, one_mul]

lemma quenched_gibbs_events_exponential (β : ℝ) (hβ : β^2 < 1)
    (c : ℝ) (hc : 0 < c) (E : (n : ℕ) → Spin n → Set (GaussianCoordinates n))
    (hE : ∀ n x, MeasurableSet (E n x))
    (hsmall : ∀ᶠ n : ℕ in atTop, ∀ x : Spin n,
      singleSpinPlantedLaw β x (E n x) ≤ ENNReal.ofReal (Real.exp (-c*n))) :
    Tendsto (fun n => disorderLaw β n {g |
      ENNReal.ofReal (Real.exp (-(c/2)*n)) ≤ gibbsEventProbability (E n) g})
      atTop (nhds 0) := by
  apply quenched_exponential_transfer β hβ c hc (fun n => gibbsEventProbability (E n))
    (fun n => measurable_gibbsEventProbability (E n) (hE n))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hs hn
  exact planted_gibbsEventProbability_bound β hn (E n) (hE n) _ hs

end SKGapCutoff

end

end OAI
