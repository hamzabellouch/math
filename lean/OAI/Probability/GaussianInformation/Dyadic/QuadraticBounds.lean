import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.ScoreBounds

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma l2bound_of_bounded_tests {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) {L : ℝ≥0∞}
    (hL : L ≠ ∞)
    (htest : ∀ h : α → ℝ, Measurable h → eLpNorm h 2 μ ≤ 1 →
      (∫⁻ x,ENNReal.ofReal |h x| *ENNReal.ofReal (p x) ∂μ) ≤ L) :
    (∫ x,(p x)^2 ∂μ) ≤ L.toReal^2 := by
  let S := ∫ x,(p x)^2 ∂μ
  have hS : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  by_cases hSz : S = 0
  · change S ≤ L.toReal^2
    rw [hSz]
    exact sq_nonneg _
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSp
  let h := fun x => p x/Real.sqrt S
  have hh : Measurable h := hp.div_const _
  have hh0 : ∀ x,0 ≤ h x := fun x => div_nonneg (hp0 x) hs.le
  have hhb : ∀ x,|h x| ≤ 1/Real.sqrt S := fun x => by
    rw [abs_of_nonneg (hh0 x)]
    exact div_le_div_of_nonneg_right (hp1 x) hs.le
  have hsqi : (∫ x,(h x)^2 ∂μ) = 1 := by
    simp_rw [h,div_pow]
    rw [integral_div,Real.sq_sqrt hS]
    exact div_self hSz
  have hnorm : eLpNorm h 2 μ ≤ 1 := by
    rw [eLpNorm_eq_sqrt_integral_sq μ h hh hhb,hsqi]
    simp
  have htest' := htest h hh hnorm
  have hiprod : Integrable (fun x => |h x| *p x) μ := by
    apply integrable_bounded_measurable μ _ (hh.abs.mul hp) (C := 1/Real.sqrt S)
    intro x
    change abs (|h x| * p x) ≤ 1/Real.sqrt S
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (hp0 x))]
    exact (mul_le_mul_of_nonneg_left (hp1 x) (abs_nonneg _)).trans (by simpa using hhb x)
  have hint : (∫ x,|h x| *p x ∂μ) = Real.sqrt S := by
    simp_rw [abs_of_nonneg (hh0 _)]
    have he : (fun x => h x*p x) = fun x => (p x)^2/Real.sqrt S := by funext x; dsimp [h]; ring
    rw [he,integral_div]
    change S/Real.sqrt S = Real.sqrt S
    rw [div_eq_iff hs.ne']
    simpa [pow_two] using (Real.sq_sqrt hS).symm
  have he : (∫⁻ x,ENNReal.ofReal |h x| *ENNReal.ofReal (p x) ∂μ) = ENNReal.ofReal (Real.sqrt S) := by
    simp_rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hiprod (ae_of_all _ (fun x => mul_nonneg (abs_nonneg _) (hp0 x))),hint]
  rw [he] at htest'
  have hreal := ENNReal.toReal_mono hL htest'
  rw [ENNReal.toReal_ofReal hs.le] at hreal
  have hsq : (Real.sqrt S)^2 ≤ L.toReal^2 := pow_le_pow_left₀ hs.le hreal 2
  rwa [Real.sq_sqrt hS] at hsq

end RepeatedLocalization

end OAI
