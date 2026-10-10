import Mathlib
import OAI.Probability.SKRatio.Dynamics.StepMass

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

lemma measurable_stepMass (p : ℕ → ℝ) : Measurable (stepMass p) := by
  unfold stepMass
  exact Measurable.tsum (fun _ => measurable_const.indicator measurableSet_Ico)

lemma stepMass_abs_le {a : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (ha : ∀ j, |a j| ≤ B)
    (x : ℝ) : |stepMass a x| ≤ B := by
  by_cases hx : 0 ≤ x
  · rw [stepMass_of_nonneg _ hx]
    exact ha _
  · rw [stepMass_of_neg _ (lt_of_not_ge hx),abs_zero]
    exact hB

lemma stepMass_mul (p a : ℕ → ℝ) (x : ℝ) :
    stepMass p x*stepMass a x=stepMass (fun j => p j*a j) x := by
  by_cases hx : 0 ≤ x
  · simp only [stepMass_of_nonneg _ hx]
  · simp only [stepMass_of_neg _ (lt_of_not_ge hx),mul_zero]

lemma summable_mul_bounded {p a : ℕ → ℝ} {B : ℝ} (hp : Summable p)
    (ha : ∀ j, |a j| ≤ B) : Summable (fun j => p j*a j) := by
  apply Summable.of_norm_bounded (hp.abs.mul_right B)
  intro j
  simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_left (ha j) (abs_nonneg (p j))

lemma integral_histogram_summable {p : ℕ → ℝ} (hp : Summable p) (q : ℝ) {n : ℕ}
    (hn : 0 < n) : ∫ x : ℝ, histogram q n p x = ∑' j, p j := by
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  unfold histogram
  rw [integral_const_mul]
  have hh : (fun x : ℝ => stepMass p (q*n+x*Real.sqrt n)) =
      (fun x : ℝ => (fun t => stepMass p (t+q*n)) (Real.sqrt n*x)) := by
    ext x
    congr 1
    ring
  rw [hh,Measure.integral_comp_mul_left (fun t : ℝ => stepMass p (t+q*n))
    (Real.sqrt (n:ℝ)),integral_add_right_eq_self,integral_stepMass hp,smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),← mul_assoc,mul_inv_cancel₀ hs,one_mul]

noncomputable def testHistogram (q : ℝ) (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  stepMass a (q*n+x*Real.sqrt n)

lemma measurable_testHistogram (q : ℝ) (n : ℕ) (a : ℕ → ℝ) :
    Measurable (testHistogram q n a) := by
  apply (measurable_stepMass a).comp
  fun_prop

lemma testHistogram_bound {a : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (ha : ∀ j, |a j| ≤ B)
    (q : ℝ) (n : ℕ) (x : ℝ) : |testHistogram q n a x| ≤ B :=
  stepMass_abs_le hB ha _

lemma integral_histogram_test {p a : ℕ → ℝ} {B : ℝ} (hp : Summable p)
    (ha : ∀ j, |a j| ≤ B) (q : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, histogram q n p x*testHistogram q n a x) = ∑' j, p j*a j := by
  have he (x : ℝ) : histogram q n p x*testHistogram q n a x =
      histogram q n (fun j => p j*a j) x := by
    unfold histogram testHistogram
    rw [mul_assoc,stepMass_mul]
  simp_rw [he]
  exact integral_histogram_summable (summable_mul_bounded hp ha) q hn

end SKRatioClock.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
