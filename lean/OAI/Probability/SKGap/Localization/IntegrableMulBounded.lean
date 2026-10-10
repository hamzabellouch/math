import Mathlib
import OAI.Probability.SKGap.Localization.StepMass

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
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
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
namespace SKGapCutoff.Clock

lemma integrable_mul_bounded {f u : ℝ → ℝ} {B : ℝ} (hf : Integrable f)
    (hu : AEStronglyMeasurable u) (hb : ∀ x, |u x| ≤ B) : Integrable (fun x => f x*u x) := by
  apply (hf.abs.mul_const B).mono' (hf.aestronglyMeasurable.mul hu)
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,Pi.mul_apply,abs_mul] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x)))

lemma pairing_abs_le {f u : ℝ → ℝ} {B : ℝ} (hf : Integrable f)
    (hu : AEStronglyMeasurable u) (hb : ∀ x, |u x| ≤ B) :
    |∫ x : ℝ, f x*u x| ≤ B*(∫ x : ℝ, |f x|) := by
  calc
    _ ≤ ∫ x : ℝ, |f x*u x| := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, |f x| * B := integral_mono (integrable_mul_bounded hf hu hb).abs
      (hf.abs.mul_const B) (fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _))
    _ = _ := by rw [integral_mul_const]; ring

lemma pairing_sub_abs_le {f g u : ℝ → ℝ} {B : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hu : AEStronglyMeasurable u)
    (hb : ∀ x, |u x| ≤ B) :
    |(∫ x : ℝ, f x*u x)-(∫ x : ℝ, g x*u x)| ≤ B*(∫ x : ℝ, |f x-g x|) := by
  rw [← integral_sub (integrable_mul_bounded hf hu hb) (integrable_mul_bounded hg hu hb)]
  simpa only [Pi.sub_apply,sub_mul] using pairing_abs_le (hf.sub hg) hu hb

lemma pairing_of_L1_limit {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℕ → ℝ → ℝ} {B : ℝ}
    (hf : ∀ᶠ n in atTop, Integrable (f n)) (hg : Integrable g)
    (hu : ∀ n, AEStronglyMeasurable (u n)) (hb : ∀ n x, |u n x| ≤ B)
    (ht : Tendsto (fun n => ∫ x : ℝ, |f n x-g x|) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ x : ℝ, f n x*u n x)-(∫ x : ℝ, g x*u n x)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using ht.const_mul B)
  filter_upwards [hf] with n hn
  simpa only [Real.norm_eq_abs] using pairing_sub_abs_le hn hg (hu n) (hb n)

theorem pairing_of_finite_approximation {ρ : ℝ → ℝ} {φ : ℝ → ℝ → ℝ}
    {u : ℕ → ℝ → ℝ} {B : ℝ}
    (hρ : Integrable ρ) (hφ : ∀ y, Integrable (φ y)) (hB : 0 < B)
    (hu : ∀ n, AEStronglyMeasurable (u n)) (hb : ∀ n x, |u n x| ≤ B)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℝ) (c : ℝ → ℝ),
      (∫ x : ℝ, |ρ x-∑ y ∈ s, c y*φ y x|) < ε)
    (ht : ∀ y, Tendsto (fun n => ∫ x : ℝ, φ y x*u n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ, ρ x*u n x) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨s,c,happrox⟩ := ha (ε/(2*B)) (by positivity)
  let F : ℝ → ℝ := fun x => ∑ y ∈ s, c y*φ y x
  have hF : Integrable F := integrable_finsetSum s (fun y _ => (hφ y).const_mul (c y))
  have hsum (n : ℕ) : (∫ x : ℝ, F x*u n x) = ∑ y ∈ s, c y*(∫ x : ℝ, φ y x*u n x) := by
    unfold F
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [integral_finsetSum s (fun y _ => (integrable_mul_bounded (hφ y) (hu n) (hb n)).const_mul (c y))]
    apply Finset.sum_congr rfl
    intro y _
    simp only [integral_const_mul]
  have hconv : Tendsto (fun n => ∫ x : ℝ, F x*u n x) atTop (𝓝 0) := by
    simp_rw [hsum]
    have hh := tendsto_finsetSum s (fun y _ => (ht y).const_mul (c y))
    simpa using hh
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hconv (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hclose := pairing_sub_abs_le hρ hF (hu n) (hb n)
  have hh := hN n hn
  simp only [Real.dist_eq,sub_zero] at hh ⊢
  have he : B*(∫ x : ℝ, |ρ x-F x|) < ε/2 := by
    have := mul_lt_mul_of_pos_left happrox hB
    have he : B*(ε/(2*B))=ε/2 := by field_simp
    rwa [he] at this
  have htri : |∫ x : ℝ, ρ x*u n x| ≤
      |(∫ x : ℝ, ρ x*u n x)-(∫ x : ℝ, F x*u n x)|+|∫ x : ℝ, F x*u n x| := by
    simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add
      (∫ x : ℝ, ρ x*u n x) (∫ x : ℝ, F x*u n x)
  linarith

end SKGapCutoff.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SKGapCutoff.Clock

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

end SKGapCutoff.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end

end OAI
