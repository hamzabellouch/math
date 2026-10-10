import OAI.Analysis.CircleDomains.Sobolev.PairKernelEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! Normalized proximity kernels for two local arclength occupations. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

def ballPairKernel (A : Set X) (a : ℝ≥0) : X × X → ℝ≥0∞ :=
  {p | p.1 ∈ A ∧ p.2 ∈ A ∧ dist p.1 p.2 < 2 * a}.indicator
    (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2)

theorem measurable_ballPairKernel (A : Set X) (hA : MeasurableSet A) (a : ℝ≥0) :
    Measurable (ballPairKernel A a) := by
  apply measurable_const.indicator
  exact (hA.preimage measurable_fst).inter
    ((hA.preimage measurable_snd).inter (measurableSet_lt measurable_dist measurable_const))

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem ballPairKernel_symm (A : Set X) (a : ℝ≥0) (x y : X) :
    ballPairKernel A a (x, y) = ballPairKernel A a (y, x) := by
  classical
  simp only [ballPairKernel, Set.indicator, mem_ofPred_eq, dist_comm y x]
  congr 1
  exact propext and_left_comm

omit [SecondCountableTopology X] in
theorem ballPairKernel_row_bound (σ : Measure X) (A : Set X) (hA : MeasurableSet A)
    {a : ℝ≥0} (ha : a ≠ 0) {C : ℝ≥0∞}
    (hball : ∀ x ∈ A, σ (ball x (2 * a)) ≤ C * (a : ℝ≥0∞) ^ 2) (x : X) :
    (∫⁻ y, ballPairKernel A a (x, y) ∂σ) ≤ C := by
  classical
  by_cases hx : x ∈ A
  · have hid : (fun y => ballPairKernel A a (x, y)) =
        (A ∩ ball x (2 * a)).indicator (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2) := by
      funext y
      simp only [ballPairKernel, Set.indicator_apply, mem_ofPred_eq,
        mem_inter_iff, mem_ball, hx, true_and, dist_comm]
    rw [hid, lintegral_indicator_const (hA.inter measurableSet_ball)]
    calc
      _ ≤ (a : ℝ≥0∞)⁻¹ ^ 2 * (C * (a : ℝ≥0∞) ^ 2) :=
        mul_le_mul' le_rfl ((measure_mono inter_subset_right).trans (hball x hx))
      _ = C := by
        have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
        rw [mul_left_comm, ← mul_pow, ENNReal.inv_mul_cancel ha0 ENNReal.coe_ne_top]
        simp
  · have hz : (fun y => ballPairKernel A a (x, y)) = 0 := by
      funext y
      simp [ballPairKernel, hx]
    rw [hz]
    change (∫⁻ _ : X, (0 : ℝ≥0∞) ∂σ) ≤ C
    simp

theorem localized_ball_pair_energy_bound (σ : Measure X) [SFinite σ]
    (A : Set X) (hA : MeasurableSet A) {a : ℝ≥0} (ha : a ≠ 0)
    (g h : X → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h) {C E : ℝ≥0∞}
    (hball : ∀ x ∈ A, σ (ball x (2 * a)) ≤ C * (a : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in A, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x in A, h x ^ 2 ∂σ) ≤ E) :
    (∫⁻ p, ballPairKernel A a p * (g p.1 * h p.2) ∂σ.prod σ) ≤ C * E := by
  have hind (f : X → ℝ≥0∞) :
      (fun x => (A.indicator f x) ^ 2) = A.indicator (fun x => f x ^ 2) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hb := pair_kernel_energy_bound σ (ballPairKernel A a)
    (measurable_ballPairKernel A hA a) (A.indicator g) (A.indicator h)
    (hg.indicator hA) (hh.indicator hA) (C := C) (E := E)
    (ballPairKernel_row_bound σ A hA ha hball)
    (fun y => by simpa only [ballPairKernel_symm A a] using
      ballPairKernel_row_bound σ A hA ha hball y)
    (by rw [hind, lintegral_indicator hA]; exact hgE)
    (by rw [hind, lintegral_indicator hA]; exact hhE)
  convert hb using 1
  apply lintegral_congr
  intro p
  by_cases hpa : p.1 ∈ A <;> by_cases hpb : p.2 ∈ A <;>
    simp [ballPairKernel, Set.indicator, hpa, hpb]

end CircleDomainRigidity

end

end OAI
