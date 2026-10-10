import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace OAI

/-! A quantitative left-endpoint quadrature bound, including errors in the
sample values. It will be applied successively to the fixed-dimensional
truncated heat integral. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

def node (a h : ℝ) (i : ℕ) : ℝ := a + (i : ℝ) * h

def sum (a h : ℝ) (N : ℕ) (evaluate : ℝ → ℝ) : ℝ :=
  h * ∑ i ∈ Finset.range N, evaluate (node a h i)

theorem cell_error (f : ℝ → ℝ) {a h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hf : ContinuousOn f (Set.Icc a (a + h)))
    (hLip : ∀ x ∈ Set.Icc a (a + h), |f x - f a| ≤ L * |x - a|) :
    |h * f a - ∫ x in a..a + h, f x| ≤ L * h ^ 2 := by
  have hab : a ≤ a + h := by linarith
  have hfi : IntervalIntegrable f volume a (a + h) :=
    ContinuousOn.intervalIntegrable_of_Icc hab hf
  have heq : h * f a - (∫ x in a..a + h, f x) =
      ∫ x in a..a + h, (f a - f x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi,
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_eq_mul]
  rw [heq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => f a - f x) (a := a) (b := a + h) (C := L * h) (by
      intro x hx
      have hx' : x ∈ Set.Icc a (a + h) := by
        have hx'' : x ∈ Set.Ioc a (a + h) := by
          simpa only [Set.uIoc_of_le hab] using hx
        exact ⟨hx''.1.le, hx''.2⟩
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact (hLip x hx').trans (mul_le_mul_of_nonneg_left
        (by rw [abs_of_nonneg (sub_nonneg.mpr hx'.1)]; linarith [hx'.2]) hL))
  simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh, pow_two,
    mul_assoc] using hi

theorem cell_sample_error (f : ℝ → ℝ) (v : ℝ) {a h L ε : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hf : ContinuousOn f (Set.Icc a (a + h)))
    (hLip : ∀ x ∈ Set.Icc a (a + h), |f x - f a| ≤ L * |x - a|)
    (hv : |v - f a| ≤ ε) :
    |h * v - ∫ x in a..a + h, f x| ≤ L * h ^ 2 + h * ε := by
  have heq : h * v - (∫ x in a..a + h, f x) =
      h * (v - f a) + (h * f a - ∫ x in a..a + h, f x) := by ring
  rw [heq]
  calc
    _ ≤ |h * (v - f a)| + |h * f a - ∫ x in a..a + h, f x| := abs_add_le _ _
    _ ≤ h * ε + L * h ^ 2 := add_le_add
      (by rw [abs_mul, abs_of_nonneg hh]; exact mul_le_mul_of_nonneg_left hv hh)
      (cell_error f hh hL hf hLip)
    _ = _ := by ring

theorem error (f evaluate : ℝ → ℝ) (a h : ℝ) (N : ℕ) {L ε : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hf : Continuous f)
    (hLip : ∀ x ∈ Set.Icc a (node a h N), ∀ y ∈ Set.Icc a (node a h N),
      |f x - f y| ≤ L * |x - y|)
    (heval : ∀ i < N, |evaluate (node a h i) - f (node a h i)| ≤ ε) :
    |sum a h N evaluate - ∫ x in a..node a h N, f x| ≤
      (N : ℝ) * (L * h ^ 2 + h * ε) := by
  have hnode (i j : ℕ) (hij : i ≤ j) : node a h i ≤ node a h j := by
    dsimp only [node]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh) a
  have hstep (i : ℕ) : node a h (i + 1) = node a h i + h := by
    simp only [node, Nat.cast_add, Nat.cast_one]
    ring
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := node a h) (n := N) (f := f) (fun i _ => hf.intervalIntegrable _ _)
  have hzero : node a h 0 = a := by simp [node]
  rw [hzero] at ht
  have heq : sum a h N evaluate - (∫ x in a..node a h N, f x) =
      ∑ i ∈ Finset.range N, (h * evaluate (node a h i) -
        ∫ x in node a h i..node a h (i + 1), f x) := by
    rw [Finset.sum_sub_distrib, ht, sum, Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |h * evaluate (node a h i) -
        ∫ x in node a h i..node a h (i + 1), f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, (L * h ^ 2 + h * ε) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.mp hi
      rw [hstep]
      apply cell_sample_error f _ hh hL hf.continuousOn _ (heval i hiN)
      intro x hx
      have hx' : x ∈ Set.Icc a (node a h N) := by
        refine ⟨?_, ?_⟩
        · have hi0 : a ≤ node a h i := by simpa only [hzero] using hnode 0 i (Nat.zero_le i)
          exact hi0.trans hx.1
        · exact hx.2.trans (by rw [← hstep]; exact hnode (i + 1) N hiN)
      have hi' : node a h i ∈ Set.Icc a (node a h N) :=
        ⟨by simpa only [hzero] using hnode 0 i (Nat.zero_le i), hnode i N hiN.le⟩
      exact hLip x hx' (node a h i) hi'
    _ = _ := by simp; ring

end ContinuumCoulomb.UniformQuadrature

end

end OAI
