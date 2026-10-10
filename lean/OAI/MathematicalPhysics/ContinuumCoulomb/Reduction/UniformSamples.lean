import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformQuadrature

namespace OAI

/-! Left-endpoint quadrature with a finite sequence of computed samples. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

def sampleSum (h : ℝ) (N : ℕ) (v : ℕ → ℝ) : ℝ :=
  h * ∑ i ∈ Finset.range N, v i

theorem samples_error (f : ℝ → ℝ) (v : ℕ → ℝ) (a h : ℝ) (N : ℕ) {L ε : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hf : Continuous f)
    (hLip : ∀ x ∈ Set.Icc a (node a h N), ∀ y ∈ Set.Icc a (node a h N),
      |f x - f y| ≤ L * |x - y|)
    (heval : ∀ i < N, |v i - f (node a h i)| ≤ ε) :
    |sampleSum h N v - ∫ x in a..node a h N, f x| ≤
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
  have heq : sampleSum h N v - (∫ x in a..node a h N, f x) =
      ∑ i ∈ Finset.range N, (h * v i -
        ∫ x in node a h i..node a h (i + 1), f x) := by
    rw [Finset.sum_sub_distrib, ht, sampleSum, Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |h * v i -
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
