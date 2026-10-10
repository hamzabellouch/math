import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformSamples

namespace OAI

/-! The quadrature estimate only needs a modulus on the integration
interval. This is the form used after cutting off the singular time zero. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

theorem continuousOn_of_abs_sub_le {f : ℝ → ℝ} {s : Set ℝ} {L : ℝ}
    (hLip : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ L * |x - y|) : ContinuousOn f s := by
  have h := LipschitzOnWith.of_dist_le' (K := L) (f := f) (s := s) (by
    intro x hx y hy
    simpa only [Real.dist_eq] using hLip x hx y hy)
  exact h.continuousOn

theorem samples_error_lipschitz (f : ℝ → ℝ) (v : ℕ → ℝ)
    (a h : ℝ) (N : ℕ) {L ε : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc a (node a h N), ∀ y ∈ Set.Icc a (node a h N),
      |f x - f y| ≤ L * |x - y|)
    (heval : ∀ i < N, |v i - f (node a h i)| ≤ ε) :
    |sampleSum h N v - ∫ x in a..node a h N, f x| ≤
      (N : ℝ) * (L * h ^ 2 + h * ε) := by
  have hc := continuousOn_of_abs_sub_le hLip
  have hnode (i j : ℕ) (hij : i ≤ j) : node a h i ≤ node a h j := by
    dsimp only [node]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh) a
  have hstep (i : ℕ) : node a h (i + 1) = node a h i + h := by
    simp only [node, Nat.cast_add, Nat.cast_one]
    ring
  have hzero : node a h 0 = a := by simp [node]
  have hcell (i : ℕ) (hi : i < N) :
      Set.Icc (node a h i) (node a h (i + 1)) ⊆ Set.Icc a (node a h N) := by
    intro x hx
    have hi0 : a ≤ node a h i := by simpa only [hzero] using hnode 0 i (Nat.zero_le i)
    exact ⟨hi0.trans hx.1, hx.2.trans (hnode (i + 1) N hi)⟩
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := node a h) (n := N) (f := f) (by
      intro i hi
      exact (hc.mono (hcell i hi)).intervalIntegrable_of_Icc (hnode i (i + 1) (Nat.le_succ i)))
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
      have hci := hc.mono (hcell i hiN)
      rw [hstep] at hci ⊢
      apply cell_sample_error f _ hh hL hci _ (heval i hiN)
      intro x hx
      have hx' : x ∈ Set.Icc a (node a h N) := by
        apply hcell i hiN
        simpa only [hstep] using hx
      have hi' : node a h i ∈ Set.Icc a (node a h N) :=
        ⟨by simpa only [hzero] using hnode 0 i (Nat.zero_le i), hnode i N hiN.le⟩
      exact hLip x hx' (node a h i) hi'
    _ = _ := by simp; ring

theorem integral_parameter_lipschitz (f : ℝ → ℝ → ℝ) {a b c d L : ℝ}
    (hcd : c ≤ d)
    (hf : ∀ x ∈ Set.Icc a b, ContinuousOn (f x) (Set.Icc c d))
    (hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc c d,
      |f x z - f y z| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |(∫ z in c..d, f x z) - ∫ z in c..d, f y z| ≤ (d - c) * L * |x - y| := by
  rw [← intervalIntegral.integral_sub
    ((hf x hx).intervalIntegrable_of_Icc hcd) ((hf y hy).intervalIntegrable_of_Icc hcd)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun z => f x z - f y z) (a := c) (b := d) (C := L * |x - y|) (by
      intro z hz
      have hz' : z ∈ Set.Icc c d := by
        have hz'' : z ∈ Set.Ioc c d := by simpa only [Set.uIoc_of_le hcd] using hz
        exact ⟨hz''.1.le, hz''.2⟩
      simpa only [Real.norm_eq_abs] using hLip x hx y hy z hz')
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcd), mul_assoc, mul_comm,
    mul_left_comm] using h

end ContinuumCoulomb.UniformQuadrature

end

end OAI
