import OAI.Analysis.IrrationalRotation.Rotation.FloorCocycle

namespace OAI

namespace Invariant233.FloorCocycle

theorem finite_exp_cocycle {ι : Type*} (s : Finset ι) (c u α : ι → ℝ)
    (v n : ℝ) :
    Real.exp (-(∑ i ∈ s, c i * (⌊u i + (v + n) * α i⌋ : ℝ))) =
      Real.exp (-(∑ i ∈ s, c i * (⌊u i + v * α i⌋ : ℝ))) *
        Real.exp (-(∑ i ∈ s, c i * (⌊Int.fract (u i + v * α i) + n * α i⌋ : ℝ))) := by
  rw [← Real.exp_add, ← neg_add, ← Finset.sum_add_distrib]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h := floor_fract_add (u i + v * α i) (n * α i)
  have heq : u i + (v + n) * α i = (u i + v * α i) + n * α i := by ring
  rw [heq, ← h]
  push_cast
  ring

theorem finite_exp_antitone {ι : Type*} (s : Finset ι) (c u α : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hα : ∀ i ∈ s, 0 ≤ α i) :
    Antitone (fun v : ℝ => Real.exp (-(∑ i ∈ s, c i * (⌊u i + v * α i⌋ : ℝ)))) := by
  intro v w hvw
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hc i hi)
  have hadd : u i + v * α i ≤ u i + w * α i := by
    linarith [mul_le_mul_of_nonneg_right hvw (hα i hi)]
  exact_mod_cast Int.floor_mono hadd

theorem finite_exp_zero {ι : Type*} (s : Finset ι) (c u α : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i < 1) :
    Real.exp (-(∑ i ∈ s, c i * (⌊u i + (0 : ℝ) * α i⌋ : ℝ))) = 1 := by
  have hf : ∀ i ∈ s, ⌊u i⌋ = 0 := by
    intro i hi
    exact Int.floor_eq_zero_iff.mpr (hu i hi)
  simp only [zero_mul, add_zero]
  have hs : (∑ i ∈ s, c i * (⌊u i⌋ : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hf i hi]
    simp
  rw [hs]
  simp

end Invariant233.FloorCocycle

end OAI
