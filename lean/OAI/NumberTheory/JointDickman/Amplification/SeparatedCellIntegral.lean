import OAI.NumberTheory.JointDickman.Analysis.MellinRestrictionEnergy
import Mathlib.MeasureTheory.Integral.Average

namespace OAI

/-! # Recovering an integral from separated samples in unit-sized cells -/
namespace JointDickman
open Finset MeasureTheory
open scoped Classical

lemma unit_measure_integral_sample {E : Set ℝ} (F : ℝ → ℝ)
    (hF : IntegrableOn F E) (hF0 : ∀ x ∈ E, 0 ≤ F x)
    (hE : volume E ≠ 0) (hEf : volume E ≠ ⊤) (hE1 : volume.real E ≤ 1) :
    ∃ x ∈ E, (∫ t in E, F t) ≤ F x := by
  obtain ⟨x,hx,havg⟩ := exists_setAverage_le hE hEf hF
  have hr : 0 < volume.real E := ENNReal.toReal_pos hE hEf
  rw [setAverage_eq,smul_eq_mul,← div_eq_inv_mul] at havg
  exact ⟨x,hx,((div_le_iff₀ hr).mp havg).trans
    (mul_le_of_le_one_right (hF0 x hx) hE1)⟩

/-- Each cell has measure at most one and cells in the family are separated.
The sample bound is therefore also a bound for the sum of their integrals. -/
theorem separated_cell_integral_bound (I : Finset ℕ) (E : ℕ → Set ℝ)
    (S : Set ℝ) (F : ℝ → ℝ) (B : ℝ)
    (hF : ∀ i ∈ I, IntegrableOn F (E i)) (hF0 : ∀ x ∈ S, 0 ≤ F x)
    (hES : ∀ i ∈ I, E i ⊆ S)
    (hEf : ∀ i ∈ I, volume (E i) ≠ ⊤)
    (hE1 : ∀ i ∈ I, volume.real (E i) ≤ 1)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ x ∈ E i, ∀ y ∈ E j, 1 ≤ |x-y|)
    (hsample : ∀ U : Finset ℝ, (∀ x ∈ U, x ∈ S) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (∑ x ∈ U, F x) ≤ B) :
    (∑ i ∈ I, ∫ t in E i, F t) ≤ B := by
  let J := I.filter (fun i => volume (E i) ≠ 0)
  have hex : ∀ i ∈ J, ∃ x ∈ E i, (∫ t in E i, F t) ≤ F x := by
    intro i hi
    obtain ⟨hi,hz⟩ := mem_filter.mp hi
    exact unit_measure_integral_sample F (hF i hi) (fun x hx => hF0 x (hES i hi hx))
      hz (hEf i hi) (hE1 i hi)
  let pick : ℕ → ℝ := fun i => if hi : i ∈ J then (hex i hi).choose else 0
  have hpick : ∀ i ∈ J, pick i ∈ E i ∧ (∫ t in E i, F t) ≤ F (pick i) := by
    intro i hi
    dsimp only [pick]
    rw [dite_eq_left hi]
    exact (hex i hi).choose_spec
  have hinj : Set.InjOn pick J := by
    intro i hi j hj hij
    by_contra hne
    have hh := hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne
      (pick i) (hpick i hi).1 (pick j) (hpick j hj).1
    rw [hij,sub_self,abs_zero] at hh
    norm_num at hh
  have hsum : (∑ i ∈ I, ∫ t in E i, F t) = ∑ i ∈ J, ∫ t in E i, F t := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hij
    have hz : volume (E i) = 0 := by
      by_contra hz
      exact hij (mem_filter.mpr ⟨hi,hz⟩)
    rw [Measure.restrict_eq_zero.mpr hz]
    simp
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ J, F (pick i) := sum_le_sum (fun i hi => (hpick i hi).2)
    _ = ∑ x ∈ J.image pick, F x := (sum_image hinj).symm
    _ ≤ B := hsample _ (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact hES i (mem_filter.mp hi).1 (hpick i hi).1) (by
      intro x hx y hy hxy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
      exact hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1
        (fun hij => hxy (congrArg pick hij)) (pick i) (hpick i hi).1 (pick j) (hpick j hj).1)

end JointDickman

end OAI
