import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BlockStein

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def weightedBlockAtom (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (t : Fin (blockDimension D N k+1)) : ℝ :=
  ∑ b : Fin (k+1), if blockLevel D N k b=t then w b else 0

def weightedBlockMass (D N k : ℕ) (w : Fin (k+1) → ℝ) :
    Fin (blockDimension D N k) → ℝ :=
  massFromAtoms (blockDimension D N k) (weightedBlockAtom D N k w)

theorem weightedBlockAtom_nonneg (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (t : Fin (blockDimension D N k+1)) :
    0  ≤  weightedBlockAtom D N k w t := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact hw b
  · exact le_rfl

theorem weightedBlockAtom_sum (D N k : ℕ) (w : Fin (k+1) → ℝ) :
    ∑ t, weightedBlockAtom D N k w t=∑ b, w b := by
  unfold weightedBlockAtom
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem weightedBlockMass_valid (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    (∀ i, weightedBlockMass D N k w i∈Icc (0:ℝ) 1) ∧ Monotone (weightedBlockMass D N k w) := by
  refine ⟨fun i => ⟨massFromAtoms_nonneg _ _ (weightedBlockAtom_nonneg D N k w hw) i,?_⟩,
    massFromAtoms_monotone _ _ (weightedBlockAtom_nonneg D N k w hw)⟩
  exact (massFromAtoms_le_sum _ _ (weightedBlockAtom_nonneg D N k w hw) i).trans_eq
    ((weightedBlockAtom_sum D N k w).trans hs)

theorem hierarchyAtom_weightedBlockMass (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hs : ∑ b, w b=1) (t : Fin (blockDimension D N k+1)) :
    hierarchyAtom (blockDimension D N k) (weightedBlockMass D N k w) 1 t=
      weightedBlockAtom D N k w t := by
  rw [← hs,← weightedBlockAtom_sum D N k w]
  exact hierarchyAtom_massFromAtoms _ _ t

theorem weightedBlockAtom_sum_mul (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (f : Fin (blockDimension D N k+1) → ℝ) :
    (∑ j, weightedBlockAtom D N k w j*f j)=∑ b, w b*f (blockLevel D N k b) := by
  simp only [weightedBlockAtom,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem weightedBlockAtom_ne_zero (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (j : Fin (blockDimension D N k+1)) (hj : weightedBlockAtom D N k w j≠0) :
    ∃ b, blockLevel D N k b=j := by
  by_contra h
  push Not at h
  exact hj (by simp only [weightedBlockAtom,h,ite_false,Finset.sum_const_zero])

theorem weightedBlockAtom_at (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hN : 0<N) (b : Fin (k+1)) :
    weightedBlockAtom D N k w (blockLevel D N k b)=w b := by
  unfold weightedBlockAtom
  simp only [(blockLevel_injective D N k hN).eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem weightedBlockMass_eq_sum (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (i : Fin (blockDimension D N k)) :
    weightedBlockMass D N k w i=∑ b : Fin (k+1),
      if (blockLevel D N k b).val ≤ i.val then w b else 0 := by
  unfold weightedBlockMass massFromAtoms weightedBlockAtom
  calc
    _ = ∑ t : Fin (blockDimension D N k+1), ∑ b : Fin (k+1),
      if blockLevel D N k b=t then (if t.val ≤ i.val then w b else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val ≤ i.val <;> simp only [ht,ite_true,ite_false,ite_self,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem weightedBlockMass_at_disorder (D N k : ℕ) (w : Fin (k+1) → ℝ) (i : Fin D) :
    weightedBlockMass D N k w (Fin.castAdd ((k+1)*N) i)=0 := by
  rw [weightedBlockMass_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  simp only [blockLevel_val,Fin.val_castAdd]
  omega

theorem weightedBlockMass_at_field (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (b : Fin (k+1)) (i : Fin N) :
    weightedBlockMass D N k w (fieldIndex D N k b i)=∑ l, if l<b then w l else 0 := by
  rw [weightedBlockMass_eq_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hh : (blockLevel D N k l).val ≤ (fieldIndex D N k b i).val ↔ l<b := by
    simp only [blockLevel_val,fieldIndex_val,Fin.lt_def]
    constructor
    · intro h
      by_contra hn
      have hl : b.val ≤ l.val := by omega
      have hl' := Nat.mul_le_mul_right N hl
      nlinarith [i.isLt]
    · intro h
      have hl := Nat.mul_le_mul_right N h
      nlinarith
  simp only [hh]

end SK.Analytic

end
end

end OAI
