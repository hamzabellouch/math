import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyMassPrefix

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def finitePrefix {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : ℝ := ∑ l, if l ≤ j then v l else 0

theorem finitePrefix_last (n : ℕ) (v : Fin (n+1) → ℝ) :
    finitePrefix v (Fin.last n)=∑ l, v l := by simp [finitePrefix, Fin.le_last]

theorem finitePrefix_succ (n : ℕ) (v : Fin (n+1) → ℝ) (i : Fin n) :
    finitePrefix v i.succ=finitePrefix v i.castSucc+v i.succ := by
  have H (l : Fin (n+1)) : (if l ≤ i.succ then v l else 0)=
      (if l ≤ i.castSucc then v l else 0)+(if l=i.succ then v l else 0) := by
    by_cases h : l=i.succ
    · subst l
      rw [ite_eq_left le_rfl,ite_eq_right (by simp),ite_eq_left rfl,zero_add]
    · have hle : l ≤ i.succ ↔ l ≤ i.castSucc := by
        have hn : l.val ≠ i.val+1 := by simpa only [Fin.val_succ] using Fin.val_ne_of_ne h
        simp only [Fin.le_def,Fin.val_succ,Fin.val_castSucc]
        omega
      simp only [ite_eq_right h,add_zero,hle]
  simp only [finitePrefix,H,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem hierarchyAtom_sum_mul_parts (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (v : Fin (n+1) → ℝ) :
    (∑ j, hierarchyAtom n m u j*v j)=u*v (Fin.last n)-∑ i, m i*(v i.succ-v i.castSucc) := by
  induction n generalizing u with
  | zero => simp [hierarchyAtom]
  | succ n ih =>
    conv_lhs => rw [Fin.sum_univ_castSucc]
    simp only [hierarchyAtom,Fin.lastCases_castSucc,Fin.lastCases_last]
    rw [ih (fun i => m i.castSucc) (m (Fin.last n)) (fun j => v j.castSucc)]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_succ,Fin.succ_last]
    ring

theorem zeroInitialAtoms_sum_mul_parts (n : ℕ) (m v : Fin (n+1) → ℝ) :
    (∑ j, zeroInitialAtoms n m j*v j)=v (Fin.last n)-∑ i : Fin n, m i.succ*(v i.succ-v i.castSucc) := by
  simpa only [zeroInitialAtoms,one_mul] using hierarchyAtom_sum_mul_parts n (fun i => m i.succ) 1 v

end SK.Analytic

end
end

end OAI
