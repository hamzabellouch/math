import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellTests
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionGrid

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open IntegerCell Classical

theorem mem_cellSupport (N p : ℕ) (lo hi : ℝ) :
    p ∈ cellSupport N lo hi ↔ p ≤ N ∧ 0 < p ∧ lo ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ hi := by
  simp only [cellSupport, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

def assignedIntegerSupport (N : ℕ) (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) : Finset ℕ :=
  (cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))).filter
    (fun p => j.val=0 ∨ gridPoint lo hi η j.val < Real.log (p:ℝ))

theorem mem_assignedIntegerSupport (N p : ℕ) (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) :
    p ∈ assignedIntegerSupport N lo hi η j ↔ p ≤ N ∧ 0 < p ∧ Real.log (p:ℝ) ∈ assignedCell lo hi η j := by
  classical
  simp only [assignedIntegerSupport,Finset.mem_filter,mem_cellSupport]
  unfold assignedCell
  split_ifs with hj
  · simp [hj,Set.mem_Icc]
  · simp [hj,Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hpN,hp,hlo,hhi⟩,hlo'⟩
      exact ⟨hpN,hp,hlo',hhi⟩
    · rintro ⟨hpN,hp,hlo,hhi⟩
      exact ⟨⟨hpN,hp,hlo.le,hhi⟩,hlo⟩

theorem assignedIntegerSupport_subset {N : ℕ} {lo hi η : ℝ} (h : lo ≤ hi)
    (j : Fin (gridCount lo hi η)) : assignedIntegerSupport N lo hi η j ⊆ cellSupport N lo hi := by
  intro p hp
  obtain ⟨hpN,hpp,hcell⟩ := (mem_assignedIntegerSupport N p lo hi η j).mp hp
  have hb := assignedCell_subset_interval h j hcell
  exact (mem_cellSupport N p lo hi).mpr ⟨hpN,hpp,hb.1,hb.2⟩

theorem assignedIntegerSupport_eq_filter {N : ℕ} {lo hi η : ℝ} (h : lo ≤ hi)
    (j : Fin (gridCount lo hi η)) :
    assignedIntegerSupport N lo hi η j = (cellSupport N lo hi).filter
      (fun p : ℕ => Real.log (p:ℝ) ∈ assignedCell lo hi η j) := by
  classical
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro hp
    exact ⟨assignedIntegerSupport_subset h j hp,(mem_assignedIntegerSupport N p lo hi η j).mp hp |>.2.2⟩
  · rintro ⟨hp,hcell⟩
    have hp' := (mem_cellSupport N p lo hi).mp hp
    exact (mem_assignedIntegerSupport N p lo hi η j).mpr ⟨hp'.1,hp'.2.1,hcell⟩

theorem exists_unique_assignedInteger {N p : ℕ} {lo hi η : ℝ} (h : lo ≤ hi)
    (hp : p ∈ cellSupport N lo hi) :
    ∃! j : Fin (gridCount lo hi η), p ∈ assignedIntegerSupport N lo hi η j := by
  have hp' := (mem_cellSupport N p lo hi).mp hp
  obtain ⟨j,hj⟩ := exists_assignedCell (η:=η) h hp'.2.2
  refine ⟨j,(mem_assignedIntegerSupport N p lo hi η j).mpr ⟨hp'.1,hp'.2.1,hj⟩,?_⟩
  intro k hk
  by_contra hkj
  exact Set.disjoint_left.mp (assignedCell_pairwiseDisjoint h hkj)
    ((mem_assignedIntegerSupport N p lo hi η k).mp hk).2.2 hj

theorem sum_assignedIntegerSupport {A : Type*} [AddCommMonoid A]
    (N : ℕ) (lo hi η : ℝ) (h : lo ≤ hi) (f : ℕ → A) :
    (∑ j : Fin (gridCount lo hi η), ∑ p ∈ assignedIntegerSupport N lo hi η j, f p) =
      ∑ p ∈ cellSupport N lo hi, f p := by
  classical
  simp_rw [assignedIntegerSupport_eq_filter h,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := (mem_cellSupport N p lo hi).mp hp
  obtain ⟨j,hj⟩ := exists_assignedCell (η:=η) h hp'.2.2
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro k hk hkj
    have hnot : Real.log (p:ℝ) ∉ assignedCell lo hi η k := fun hkp =>
      Set.disjoint_left.mp (assignedCell_pairwiseDisjoint h hkj) hkp hj
    simp [hnot]
  · simp

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
