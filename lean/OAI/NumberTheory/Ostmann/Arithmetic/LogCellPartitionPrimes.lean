import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionGrid

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open PrimeProgression Classical

def assignedPrimeSupport (N : ℕ) (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) : Finset ℕ :=
  (logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))).filter
    (fun p => j.val=0 ∨ gridPoint lo hi η j.val < Real.log (p:ℝ))

theorem mem_assignedPrimeSupport (N p : ℕ) (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) :
    p ∈ assignedPrimeSupport N lo hi η j ↔ p ≤ N ∧ p.Prime ∧ Real.log (p:ℝ) ∈ assignedCell lo hi η j := by
  classical
  simp only [assignedPrimeSupport,Finset.mem_filter,mem_logPrimeSupport]
  unfold assignedCell
  split_ifs with hj
  · simp [hj,Set.mem_Icc]
  · simp [hj,Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hpN,hp,hlo,hhi⟩,hlo'⟩
      exact ⟨hpN,hp,hlo',hhi⟩
    · rintro ⟨hpN,hp,hlo,hhi⟩
      exact ⟨⟨hpN,hp,hlo.le,hhi⟩,hlo⟩

theorem assignedPrimeSupport_subset {N : ℕ} {lo hi η : ℝ} (h : lo ≤ hi)
    (j : Fin (gridCount lo hi η)) : assignedPrimeSupport N lo hi η j ⊆ logPrimeSupport N lo hi := by
  intro p hp
  obtain ⟨hpN,hpp,hcell⟩ := (mem_assignedPrimeSupport N p lo hi η j).mp hp
  have hb := assignedCell_subset_interval h j hcell
  exact (mem_logPrimeSupport N p lo hi).mpr ⟨hpN,hpp,hb.1,hb.2⟩

theorem assignedPrimeSupport_eq_filter {N : ℕ} {lo hi η : ℝ} (h : lo ≤ hi)
    (j : Fin (gridCount lo hi η)) :
    assignedPrimeSupport N lo hi η j = (logPrimeSupport N lo hi).filter
      (fun p : ℕ => Real.log (p:ℝ) ∈ assignedCell lo hi η j) := by
  classical
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro hp
    exact ⟨assignedPrimeSupport_subset h j hp,(mem_assignedPrimeSupport N p lo hi η j).mp hp |>.2.2⟩
  · rintro ⟨hp,hcell⟩
    have hp' := (mem_logPrimeSupport N p lo hi).mp hp
    exact (mem_assignedPrimeSupport N p lo hi η j).mpr ⟨hp'.1,hp'.2.1,hcell⟩

theorem exists_unique_assignedPrime {N p : ℕ} {lo hi η : ℝ} (h : lo ≤ hi)
    (hp : p ∈ logPrimeSupport N lo hi) :
    ∃! j : Fin (gridCount lo hi η), p ∈ assignedPrimeSupport N lo hi η j := by
  have hp' := (mem_logPrimeSupport N p lo hi).mp hp
  obtain ⟨j,hj⟩ := exists_assignedCell (η:=η) h hp'.2.2
  refine ⟨j,(mem_assignedPrimeSupport N p lo hi η j).mpr ⟨hp'.1,hp'.2.1,hj⟩,?_⟩
  intro k hk
  by_contra hkj
  exact Set.disjoint_left.mp (assignedCell_pairwiseDisjoint h hkj)
    ((mem_assignedPrimeSupport N p lo hi η k).mp hk).2.2 hj

theorem sum_assignedPrimeSupport {A : Type*} [AddCommMonoid A]
    (N : ℕ) (lo hi η : ℝ) (h : lo ≤ hi) (f : ℕ → A) :
    (∑ j : Fin (gridCount lo hi η), ∑ p ∈ assignedPrimeSupport N lo hi η j, f p) =
      ∑ p ∈ logPrimeSupport N lo hi, f p := by
  classical
  simp_rw [assignedPrimeSupport_eq_filter h,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := (mem_logPrimeSupport N p lo hi).mp hp
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
