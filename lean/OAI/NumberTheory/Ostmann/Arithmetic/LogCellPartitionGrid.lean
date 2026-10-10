import OAI.NumberTheory.Ostmann.Arithmetic.PrimeProgression

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open MeasureTheory

def gridCount (lo hi η : ℝ) : ℕ := ⌈(hi-lo)/η⌉₊+1

def gridStep (lo hi η : ℝ) : ℝ := (hi-lo)/(gridCount lo hi η:ℝ)

def gridPoint (lo hi η : ℝ) (j : ℕ) : ℝ := lo+(j:ℝ)*gridStep lo hi η

def assignedCell (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) : Set ℝ :=
  if j.val=0 then Set.Icc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))
  else Set.Ioc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))

theorem gridCount_pos (lo hi η : ℝ) : 0 < gridCount lo hi η := by unfold gridCount; omega

theorem gridStep_nonneg {lo hi η : ℝ} (h : lo ≤ hi) : 0 ≤ gridStep lo hi η := by
  unfold gridStep
  exact div_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg _)

@[simp] theorem gridPoint_zero (lo hi η : ℝ) : gridPoint lo hi η 0 = lo := by simp [gridPoint]

@[simp] theorem gridPoint_last (lo hi η : ℝ) :
    gridPoint lo hi η (gridCount lo hi η) = hi := by
  have hn : (gridCount lo hi η:ℝ) ≠ 0 := by exact_mod_cast (gridCount_pos lo hi η).ne'
  unfold gridPoint gridStep
  field_simp
  ring

theorem gridPoint_mono {lo hi η : ℝ} (h : lo ≤ hi) : Monotone (gridPoint lo hi η) := by
  intro i j hij
  unfold gridPoint
  have hs := gridStep_nonneg (η:=η) h
  gcongr

theorem gridPoint_mem {lo hi η : ℝ} (h : lo ≤ hi) {j : ℕ} (hj : j ≤ gridCount lo hi η) :
    gridPoint lo hi η j ∈ Set.Icc lo hi := by
  have hm := gridPoint_mono (η:=η) h
  exact ⟨by simpa using hm (Nat.zero_le j),by simpa using hm hj⟩

theorem gridPoint_width (lo hi η : ℝ) (j : ℕ) :
    gridPoint lo hi η (j+1)-gridPoint lo hi η j = gridStep lo hi η := by
  unfold gridPoint
  push_cast
  ring

theorem gridStep_le {lo hi η : ℝ} (_h : lo ≤ hi) (hη : 0 < η) : gridStep lo hi η ≤ η := by
  have hn : (0:ℝ) < gridCount lo hi η := by exact_mod_cast gridCount_pos lo hi η
  have hc := Nat.le_ceil ((hi-lo)/η)
  have hc' : (hi-lo)/η ≤ (gridCount lo hi η:ℝ) := by
    unfold gridCount
    push_cast
    linarith
  apply (div_le_iff₀ hn).mpr
  have hh := (div_le_iff₀ hη).mp hc'
  nlinarith

theorem gridCount_le_ceiling {lo hi η U : ℝ} (hη : 0 < η) (hU : hi-lo ≤ U) :
    gridCount lo hi η ≤ ⌈U/η⌉₊+1 := by
  unfold gridCount
  exact Nat.add_le_add_right (Nat.ceil_mono (div_le_div_of_nonneg_right hU hη.le)) 1

theorem assignedCell_subset_closed (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) :
    assignedCell lo hi η j ⊆ Set.Icc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) := by
  unfold assignedCell
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.Ioc_subset_Icc_self

theorem assignedCell_subset_interval {lo hi η : ℝ} (h : lo ≤ hi)
    (j : Fin (gridCount lo hi η)) : assignedCell lo hi η j ⊆ Set.Icc lo hi := by
  intro x hx
  have hc := assignedCell_subset_closed lo hi η j hx
  have hl := gridPoint_mem (η:=η) h j.isLt.le
  have hu := gridPoint_mem (η:=η) h (show j.val+1 ≤ gridCount lo hi η by omega)
  exact ⟨hl.1.trans hc.1,hc.2.trans hu.2⟩

theorem assignedCell_disjoint_of_lt {lo hi η : ℝ} (h : lo ≤ hi)
    {i j : Fin (gridCount lo hi η)} (hij : i < j) :
    Disjoint (assignedCell lo hi η i) (assignedCell lo hi η j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi' := (assignedCell_subset_closed lo hi η i hxi).2
  have hj0 : j.val ≠ 0 := by
    have hh : i.val < j.val := hij
    omega
  have hjc : x ∈ Set.Ioc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) := by
    simpa only [assignedCell,ite_eq_right hj0] using hxj
  have hj' := hjc.1
  have hm := gridPoint_mono (η:=η) h (show i.val+1 ≤ j.val by exact hij)
  linarith

theorem assignedCell_pairwiseDisjoint {lo hi η : ℝ} (h : lo ≤ hi) :
    Pairwise (fun i j : Fin (gridCount lo hi η) => Disjoint (assignedCell lo hi η i) (assignedCell lo hi η j)) := by
  intro i j hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact assignedCell_disjoint_of_lt h hij
  · exact (assignedCell_disjoint_of_lt h hji).symm

theorem exists_assignedCell {lo hi η x : ℝ} (h : lo ≤ hi) (hx : x ∈ Set.Icc lo hi) :
    ∃ j : Fin (gridCount lo hi η), x ∈ assignedCell lo hi η j := by
  by_cases hx0 : x=lo
  · refine ⟨⟨0,gridCount_pos lo hi η⟩,?_⟩
    have hu := gridPoint_mem (η:=η) h (gridCount_pos lo hi η)
    simp only [assignedCell,ite_true,gridPoint_zero,Set.mem_Icc]
    exact ⟨by linarith,by simpa only [hx0,Nat.zero_add] using hu.1⟩
  · have hx' : x ∈ Set.Ioc (gridPoint lo hi η 0) (gridPoint lo hi η (gridCount lo hi η)) := by
      simp only [gridPoint_zero,gridPoint_last,Set.mem_Ioc]
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),hx.2⟩
    obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc (gridCount lo hi η)
      (gridPoint lo hi η) hx')
    refine ⟨⟨j,Finset.mem_range.mp hj⟩,?_⟩
    unfold assignedCell
    split_ifs
    · exact ⟨hxj.1.le,hxj.2⟩
    · exact hxj

theorem iUnion_assignedCell {lo hi η : ℝ} (h : lo ≤ hi) :
    (⋃ j : Fin (gridCount lo hi η), assignedCell lo hi η j) = Set.Icc lo hi := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨j,hj⟩ => assignedCell_subset_interval h j hj,exists_assignedCell h⟩

theorem measurableSet_assignedCell (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) :
    MeasurableSet (assignedCell lo hi η j) := by
  unfold assignedCell
  split_ifs <;> measurability

theorem assignedCell_ae_eq_closed (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) :
    assignedCell lo hi η j =ᵐ[volume] Set.Icc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) := by
  unfold assignedCell
  split_ifs
  · rfl
  · exact Ioc_ae_eq_Icc

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
