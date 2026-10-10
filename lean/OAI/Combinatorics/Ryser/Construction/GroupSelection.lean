import OAI.Combinatorics.Ryser.Construction.GroupBounds
import OAI.Combinatorics.Ryser.Construction.DeletionUnionBasic
import OAI.Combinatorics.Ryser.Selection.Definitions

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]

def groupSelectionData (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    Selection.Data F (Fintype.card (ConfigurationGroup σ)) where
  W i := groupPoints σ u v huv ((Fintype.equivFin (ConfigurationGroup σ)).symm i)
  dirs i := groupConflict σ u v huv ((Fintype.equivFin (ConfigurationGroup σ)).symm i)

@[simp] theorem groupSelectionData_W_equivFin (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (i : ConfigurationGroup σ) :
    (groupSelectionData σ u v huv).W ((Fintype.equivFin (ConfigurationGroup σ)) i) =
      groupPoints σ u v huv i := by
  simp only [groupSelectionData, Equiv.symm_apply_apply]

@[simp] theorem groupSelectionData_dirs_equivFin (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (i : ConfigurationGroup σ) :
    (groupSelectionData σ u v huv).dirs ((Fintype.equivFin (ConfigurationGroup σ)) i) =
      groupConflict σ u v huv i := by
  simp only [groupSelectionData, Equiv.symm_apply_apply]

def groupSelectionConstant (s : ℕ) : ℕ := s ^ 2 + s + 2

theorem card_groups_le_two_mul_card (σ : k →+* F)
    (hs : 2 ≤ Fintype.card k) :
    Fintype.card (ConfigurationGroup σ) ≤ 2 * Fintype.card F := by
  have hfactor : 1 ≤ Fintype.card k - 1 := by omega
  have hle : Fintype.card (ConfigurationGroup σ) ≤
      Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (Fintype.card (ConfigurationGroup σ)) hfactor
  exact hle.trans (card_groups_mul_sub_one_le σ)

theorem groupSelectionData_direction_multiplicity_le_two
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ (groupSelectionData σ u v huv).dirs i)).card ≤ 2 := by
  classical
  let e := Fintype.equivFin (ConfigurationGroup σ)
  let I := Finset.univ.filter (fun i => d ∈ (groupSelectionData σ u v huv).dirs i)
  let J := Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)
  have hsub : I.image e.symm ⊆ J := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e.symm.injective] at hc
  exact hc.trans (groupConflict_multiplicity_le_two σ u v huv d)

theorem groupSelectionData_bounded (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hs : 2 ≤ Fintype.card k) :
    Selection.Bounded (groupSelectionConstant (Fintype.card k))
      (groupSelectionData σ u v huv) := by
  classical
  have htwo : 2 ≤ groupSelectionConstant (Fintype.card k) := by
    unfold groupSelectionConstant
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (card_groups_le_two_mul_card σ hs).trans
      (Nat.mul_le_mul_right (Fintype.card F) htwo)
  · intro i
    change (groupPoints σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)).card ≤ _
    rw [groupPoints_card]
    unfold groupSelectionConstant
    omega
  · intro i
    have hc := groupConflict_card_le σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)
    change (groupConflict σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)).card ≤ _
    unfold groupSelectionConstant
    omega
  · intro d
    exact (groupSelectionData_direction_multiplicity_le_two σ u v huv d).trans htwo

def selectedShifts (σ : k →+* F) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (i : ConfigurationGroup σ) : Point F :=
  pool ((Fintype.equivFin (ConfigurationGroup σ)) i,
    choice ((Fintype.equivFin (ConfigurationGroup σ)) i))

theorem selectedShifts_projection_ne
    (σ : k →+* F) (u v : k) (huv : u ≠ v) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (hchoice : ∀ i j, i ≠ j →
      ¬ Selection.Conflict (groupSelectionData σ u v huv) i j
        (pool (i, choice i)) (pool (j, choice j)))
    (i j : ConfigurationGroup σ) (hij : i ≠ j)
    (x y : Point k) (d : Direction F)
    (hd : d ∈ groupConflict σ u v huv i ∪ groupConflict σ u v huv j) :
    projection d (placedPoint σ (groupPlacement σ u v huv i)
        (selectedShifts σ pool choice i) x) ≠
      projection d (placedPoint σ (groupPlacement σ u v huv j)
        (selectedShifts σ pool choice j) y) := by
  classical
  let e := Fintype.equivFin (ConfigurationGroup σ)
  intro heq
  apply hchoice (e i) (e j) (fun h => hij (e.injective h))
  refine ⟨(groupPlacement σ u v huv i).apply (mapPoint σ x), ?_,
    (groupPlacement σ u v huv j).apply (mapPoint σ y), ?_, d, ?_, ?_⟩
  · change (groupPlacement σ u v huv i).apply (mapPoint σ x) ∈
      groupPoints σ u v huv (e.symm (e i))
    rw [e.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · change (groupPlacement σ u v huv j).apply (mapPoint σ y) ∈
      groupPoints σ u v huv (e.symm (e j))
    rw [e.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  · change d ∈ groupConflict σ u v huv (e.symm (e i)) ∪
      groupConflict σ u v huv (e.symm (e j))
    simpa only [e.symm_apply_apply] using hd
  · rw [Selection.projection_sub_eq]
    exact sub_eq_zero.mpr (by
      simpa only [placedPoint, selectedShifts, e] using heq)

theorem selectedShifts_deletionSeparated
    (σ : k →+* F) (u v : k) (huv : u ≠ v) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (hchoice : ∀ i j, i ≠ j →
      ¬ Selection.Conflict (groupSelectionData σ u v huv) i j
        (pool (i, choice i)) (pool (j, choice j)))
    (a : GadgetOutcome k) :
    DeletionSeparated σ (groupPlacement σ u v huv) (selectedShifts σ pool choice) a := by
  classical
  intro i j hij p hp q hq d hd
  obtain ⟨x, rfl⟩ :=
    (mem_placedSubplane_iff σ (groupPlacement σ u v huv i)
      (selectedShifts σ pool choice i) p).mp hp
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
  apply selectedShifts_projection_ne σ u v huv pool choice hchoice i j hij x y d
  exact Finset.mem_union_right _ (groupAltered_subset_conflict σ u v huv j hd)

theorem exists_selectedShifts_deletionSeparated
    (σ : k →+* F) (u v : k) (huv : u ≠ v) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (hcompatible : Selection.HasCompatibleChoice (groupSelectionData σ u v huv) pool) :
    ∃ choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K,
      ∀ a : GadgetOutcome k,
        DeletionSeparated σ (groupPlacement σ u v huv) (selectedShifts σ pool choice) a := by
  obtain ⟨choice, hchoice⟩ := hcompatible
  exact ⟨choice, fun a => selectedShifts_deletionSeparated σ u v huv pool choice hchoice a⟩

end RyserCoveringCounterexample.Construction

end

end OAI
