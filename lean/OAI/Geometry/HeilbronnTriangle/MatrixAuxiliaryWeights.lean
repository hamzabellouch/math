import OAI.Geometry.HeilbronnTriangle.AuxiliaryWeights
import OAI.Geometry.HeilbronnTriangle.IndependentColumns

namespace OAI


noncomputable section

namespace Problem355.MatrixAuxiliaryWeights

variable {K : Type*} [Field K] [Fintype K]

abbrev Space (K : Type*) := Fin 3 → K
abbrev LinearGroup (K : Type*) [Field K] := Space K ≃ₗ[K] Space K

variable [Fintype (LinearGroup K)]

def inclusionEvents (A : Matrix (Fin 3) (Fin 3) K) (S : Finset (Space K)) :
    Finset (LinearGroup K) := by
  classical
  exact Finset.univ.filter fun e => ∀ j, e.symm (A.col j) ∈ S

def fixedShiftWeight (A : Matrix (Fin 3) (Fin 3) K) (S : Finset (Space K)) : ℝ :=
  ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
    ((inclusionEvents A S).card / (Fintype.card (LinearGroup K) : ℝ))

theorem fixedShiftWeight_nonneg (A : Matrix (Fin 3) (Fin 3) K)
    (S : Finset (Space K)) : 0 ≤ fixedShiftWeight A S := by
  unfold fixedShiftWeight
  positivity

theorem fixedShiftWeight_pos_iff (A : Matrix (Fin 3) (Fin 3) K)
    (S : Finset (Space K)) (hS : S.Nonempty) :
    0 < fixedShiftWeight A S ↔
      ∃ g : LinearGroup K, ∀ j, g.symm (A.col j) ∈ S := by
  classical
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hfactor : 0 < ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 := by positivity
  have hgroup : (0 : ℝ) < Fintype.card (LinearGroup K) := by positivity
  rw [fixedShiftWeight, mul_pos_iff_of_pos_left hfactor,
    div_pos_iff_of_pos_right hgroup]
  have hcard : (0 : ℝ) < (inclusionEvents A S).card ↔
      (inclusionEvents A S).Nonempty := by
    exact_mod_cast (Finset.card_pos : 0 < (inclusionEvents A S).card ↔ _)
  rw [hcard]
  simp [inclusionEvents, Finset.nonempty_def]

theorem normalized_inclusion_probability (A : Matrix (Fin 3) (Fin 3) K)
    (S : Finset (Space K)) (hS : S.Nonempty) :
    (((inclusionEvents A S).card : ℝ) / Fintype.card (LinearGroup K)) /
        (S.card : ℝ) ^ 3 = fixedShiftWeight A S / (Fintype.card K : ℝ) ^ 9 := by
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hq : (Fintype.card K : ℝ) ≠ 0 := by positivity
  unfold fixedShiftWeight
  field_simp

theorem fixedShiftWeight_le_four_of_rank_two
    (A : Matrix (Fin 3) (Fin 3) K) (S : Finset (Space K))
    (hS : S.Nonempty) (hrank : 2 ≤ A.rank) :
    fixedShiftWeight A S ≤ 4 * ((Fintype.card K : ℝ) ^ 3 / S.card) := by
  classical
  obtain ⟨e, he⟩ := IndependentColumns.exists_independent_columns A 2 hrank
  let p : AuxiliaryWeights.LinearFamily K (Space K) (Fin 2) := ⟨A.col ∘ e, he⟩
  let E := Finset.univ.filter fun g : LinearGroup K => ∀ i, g.symm (p.1 i) ∈ S
  have hsub : inclusionEvents A S ⊆ E := by
    intro g hg
    have hcols := (Finset.mem_filter.mp hg).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hcols (e i)⟩
  have hc : ((inclusionEvents A S).card : ℝ) ≤ E.card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    fixedShiftWeight A S ≤ ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
        ((E.card : ℝ) / Fintype.card (LinearGroup K)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hc (by positivity)) (by positivity)
    _ ≤ 4 * ((Fintype.card K : ℝ) ^ 3 / S.card) :=
      AuxiliaryWeights.linear_pair_weight_le_four p S hS

theorem fixedShiftWeight_le_two_of_column_ne_zero
    (A : Matrix (Fin 3) (Fin 3) K) (S : Finset (Space K))
    (hS : S.Nonempty) (j : Fin 3) (hj : A.col j ≠ 0) :
    fixedShiftWeight A S ≤ 2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
  classical
  let E := Finset.univ.filter fun g : LinearGroup K => g.symm (A.col j) ∈ S
  have hsub : inclusionEvents A S ⊆ E := by
    intro g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hg).2 j⟩
  have hc : ((inclusionEvents A S).card : ℝ) ≤ E.card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    fixedShiftWeight A S ≤ ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
        ((E.card : ℝ) / Fintype.card (LinearGroup K)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hc (by positivity)) (by positivity)
    _ ≤ 2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 :=
      AuxiliaryWeights.nonzero_vector_weight_le_two (A.col j) hj S hS

theorem fixedShiftWeight_eq_zero_of_column_zero
    (A : Matrix (Fin 3) (Fin 3) K) (S : Finset (Space K))
    (hzero : (0 : Space K) ∉ S) (j : Fin 3) (hj : A.col j = 0) :
    fixedShiftWeight A S = 0 := by
  classical
  have he : inclusionEvents A S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hcol := (Finset.mem_filter.mp hg).2 j
    exact hzero (by simpa [hj] using hcol)
  simp [fixedShiftWeight, he]

theorem fixedShiftWeight_le_two
    (A : Matrix (Fin 3) (Fin 3) K) (S : Finset (Space K))
    (hS : S.Nonempty) (hzero : (0 : Space K) ∉ S) :
    fixedShiftWeight A S ≤ 2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
  by_cases h : A.col 0 = 0
  · rw [fixedShiftWeight_eq_zero_of_column_zero A S hzero 0 h]
    positivity
  · exact fixedShiftWeight_le_two_of_column_ne_zero A S hS 0 h

end Problem355.MatrixAuxiliaryWeights

end

end OAI
