import OAI.Combinatorics.ContingencyTables.Counting.CompanionStoredSize

namespace OAI

/-! # Height and shape invariants for chronological stored values -/
namespace ContingencyTables.CompanionStoredSize
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram
open CompanionPhaseFinishProgram

def StoredShape (R : ℕ) (s : Stored) : Prop :=
  s.1.length ≤ R ∧ ∀ row∈s.1,row.length ≤ R

lemma height_mono {M N : ℕ} (h : M ≤ N) {s : Stored} (hs : StoredHeight M s) : StoredHeight N s :=
  ⟨fun row hr x hx => (hs.1 row hr x hx).trans h,hs.2.trans h⟩

lemma shape_mono {M N : ℕ} (h : M ≤ N) {s : Stored} (hs : StoredShape M s) : StoredShape N s :=
  ⟨hs.1.trans h,fun row hr => (hs.2 row hr).trans h⟩

lemma shape_of_weight (s : Stored) : StoredShape (weight s) s := by
  refine ⟨(list_length_le_weight _).trans (weight_fst s),?_⟩
  intro row hr
  exact (list_length_le_weight _).trans ((weight_mem hr).trans (weight_fst s))

lemma height_of_weight (s : Stored) : StoredHeight (weight s) s := by
  refine ⟨?_,(TreeFraction.height_le_weight _).trans (weight_snd s)⟩
  intro row hr x hx
  exact (TreeFraction.height_le_weight _).trans
    ((weight_mem hx).trans ((weight_mem hr).trans (weight_fst s)))

lemma weight_of_bounds (s : Stored) (R M : ℕ) (hR : StoredShape R s) (hM : StoredHeight M s) :
    weight s ≤ R*(R*(8*M+4)+2)+8*M+5 := by
  have rows (row : List TreeFraction.Fraction) (hr : row∈s.1) :
      weight row ≤ R*(8*M+4)+1 := by
    have h := weight_map_bound (f := id) (as := row) (N := 8*M+3) (by
      intro x hx
      exact (TreeFraction.weight_le_height x).trans (by have := hM.1 row hr x hx; omega))
    simp only [List.map_id] at h
    exact h.trans (by gcongr; exact hR.2 row hr)
  have h := weight_map_bound (f := id) (as := s.1) (N := R*(8*M+4)+1) rows
  simp only [List.map_id] at h
  have hm := TreeFraction.weight_le_height s.2
  have hn : weight s.1 ≤ R*(R*(8*M+4)+2)+1 := h.trans (by gcongr; exact hR.1)
  conv_lhs => rw [show s=(s.1,s.2) from rfl,weight_prod]
  nlinarith [hM.2]

lemma next_shape (z : CompanionPhaseFinishProgram.Input) :
    StoredShape (trajectory z).1.length (next z) := by
  constructor
  · simp only [next,updateMatrix,CompanionMultiplierMatrixProgram.indices,List.length_map,
      List.length_range]
    exact le_rfl
  · intro row hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    simp only [updateRow,CompanionMultiplierMatrixProgram.indices,List.length_map,List.length_range]
    exact le_rfl

end ContingencyTables.CompanionStoredSize

end OAI
