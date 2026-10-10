import OAI.Combinatorics.BalancedRyser.Candidates.DeletedConstituentForcing

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] in
lemma regular_not_deleted {l : Line F}
    (hsplit : l ∉ C.splitLines) (hconst : l ∉ constituentLines C.merged) :
    l ∉ C.deletedLines := by
  intro hl
  rcases Finset.mem_union.mp hl with hs | ht
  · exact hsplit hs
  · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp ht
    exact hconst (C.mem_constituentLines d true)

omit [Field F] in
lemma regular_label_selected_of_represented (B : Finset (BlockLabel F))
    {l : Line F} (hconst : l ∉ constituentLines C.merged)
    (hrep : l ∈ B.biUnion C.coreRepresentative) : (Sum.inl l : BlockLabel F) ∈ B := by
  obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hrep
  rcases b with m | d | s
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    simpa [hbl] using hb
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    exact False.elim (hconst (hbl.symm ▸ C.mem_constituentLines d false))
  · simp [coreRepresentative] at hbl

omit [Field F] in
lemma merged_label_selected_of_false_represented (B : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ B, C.IsBlockLabel b) (d : Direction F)
    (hrep : constituent C.merged d false ∈ B.biUnion C.coreRepresentative) :
    (Sum.inr (Sum.inl d) : BlockLabel F) ∈ B := by
  obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hrep
  rcases b with m | e | s
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    have hbad := hlabels (Sum.inl m) hb
    exact False.elim (hbad (Finset.mem_union_right _ (hbl ▸ C.mem_constituentLines d false)))
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    have hde : d = e := congrArg Prod.fst hbl
    simpa [hde] using hb
  · simp [coreRepresentative] at hbl

def forcedNonsplitLabel (p : Point F) (d : Direction F) : BlockLabel F :=
  if lineThrough d p ∈ constituentLines C.merged then Sum.inr (Sum.inl d)
  else Sum.inl (lineThrough d p)

@[simp] theorem forcedNonsplitLabel_direction (p : Point F) (d : Direction F) :
    blockDirection (C.forcedNonsplitLabel p d) = d := by
  unfold forcedNonsplitLabel
  split <;> rfl

theorem forcedNonsplitLabel_injective (p : Point F) :
    Function.Injective (C.forcedNonsplitLabel p) := by
  intro d e h
  have he := congrArg blockDirection h
  simpa using he

theorem forcedNonsplitLabel_mem (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (d : Direction F) (hnotsplit : lineThrough d p ∉ C.splitLines) :
    C.forcedNonsplitLabel p d ∈ B := by
  classical
  unfold forcedNonsplitLabel
  split
  · rename_i hconst
    obtain ⟨⟨e, side⟩, _, he⟩ := Finset.mem_image.mp hconst
    have hed : e = d := congrArg Prod.fst he
    subst e
    cases side
    · have hnotdel := C.false_constituent_not_deleted hvalid d
      have hpd : OnLine p (constituent C.merged d false) := by rw [he]; rfl
      have hrep := C.ordinary_pencil_line_is_represented hvalid hocc hsize B hlabels hcover
        p hbudget (constituent C.merged d false) hpd hnotdel
      exact C.merged_label_selected_of_false_represented B hlabels d hrep
    · have hpd : OnLine p (constituent C.merged d true) := by rw [he]; rfl
      exact C.deleted_constituent_merged_label_selected hocc hsize B hlabels hcover p hbudget d hpd
  · rename_i hconst
    apply C.regular_label_selected_of_represented B hconst
    exact C.ordinary_pencil_line_is_represented hvalid hocc hsize B hlabels hcover p hbudget
      (lineThrough d p) (onLine_lineThrough d p) (C.regular_not_deleted hnotsplit hconst)

def nonsplitDirections (p : Point F) : Finset (Direction F) :=
  Finset.univ.filter (fun d => lineThrough d p ∉ C.splitLines)

def forcedNonsplitLabels (p : Point F) : Finset (BlockLabel F) :=
  (C.nonsplitDirections p).image (C.forcedNonsplitLabel p)

theorem split_directions_card (p : Point F) :
    ((Finset.univ : Finset (Direction F)).filter
      (fun d => lineThrough d p ∈ C.splitLines)).card = C.splitMultiplicity p := by
  classical
  let dirs := (Finset.univ : Finset (Direction F)).filter (fun d => lineThrough d p ∈ C.splitLines)
  have himage : dirs.image (fun d => lineThrough d p) = C.splitLinesAt p := by
    ext l
    constructor
    · intro hl
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hl
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).2, onLine_lineThrough d p⟩
    · intro hl
      obtain ⟨hsplit, hp⟩ := Finset.mem_filter.mp hl
      have he := line_eq_lineThrough p l hp
      refine Finset.mem_image.mpr ⟨l.1, ?_, he.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ hsplit⟩
  have hinj : Function.Injective (fun d : Direction F => lineThrough d p) := by
    intro d e he
    exact congrArg Prod.fst he
  have hcard := Finset.card_image_of_injective dirs hinj
  rw [himage] at hcard
  exact hcard.symm

theorem forcedNonsplitLabels_card_add (p : Point F) :
    (C.forcedNonsplitLabels p).card + C.splitMultiplicity p = Fintype.card F + 1 := by
  classical
  have hforced : (C.forcedNonsplitLabels p).card = (C.nonsplitDirections p).card :=
    Finset.card_image_of_injective _ (C.forcedNonsplitLabel_injective p)
  rw [hforced, ← C.split_directions_card p]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Direction F))) (fun d => lineThrough d p ∈ C.splitLines)
  simpa [nonsplitDirections, Nat.add_comm, Fintype.card_option] using hpartition

theorem forcedNonsplitLabels_card (p : Point F) :
    (C.forcedNonsplitLabels p).card = Fintype.card F + 1 - C.splitMultiplicity p := by
  have := C.forcedNonsplitLabels_card_add p
  omega

theorem forcedNonsplitLabels_subset (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) : C.forcedNonsplitLabels p ⊆ B := by
  intro b hb
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
  exact C.forcedNonsplitLabel_mem hvalid hocc hsize B hlabels hcover p hbudget d
    (Finset.mem_filter.mp hd).2

theorem remaining_labels_budget (B : Finset (BlockLabel F))
    (p : Point F) (hsubset : C.forcedNonsplitLabels p ⊆ B)
    (hcard : B.card ≤ Fintype.card F) :
    1 ≤ C.splitMultiplicity p ∧
      (B \ C.forcedNonsplitLabels p).card ≤ C.splitMultiplicity p - 1 := by
  have hforce := C.forcedNonsplitLabels_card_add p
  have hle := Finset.card_le_card hsubset
  rw [Finset.card_sdiff_of_subset hsubset]
  omega

end
end Configuration
end Balanced

end OAI
