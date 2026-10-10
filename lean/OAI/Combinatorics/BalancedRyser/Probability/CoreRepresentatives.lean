import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Construction.Construction

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def coreRepresentative : BlockLabel F → Finset (Line F)
  | Sum.inl l => {l}
  | Sum.inr (Sum.inl d) => {constituent C.merged d false}
  | Sum.inr (Sum.inr _) => ∅

omit [Field F] in
lemma mem_constituentLines (d : Direction F) (s : Bool) :
    constituent C.merged d s ∈ constituentLines C.merged := by
  classical
  exact Finset.mem_image.mpr ⟨(d, s), Finset.mem_univ _, rfl⟩

lemma constituent_not_split (hvalid : C.Valid) (d : Direction F) (s : Bool) :
    constituent C.merged d s ∉ C.splitLines := by
  classical
  intro h
  obtain ⟨slot, _, he⟩ := Finset.mem_image.mp h
  have hex := (hvalid.2 slot).2.1
  apply hex
  rw [he]
  exact C.mem_constituentLines d s

lemma false_constituent_not_deleted (hvalid : C.Valid) (d : Direction F) :
    constituent C.merged d false ∉ C.deletedLines := by
  classical
  intro h
  rcases Finset.mem_union.mp h with hs | hm
  · exact C.constituent_not_split hvalid d false hs
  · obtain ⟨e, _, he⟩ := Finset.mem_image.mp hm
    have hed : e = d := congrArg Prod.fst he
    subst e
    exact hvalid.1 d (congrArg Prod.snd he).symm

lemma core_avoids_deleted {p : Point F} (hp : p ∈ C.core)
    {l : Line F} (hl : l ∈ C.deletedLines) : ¬ OnLine p l := by
  exact (Finset.mem_filter.mp hp).2 l hl

omit [Field F] in
lemma split_mem_deleted (slot : Slot F) : (C.choice slot).line ∈ C.deletedLines := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

lemma tuplePoint_not_core (hvalid : C.Valid) (slot : Slot F) (i : Fin 4) :
    tuplePoint C.merged (C.choice slot).tuple i ∉ C.core := by
  intro hp
  exact C.core_avoids_deleted hp (C.split_mem_deleted slot)
    ((hvalid.2 slot).2.2.2.2.2.1 i)

theorem core_block_has_representative (hvalid : C.Valid)
    {b : BlockLabel F} (hb : C.IsBlockLabel b) {p : Point F}
    (hp : p ∈ C.core) (hpb : p ∈ C.blockPoints b) :
    ∃ l ∈ C.coreRepresentative b, l ∉ C.deletedLines ∧ OnLine p l := by
  classical
  rcases b with l | d | ⟨slot, side⟩
  · refine ⟨l, by simp [coreRepresentative], ?_, ?_⟩
    · intro hd
      rcases Finset.mem_union.mp hd with hs | hm
      · exact hb (Finset.mem_union_left _ hs)
      · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hm
        exact hb (Finset.mem_union_right _ (C.mem_constituentLines d true))
    · exact (Finset.mem_filter.mp (Finset.mem_inter.mp hpb).1).2
  · refine ⟨constituent C.merged d false, by simp [coreRepresentative],
      C.false_constituent_not_deleted hvalid d, ?_⟩
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hpb).1 with hfalse | htrue
    · exact (Finset.mem_filter.mp hfalse).2
    · have hdel : constituent C.merged d true ∈ C.deletedLines := by
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩
      exact False.elim (C.core_avoids_deleted hp hdel (Finset.mem_filter.mp htrue).2)
  · cases side <;> simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hpb
    · rcases hpb with rfl | rfl
      · exact False.elim (C.tuplePoint_not_core hvalid slot 0 hp)
      · exact False.elim (C.tuplePoint_not_core hvalid slot 2 hp)
    · rcases hpb with rfl | rfl
      · exact False.elim (C.tuplePoint_not_core hvalid slot 1 hp)
      · exact False.elim (C.tuplePoint_not_core hvalid slot 3 hp)

lemma core_subset_points_for_representatives : C.core ⊆ C.points := by
  classical
  intro p hp
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l hl
  exact C.core_avoids_deleted hp (Finset.mem_union_left _ hl)

omit [Field F] [Fintype F] [DecidableEq F] in
lemma coreRepresentative_card_le_one (b : BlockLabel F) :
    (C.coreRepresentative b).card ≤ 1 := by
  rcases b with l | d | s <;> simp [coreRepresentative]

lemma coreRepresentative_not_deleted (hvalid : C.Valid)
    {b : BlockLabel F} (hb : C.IsBlockLabel b)
    {l : Line F} (hl : l ∈ C.coreRepresentative b) : l ∉ C.deletedLines := by
  classical
  rcases b with b | d | s
  · simp only [coreRepresentative, Finset.mem_singleton] at hl
    subst l
    intro hd
    rcases Finset.mem_union.mp hd with hs | hm
    · exact hb (Finset.mem_union_left _ hs)
    · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hm
      exact hb (Finset.mem_union_right _ (C.mem_constituentLines d true))
  · simp only [coreRepresentative, Finset.mem_singleton] at hl
    subst l
    exact C.false_constituent_not_deleted hvalid d
  · simp [coreRepresentative] at hl

omit [Field F] [Fintype F] in
theorem representatives_card_le (B : Finset (BlockLabel F)) :
    (B.biUnion C.coreRepresentative).card ≤ B.card := by
  simpa using Finset.card_biUnion_le_card_mul B C.coreRepresentative 1
    (fun b _ => C.coreRepresentative_card_le_one b)

theorem core_cover_reduction (hvalid : C.Valid)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ p ∈ C.points, ∃ b ∈ B, p ∈ C.blockPoints b) :
    (B.biUnion C.coreRepresentative).card ≤ B.card ∧
    (∀ l ∈ B.biUnion C.coreRepresentative, l ∉ C.deletedLines) ∧
    CoversPoints (B.biUnion C.coreRepresentative) C.core := by
  classical
  refine ⟨C.representatives_card_le B, ?_, ?_⟩
  · intro l hl
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hl
    exact C.coreRepresentative_not_deleted hvalid (hlabels b hb) hbl
  · intro p hp
    obtain ⟨b, hb, hpb⟩ := hcover p (C.core_subset_points_for_representatives hp)
    obtain ⟨l, hl, _, hpl⟩ := C.core_block_has_representative hvalid (hlabels b hb) hp hpb
    exact ⟨l, Finset.mem_biUnion.mpr ⟨b, hb, hl⟩, hpl⟩

def RepresentedThrough (P : ProjectivePoint F) (b : BlockLabel F) : Prop :=
  ∃ l ∈ C.coreRepresentative b, ThroughProjective l P

omit [Fintype F] in
lemma pencil_representatives_card_le_labels (B : Finset (BlockLabel F))
    (P : ProjectivePoint F) :
    ((B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l P)).card ≤
      (B.filter (C.RepresentedThrough P)).card := by
  classical
  have hsub : (B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l P) ⊆
      (B.filter (C.RepresentedThrough P)).biUnion C.coreRepresentative := by
    intro l hl
    obtain ⟨hunion, hthrough⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hunion
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, l, hbl, hthrough⟩, hbl⟩
  exact (Finset.card_le_card hsub).trans (C.representatives_card_le _)

omit [Fintype F] in
lemma outside_pencil_representatives_card_le_labels (B : Finset (BlockLabel F))
    (P : ProjectivePoint F) :
    ((B.biUnion C.coreRepresentative).filter (fun l => ¬ ThroughProjective l P)).card ≤
      (B.filter (fun b => ¬ C.RepresentedThrough P b)).card := by
  classical
  have hsub : (B.biUnion C.coreRepresentative).filter (fun l => ¬ ThroughProjective l P) ⊆
      (B.filter (fun b => ¬ C.RepresentedThrough P b)).biUnion C.coreRepresentative := by
    intro l hl
    obtain ⟨hunion, hnot⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hunion
    have hbnot : ¬ C.RepresentedThrough P b := by
      rintro ⟨m, hbm, hm⟩
      have he : l = m := Finset.card_le_one.mp (C.coreRepresentative_card_le_one b) l hbl m hbm
      exact hnot (he.symm ▸ hm)
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hbnot⟩, hbl⟩
  exact (Finset.card_le_card hsub).trans (C.representatives_card_le _)

theorem core_cover_outside_pencil_budget (hvalid : C.Valid)
    {rho : ℝ} (hconcentration : C.CoreConcentration rho)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F)
    (hcover : ∀ p ∈ C.points, ∃ b ∈ B, p ∈ C.blockPoints b) :
    ∃ P : ProjectivePoint F,
      ((B.filter (fun b => ¬ C.RepresentedThrough P b)).card : ℝ) ≤
        rho * Fintype.card F / 4 := by
  classical
  obtain ⟨hrepCard, hrepDeleted, hrepCover⟩ := C.core_cover_reduction hvalid B hlabels hcover
  obtain ⟨P, hlarge⟩ := hconcentration (B.biUnion C.coreRepresentative)
    hrepDeleted (hrepCard.trans hcard) hrepCover
  refine ⟨P, ?_⟩
  have hcount := C.pencil_representatives_card_le_labels B P
  have hcountReal :
      (((B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l P)).card : ℝ) ≤
      ((B.filter (C.RepresentedThrough P)).card : ℝ) := by exact_mod_cast hcount
  have hcardReal : (B.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hcard
  have hpartition :
      (B.filter (C.RepresentedThrough P)).card +
      (B.filter (fun b => ¬ C.RepresentedThrough P b)).card = B.card := by
    exact Finset.card_filter_add_card_filter_not _
  have hpartitionReal :
      ((B.filter (C.RepresentedThrough P)).card : ℝ) +
      ((B.filter (fun b => ¬ C.RepresentedThrough P b)).card : ℝ) = B.card := by
    exact_mod_cast hpartition
  nlinarith

end
end Configuration
end Balanced

end OAI
