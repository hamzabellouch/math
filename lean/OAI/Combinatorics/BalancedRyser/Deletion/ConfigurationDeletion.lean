import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Incidence.Stability

namespace OAI

namespace Balanced.Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem choice_line_injective_of_valid_compatible
    (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro i j hij
  by_contra hne
  let p := tuplePoint C.merged (C.choice j).tuple 0
  have hp : p ∈ designated C.merged (C.choice j) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hon : OnLine p (C.choice j).line := (hV.2 j).2.2.2.2.2.1 0
  apply hC.1 i j hne p hp
  simpa only [hij] using hon

theorem splitLines_filter_direction (hV : C.Valid) (d : Direction F) :
    C.splitLines.filter (fun l => l.1 = d) =
      Finset.univ.image (fun b : Bool => (C.choice (d, b)).line) := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨hl, hdir⟩ := Finset.mem_filter.mp hl
    obtain ⟨⟨e, b⟩, _, he⟩ := Finset.mem_image.mp hl
    have hed : e = d := by
      calc
        e = (C.choice (e, b)).line.1 := (hV.2 (e, b)).1.symm
        _ = l.1 := congrArg Prod.fst he
        _ = d := hdir
    subst e
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, he⟩
  · intro hl
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hl
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, hb⟩
    · exact hb ▸ (hV.2 (d, b)).1

theorem card_splitLines_filter_direction (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) :
    (C.splitLines.filter (fun l => l.1 = d)).card = 2 := by
  rw [C.splitLines_filter_direction hV d]
  have hinj : Function.Injective (fun b : Bool => (C.choice (d, b)).line) := by
    intro a b hab
    exact congrArg Prod.snd (C.choice_line_injective_of_valid_compatible hV hC hab)
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem splitLines_disjoint_constituents (hV : C.Valid) :
    Disjoint C.splitLines (constituentLines C.merged) := by
  classical
  apply Finset.disjoint_left.mpr
  intro l hl hm
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hl
  exact (hV.2 s).2.1 (hs ▸ hm)

omit [Field F] in

theorem deletedLines_filter_direction (d : Direction F) :
    C.deletedLines.filter (fun l => l.1 = d) =
      (C.splitLines.filter (fun l => l.1 = d)) ∪ {constituent C.merged d true} := by
  classical
  rw [deletedLines, Finset.filter_union]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨e, he⟩, hdir⟩
    have hed : e = d := by
      calc
        e = l.1 := congrArg Prod.fst he
        _ = d := hdir
    exact hed ▸ he.symm
  · intro hl
    exact ⟨⟨d, hl.symm⟩, hl ▸ rfl⟩

theorem deletedLines_isDeletionSet (hV : C.Valid) (hC : C.Compatible) :
    IsDeletionSet 3 C.deletedLines := by
  classical
  intro d
  rw [C.deletedLines_filter_direction d]
  have hdis : Disjoint (C.splitLines.filter (fun l => l.1 = d))
      {constituent C.merged d true} := by
    apply Finset.disjoint_left.mpr
    intro l hl hm
    have hc : l ∈ constituentLines C.merged := by
      have he : l = constituent C.merged d true := Finset.mem_singleton.mp hm
      exact he ▸ Finset.mem_image.mpr ⟨(d, true), Finset.mem_univ _, rfl⟩
    exact Finset.disjoint_left.mp (C.splitLines_disjoint_constituents hV)
      (Finset.mem_filter.mp hl).1 hc
  rw [Finset.card_union_of_disjoint hdis, C.card_splitLines_filter_direction hV hC]
  simp

theorem core_eq_uncoveredBy : C.core = uncoveredBy C.deletedLines := rfl

theorem core_eq_uncoveredPoints : C.core = uncoveredPoints C.deletedLines := rfl

theorem corePencilEvent_iff_coreConcentration (ρ : ℝ) :
    CorePencilEvent (ρ / 4) C.deletedLines ↔ C.CoreConcentration ρ := by
  constructor
  · intro h L hL hc hcover
    apply h L (Finset.disjoint_left.mpr hL) hc hcover
  · intro h L hL hc hcover
    apply h L (Finset.disjoint_left.mp hL) hc hcover

end Balanced.Configuration

end OAI
