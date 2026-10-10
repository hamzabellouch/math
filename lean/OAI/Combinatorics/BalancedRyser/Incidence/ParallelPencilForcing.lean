import OAI.Combinatorics.BalancedRyser.Incidence.AffinePencilForcing
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationStructure

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem parallel_mem_linePoints_iff (p : Point F) (l : Line F) :
    p ∈ linePoints l ↔ OnLine p l := by simp [linePoints]

private theorem missing_parallel_line_cover
    (L : Finset (Line F)) (U : Finset (Point F)) (hcover : CoversPoints L U)
    (l : Line F) (homit : l ∉ L) :
    linePoints l ∩ U ⊆
      (∅ : Finset (Point F)) ∪ (L.filter (fun m => m.1 ≠ l.1)).biUnion linePoints := by
  intro p hp
  obtain ⟨m, hm, hpm⟩ := hcover p (Finset.mem_inter.mp hp).2
  have hpl : OnLine p l := (parallel_mem_linePoints_iff p l).mp (Finset.mem_inter.mp hp).1
  have hdir : m.1 ≠ l.1 := by
    intro hsame
    have heq : m = l := eq_of_onLine_same_direction p m l hsame hpm hpl
    exact homit (heq ▸ hm)
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨m, Finset.mem_filter.mpr ⟨hm, hdir⟩, (parallel_mem_linePoints_iff p m).mpr hpm⟩)

private theorem parallel_trace_card_le_one (U : Finset (Point F))
    (l m : Line F) (hne : l ≠ m) :
    (linePoints m ∩ (linePoints l ∩ U)).card ≤ 1 := by
  calc
    (linePoints m ∩ (linePoints l ∩ U)).card ≤ (linePoints l ∩ linePoints m).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hp).2).1, (Finset.mem_inter.mp hp).1⟩
    _ ≤ 1 := distinct_line_intersection_card_le_one l m hne

private theorem missing_parallel_trace_bound
    (L : Finset (Line F)) (U : Finset (Point F)) (l : Line F) :
    ∀ m ∈ L.filter (fun m => m.1 ≠ l.1),
      (linePoints m ∩ (linePoints l ∩ U)).card ≤ 1 := by
  intro m hm
  apply parallel_trace_card_le_one U l m
  intro heq
  exact (Finset.mem_filter.mp hm).2 (congrArg Prod.fst heq.symm)

theorem missing_parallel_line_occupancy_bound
    (L : Finset (Line F)) (U : Finset (Point F)) (hcover : CoversPoints L U)
    (l : Line F) (homit : l ∉ L) :
    (linePoints l ∩ U).card ≤ (L.filter (fun m => m.1 ≠ l.1)).card := by
  have hbound : (linePoints l ∩ U).card ≤ (∅ : Finset (Point F)).card +
      1 * (L.filter (fun m => m.1 ≠ l.1)).card := by
    apply card_le_exceptional_add_cover_budget (linePoints l ∩ U)
      (∅ : Finset (Point F)) (L.filter (fun m => m.1 ≠ l.1))
      (fun m : Line F => linePoints m) 1
    · exact missing_parallel_line_cover L U hcover l homit
    · exact missing_parallel_trace_bound L U l
  rw [Finset.card_empty, Nat.one_mul, Nat.zero_add] at hbound
  exact hbound

namespace Configuration
variable (C : Configuration F)

theorem parallel_pencil_line_is_represented (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hrho : 0 < rho) (hoccupancy : C.Occupancy rho cap)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (g : Direction F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (l : Line F) (hdir : l.1 = g) (hnotdel : l ∉ C.deletedLines) :
    l ∈ B.biUnion C.coreRepresentative := by
  by_contra homit
  have hcoreCover := (C.core_cover_reduction hvalid B hlabels hcover).2.2
  have hmissing := missing_parallel_line_occupancy_bound
    (B.biUnion C.coreRepresentative) C.core hcoreCover l homit
  have houtside := C.outside_pencil_representatives_card_le_labels B (Sum.inr g)
  have houtside' :
      ((B.biUnion C.coreRepresentative).filter (fun m => m.1 ≠ l.1)).card ≤
      (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card := by
    apply le_trans (Finset.card_le_card ?_) houtside
    intro representative hrepresentative
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hrepresentative).1, ?_⟩
    simpa only [ThroughProjective, hdir] using (Finset.mem_filter.mp hrepresentative).2
  have hmissingReal : ((linePoints l ∩ C.core).card : ℝ) ≤
      ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card : ℝ) := by
    exact_mod_cast hmissing.trans houtside'
  have hocc := hoccupancy.2.1 l hnotdel
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < rho * Fintype.card F := mul_pos hrho hq
  linarith

omit [Field F] in
private theorem parallel_direction_card (g : Direction F) :
    (linesInDirection g).card = Fintype.card F := by
  unfold linesInDirection
  rw [← Finset.univ_product_univ,
    Finset.filter_product_left (fun d : Direction F => d = g)]
  simp [Finset.filter_eq']

theorem parallel_nondeleted_card (hvalid : C.Valid) (hcompatible : C.Compatible)
    (g : Direction F) :
    ((linesInDirection g) \ C.deletedLines).card = Fintype.card F - 3 := by
  rw [Finset.card_sdiff, parallel_direction_card]
  have hinter : C.deletedLines ∩ linesInDirection g =
      C.deletedLines.filter (fun l => l.1 = g) := by
    ext l
    simp only [Finset.mem_inter, linesInDirection, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hinter, ConfigurationStructure.deleted_lines_in_direction_card C hvalid hcompatible g]

theorem parallel_pencil_forced_label_count (hvalid : C.Valid)
    (hcompatible : C.Compatible) {rho : ℝ} {cap : ℕ}
    (hrho : 0 < rho) (hoccupancy : C.Occupancy rho cap)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (g : Direction F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) :
    Fintype.card F - 3 ≤ (B.filter (C.RepresentedThrough (Sum.inr g))).card := by
  have hsubset : (linesInDirection g) \ C.deletedLines ⊆
      (B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l (Sum.inr g)) := by
    intro l hl
    obtain ⟨hlg, hnotdel⟩ := Finset.mem_sdiff.mp hl
    have hdir : l.1 = g := (Finset.mem_filter.mp hlg).2
    exact Finset.mem_filter.mpr
      ⟨C.parallel_pencil_line_is_represented hvalid hrho hoccupancy
        B hlabels hcover g hbudget l hdir hnotdel, hdir⟩
  calc
    Fintype.card F - 3 = ((linesInDirection g) \ C.deletedLines).card :=
      (C.parallel_nondeleted_card hvalid hcompatible g).symm
    _ ≤ ((B.biUnion C.coreRepresentative).filter
        (fun l => ThroughProjective l (Sum.inr g))).card := Finset.card_le_card hsubset
    _ ≤ (B.filter (C.RepresentedThrough (Sum.inr g))).card :=
      C.pencil_representatives_card_le_labels B (Sum.inr g)

theorem parallel_pencil_remaining_labels_le_three (hvalid : C.Valid)
    (hcompatible : C.Compatible) {rho : ℝ} {cap : ℕ}
    (hrho : 0 < rho) (hoccupancy : C.Occupancy rho cap)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (g : Direction F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) :
    (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card ≤ 3 := by
  have hforced := C.parallel_pencil_forced_label_count hvalid hcompatible hrho
    hoccupancy B hlabels hcover g hbudget
  have hsum := Finset.card_filter_add_card_filter_not
    (s := B) (p := C.RepresentedThrough (Sum.inr g))
  omega

end Configuration
end
end Balanced

end OAI
