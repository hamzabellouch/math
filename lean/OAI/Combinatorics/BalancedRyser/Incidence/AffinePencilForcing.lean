import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.PencilOccupancy
import OAI.Combinatorics.BalancedRyser.Probability.CoreRepresentatives
import OAI.Combinatorics.BalancedRyser.Probability.SizeThreshold

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[simp] private lemma mem_linePoints_iff (p : Point F) (l : Line F) :
    p ∈ linePoints l ↔ OnLine p l := by simp [linePoints]

lemma distinct_line_intersection_card_le_one (l m : Line F) (hne : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  exact common_point_eq_of_lines_ne l m hne p r
    (mem_linePoints_iff p l |>.mp (Finset.mem_inter.mp hp).1)
    (mem_linePoints_iff p m |>.mp (Finset.mem_inter.mp hp).2)
    (mem_linePoints_iff r l |>.mp (Finset.mem_inter.mp hr).1)
    (mem_linePoints_iff r m |>.mp (Finset.mem_inter.mp hr).2)

lemma pencil_line_trace_subset_point (l m : Line F) (hne : l ≠ m)
    (p : Point F) (hpl : OnLine p l) (hpm : OnLine p m) :
    linePoints m ∩ linePoints l ⊆ {p} := by
  intro r hr
  apply Finset.mem_singleton.mpr
  exact common_point_eq_of_lines_ne l m hne r p
    (mem_linePoints_iff r l |>.mp (Finset.mem_inter.mp hr).2)
    (mem_linePoints_iff r m |>.mp (Finset.mem_inter.mp hr).1) hpl hpm

theorem missing_pencil_line_occupancy_bound (L : Finset (Line F))
    (U : Finset (Point F)) (hcover : CoversPoints L U)
    (p : Point F) (l : Line F) (hpl : OnLine p l) (homit : l ∉ L) :
    (linePoints l ∩ U).card ≤ 1 + (L.filter (fun m => ¬ OnLine p m)).card := by
  classical
  apply affine_pencil_cover_card_bound (linePoints l ∩ U) p
    (L.filter (OnLine p)) linePoints (L.filter (fun m => ¬ OnLine p m)) linePoints
  · intro x hx
    obtain ⟨m, hm, hxm⟩ := hcover x (Finset.mem_inter.mp hx).2
    by_cases hpm : OnLine p m
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_filter.mpr ⟨hm, hpm⟩, (mem_linePoints_iff x m).mpr hxm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_filter.mpr ⟨hm, hpm⟩, (mem_linePoints_iff x m).mpr hxm⟩)
  · intro m hm x hx
    have hml : l ≠ m := by intro he; subst m; exact homit (Finset.mem_filter.mp hm).1
    apply pencil_line_trace_subset_point l m hml p hpl (Finset.mem_filter.mp hm).2
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
  · intro m hm
    have hml : l ≠ m := by intro he; subst m; exact homit (Finset.mem_filter.mp hm).1
    calc
      (linePoints m ∩ (linePoints l ∩ U)).card ≤ (linePoints l ∩ linePoints m).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1, (Finset.mem_inter.mp hx).1⟩
      _ ≤ 1 := distinct_line_intersection_card_le_one l m hml

namespace Configuration

variable (C : Configuration F)

theorem ordinary_pencil_line_is_represented (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hoccupancy : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (l : Line F) (hpl : OnLine p l) (hnotdel : l ∉ C.deletedLines) :
    l ∈ B.biUnion C.coreRepresentative := by
  classical
  by_contra homit
  have hcoreCover := (C.core_cover_reduction hvalid B hlabels hcover).2.2
  have hmissing := missing_pencil_line_occupancy_bound
    (B.biUnion C.coreRepresentative) C.core hcoreCover p l hpl homit
  have houtside := C.outside_pencil_representatives_card_le_labels B (Sum.inl p)
  have houtside' :
      ((B.biUnion C.coreRepresentative).filter (fun m => ¬ OnLine p m)).card ≤
      (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card := by
    apply le_trans (Finset.card_le_card ?_) houtside
    intro representative hrepresentative
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hrepresentative).1, (Finset.mem_filter.mp hrepresentative).2⟩
  have hmissingReal : ((linePoints l ∩ C.core).card : ℝ) ≤
      1 + ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) := by
    exact_mod_cast hmissing.trans (Nat.add_le_add_left houtside' 1)
  have hgap := ordinary_pencil_gap (Nat.cast_nonneg cap) hsize hbudget
  have hocc := hoccupancy.2.1 l hnotdel
  linarith

end Configuration

end
end Balanced

end OAI
