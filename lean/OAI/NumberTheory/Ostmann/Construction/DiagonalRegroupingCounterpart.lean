import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceVariables
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRootCounterpart
import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingMatching
import OAI.NumberTheory.Ostmann.Construction.TemplateLabels

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Arithmetic Arithmetic.HistoryOccurrenceVariables

theorem reinsert_role_filters (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot)
    (hu : Template.Matches (Template.extracted j T) u)
    (hh : Template.Matches (Template.remainder j T) h) :
    (Template.reinsert j T u h).filter (fun a => decide (a.role=.compensation j))=u ∧
    (Template.reinsert j T u h).filter (fun a => decide (a.role≠.compensation j))=h := by
  induction T generalizing u h with
  | nil =>
    have hu0 : u=[] := List.length_eq_zero_iff.mp (by simpa [Template.extracted] using Template.matches_length hu)
    have hh0 : h=[] := List.length_eq_zero_iff.mp (by simpa [Template.remainder] using Template.matches_length hh)
    subst u; subst h
    simp [Template.reinsert]
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · cases u with
      | nil => simp [Template.Matches,Template.extracted,hq] at hu
      | cons a u =>
        have hu' : (a.role,a.origin)=(q.role,q.origin) ∧ Template.Matches (Template.extracted j T) u := by
          simpa [Template.Matches,Template.extracted,hq] using hu
        have hh' : Template.Matches (Template.remainder j T) h := by
          simpa [Template.Matches,Template.remainder,hq] using hh
        have ha : a.role=.compensation j := (congrArg Prod.fst hu'.1).trans hq
        simpa [Template.reinsert,hq,ha] using ih u h hu'.2 hh'
    · cases h with
      | nil => simp [Template.Matches,Template.remainder,hq] at hh
      | cons a h =>
        have hu' : Template.Matches (Template.extracted j T) u := by
          simpa [Template.Matches,Template.extracted,hq] using hu
        have hh' : (a.role,a.origin)=(q.role,q.origin) ∧ Template.Matches (Template.remainder j T) h := by
          simpa [Template.Matches,Template.remainder,hq] using hh
        have ha : a.role≠.compensation j := by
          exact fun he => hq ((congrArg Prod.fst hh'.1).symm.trans he)
        simpa [Template.reinsert,hq,ha] using ih u h hu' hh'.2

def diagonalRoleKeys {l : ℕ} (h : History l) (pred : SmallSlot→Bool) : List (Key h) :=
  ((List.finRange h.root.small.length).filter (fun i => pred (h.root.small.get i))).map
    (fun i => Sum.inr (Sum.inl i))

def diagonalHKeys {l : ℕ} (h : History l) (j : ℕ) : List (Key h) :=
  Sum.inl true :: diagonalRoleKeys h (fun q => decide (q.role≠.compensation j))

def diagonalUKeys {l : ℕ} (h : History l) (j : ℕ) : List (Key h) :=
  diagonalRoleKeys h (fun q => decide (q.role=.compensation j))

theorem diagonalRoleKeys_sample {l : ℕ} (h : History l) (pred : SmallSlot→Bool) :
    (diagonalRoleKeys h pred).map (fun i => (integerSample h i:ℝ))=
      (h.root.small.filter pred).map (fun q => (q.value:ℝ)) := by
  have he : (List.finRange h.root.small.length).map h.root.small.get=h.root.small := by
    simpa only [←List.ofFn_eq_map] using List.ofFn_get h.root.small
  conv_rhs => rw [←he]
  simp only [diagonalRoleKeys,List.filter_map,List.map_map]
  rfl

theorem diagonalHKeys_product {l : ℕ} (h : History l)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : h.root=remainingState sources T j giant p u x v) :
    ((diagonalHKeys h j).map (fun i => (integerSample h i:ℝ))).prod=
      (remainingProduct sources (Template.remainder j T) giant x:ℝ) := by
  simp only [diagonalHKeys,List.map_cons,List.prod_cons,diagonalRoleKeys_sample]
  simp only [integerSample,Int.cast_natCast]
  rw [hroot]
  change (x.1.val:ℝ)*((Template.reinsert j T _ _).filter _ |>.map (fun q => (q.value:ℝ))).prod=_
  rw [(reinsert_role_filters j T _ _ (Template.assignedSlots_matches _ _ u)
    (Template.assignedSlots_matches _ _ x.2)).2]
  simp only [remainingProduct,halfProduct,Nat.cast_mul,Nat.cast_list_prod,List.map_map,Function.comp_def]

theorem diagonalUKeys_product {l : ℕ} (h : History l)
    (sources : SourceFamily) (T : List SourceSlot) (j : ℕ) (giant : PrimeSource) (p : ℕ)
    (u : SourceAssignment sources (Template.extracted j T))
    (x : RemainingSample sources (Template.remainder j T) giant) (v : ℤ)
    (hroot : h.root=remainingState sources T j giant p u x v) :
    ((diagonalUKeys h j).map (fun i => (integerSample h i:ℝ))).prod=
      (((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod:ℝ) := by
  rw [diagonalUKeys,diagonalRoleKeys_sample,hroot]
  change ((Template.reinsert j T _ _).filter _ |>.map (fun q => (q.value:ℝ))).prod=_
  rw [(reinsert_role_filters j T _ _ (Template.assignedSlots_matches _ _ u)
    (Template.assignedSlots_matches _ _ x.2)).1]
  simp only [Nat.cast_list_prod,List.map_map,Function.comp_def]

end Ostmann.Construction

end

end OAI
