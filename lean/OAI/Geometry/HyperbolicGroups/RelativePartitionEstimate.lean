import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualPartition
import OAI.Geometry.HyperbolicGroups.RelativePartition
import OAI.Geometry.HyperbolicGroups.RelativeFragment

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma actual_boundary_card (select : P.Face → Bool) :
    actualBoundary n w d ell hell word c hc f P select =
      Fintype.card {x : P.Dart // select (P.faceClass x) = true ∧
        select (P.faceClass (P.pairing.edge x)) ≠ true} := by
  rw [actualBoundary,← Fintype.card_sum]
  let g : ActualRawBoundary n w d ell hell word c hc f P select ⊕ RadialBoundarySide n w d ell hell word c hc f P select →
      {x : P.Dart // select (P.faceClass x) = true ∧ select (P.faceClass (P.pairing.edge x)) ≠ true} :=
    Sum.elim (fun x => ⟨x.val,x.property.2⟩) (fun x => ⟨x.val,x.property.2⟩)
  apply Fintype.card_congr (Equiv.ofBijective g ?_)
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext he)
    · have hx := x.property.1
      have hy := y.property.1
      change x.val = y.val at he
      dsimp only [rawDart] at hx
      dsimp only [walkRadial] at hy
      rw [he,hy] at hx
      cases hx
    · have hx := x.property.1
      have hy := y.property.1
      change x.val = y.val at he
      dsimp only [rawDart] at hy
      dsimp only [walkRadial] at hx
      rw [he,hy] at hx
      cases hx
    · exact congrArg Sum.inr (Subtype.ext he)
  · rintro ⟨x,hx,he⟩
    cases hr : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) with
    | false => exact ⟨.inr ⟨x,hr,hx,he⟩,rfl⟩
    | true => exact ⟨.inl ⟨x,hr,hx,he⟩,rfl⟩

end

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open scoped BigOperators
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

/-- Literal interior cells: the exterior cell kind is not selected. -/
def Interior (F : P.Face) : Prop := ∃ k, P.faceKind F = .inl k
abbrev InteriorFace := {F : P.Face // Interior n w d ell hell word c hc f P F}
instance : Fintype (InteriorFace n w d ell hell word c hc f P) := Fintype.ofFinite _

lemma interior_iff (x : P.Dart) : Interior n w d ell hell word c hc f P (P.faceClass x) ↔
    ¬ (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
      (letterWordClosed n w ell word) (P.index x) := by
  change (∃ k, (target n w d ell hell word c hc f).kind (P.index x) = .inl k) ↔ _
  cases hi : P.index x with
  | inl s =>
    change (∃ k, (Sum.inl (walkKind n w d s) : WalkKind n w d ⊕ Unit) = .inl k) ↔ ¬ False
    exact ⟨fun _ => not_false,fun _ => ⟨_,rfl⟩⟩
  | inr s =>
    change (∃ k, (Sum.inr () : WalkKind n w d ⊕ Unit) = .inl k) ↔ ¬ True
    simp only [Sum.inr_ne_inl,exists_false,not_true]

variable {I : Type*} (part : P.Face → I)
def partSelect (i : I) (F : P.Face) : Bool :=
  decide (Interior n w d ell hell word c hc f P F ∧ part F = i)

lemma part_interior (i : I) : InteriorSelection n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i) := by
  intro F hF
  exact (of_decide_eq_true hF).1

lemma part_area (i : I) : actualArea n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i) =
    Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} := by
  apply Fintype.card_congr
  exact {
    toFun := fun F => ⟨⟨F.val,(of_decide_eq_true F.property).1⟩,(of_decide_eq_true F.property).2⟩
    invFun := fun F => ⟨F.val.val,decide_eq_true ⟨F.val.property,F.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma part_boundary (i : I) : actualBoundary n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i) =
    Fintype.card (RelativePartBoundary P.pairing
      (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass) i) := by
  rw [actual_boundary_card]
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro x
  simp only [partSelect,ne_eq,decide_eq_true_eq,Function.comp_apply]
  tauto

variable [Fintype I]

lemma sum_part_area : (∑ i, actualArea n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i)) =
    Fintype.card (InteriorFace n w d ell hell word c hc f P) := by
  simp only [part_area]
  exact sum_part_sizes (fun F : InteriorFace n w d ell hell word c hc f P => part F.val)

lemma sum_part_boundary : (∑ i, actualBoundary n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i)) =
    Fintype.card (OutsideContact P.pairing (Interior n w d ell hell word c hc f P ∘ P.faceClass)) +
      2 * Fintype.card (RelativeCutContact P.pairing
        (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) := by
  simp only [part_boundary]
  exact sum_relative_part_boundary P.pairing _ _

/-- The genuine relative summation identity applied to all small fragments.
This does NOT assume that a low-cut partition exists. -/
theorem actual_partition_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ M) :
    defectConstant α β δ * Fintype.card (InteriorFace n w d ell hell word c hc f P) ≤
      (Fintype.card (OutsideContact P.pairing (Interior n w d ell hell word c hc f P ∘ P.faceClass)) : ℝ) +
      2 * Fintype.card (RelativeCutContact P.pairing
        (Interior n w d ell hell word c hc f P ∘ P.faceClass) (part ∘ P.faceClass)) := by
  have hi (i : I) := actual_fragment_bound n w d ell hell word c hc f P
    (partSelect n w d ell hell word c hc f P part i)
    (part_interior n w d ell hell word c hc f P part i) hs hm hred hrad ha hgood hb
    (by rw [part_area]; exact hM i)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hi i)
  rw [← Finset.mul_sum,← Nat.cast_sum,← Nat.cast_sum,sum_part_area,sum_part_boundary] at h
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using h

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
