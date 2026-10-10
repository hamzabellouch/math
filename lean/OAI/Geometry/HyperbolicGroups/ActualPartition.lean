import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualFragment
import OAI.Geometry.HyperbolicGroups.PicturePartition

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma actual_boundary_card (select : P.Face → Bool) :
    actualBoundary n w d c hc f P select =
      Fintype.card {x : P.Dart // select (P.faceClass x) = true ∧
        select (P.faceClass (P.pairing.edge x)) ≠ true} := by
  rw [actualBoundary,← Fintype.card_sum]
  let g : ActualRawBoundary n w d c hc f P select ⊕ RadialBoundarySide n w d c hc f P select →
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
    cases hr : isLetter n w (walkLabel n w d (P.index x)) with
    | false => exact ⟨.inr ⟨x,hr,hx,he⟩,rfl⟩
    | true => exact ⟨.inl ⟨x,hr,hx,he⟩,rfl⟩

variable {I : Type*} [Fintype I] (part : P.Face → I)

def partSelect (i : I) (F : P.Face) : Bool := decide (part F = i)

omit [Fintype I] in
lemma part_area (i : I) : actualArea n w d c hc f P (partSelect n w d c hc f P part i) =
    Fintype.card {F : P.Face // part F = i} := by
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro F
  simp only [partSelect,decide_eq_true_eq]

omit [Fintype I] in
lemma part_boundary (i : I) : actualBoundary n w d c hc f P (partSelect n w d c hc f P part i) =
    Fintype.card (PartBoundary P.pairing (part ∘ P.faceClass) i) := by
  rw [actual_boundary_card]
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro x
  simp [partSelect,Function.comp_apply]

lemma sum_part_area : (∑ i, actualArea n w d c hc f P (partSelect n w d c hc f P part i)) =
    Fintype.card P.Face := by
  simp only [part_area]
  exact sum_part_sizes part

lemma sum_part_boundary : (∑ i, actualBoundary n w d c hc f P (partSelect n w d c hc f P part i)) =
    2 * Fintype.card (CutContact P.pairing (part ∘ P.faceClass)) := by
  simp only [part_boundary]
  exact (PictureSwitch.sum_part_boundary P.pairing (part ∘ P.faceClass)).trans
    (cut_sides_twice P.pairing (part ∘ P.faceClass))

/-- Summing fragment bounds over a partition of faces bounds the total defect
by twice the number of cut contacts. -/
theorem actual_partition_bound {M : ℕ} {α β δ : ℝ} (ha : 0 ≤ α)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : ∀ i, 8 * Fintype.card {F : P.Face // part F = i} ≤ M) :
    defectConstant α β δ * Fintype.card P.Face ≤
      2 * (Fintype.card (CutContact P.pairing (part ∘ P.faceClass)) : ℝ) := by
  have hi (i : I) := actual_fragment_bound n w d c hc f P (partSelect n w d c hc f P part i)
    hs hm hred hrad ha hgood hb (by rw [part_area]; exact hM i)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hi i)
  rw [← Finset.mul_sum,← Nat.cast_sum,← Nat.cast_sum,sum_part_area,sum_part_boundary] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

end HyperbolicObstruction.ConeSkeleton
end

end OAI
