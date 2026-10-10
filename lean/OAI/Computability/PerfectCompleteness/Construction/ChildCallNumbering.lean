import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Decoding.ChildBlockProjection

namespace OAI

section

namespace PerfectCompleteness.ChildCallNumbering

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {C : Type*} [Fintype C] {branch : Nat → Nat} {n t : Nat}

abbrev Raw (rows : Nat → Nat) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  (C → squareSpace (H slots)) × Arrays slots rows

instance rawFintype (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Raw (C := C) rows slots) := Fintype.ofFinite _

instance rawNonempty (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Raw (C := C) rows slots) := ⟨(fun _ => 0, fun _ _ => 0)⟩

def equiv (rows : Nat → Nat) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Raw (C := C) rows slots ≃ₗ[F2]
      ChildBlockCardinality.Raw (Fintype.card C) rows slots where
  toFun x := (fun k => x.1 ((Fintype.equivFin C).symm k), x.2)
  invFun x := (fun c => x.1 (Fintype.equivFin C c), x.2)
  left_inv x := by
    apply Prod.ext
    · funext c
      simp only [Equiv.symm_apply_apply]
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext k
      simp only [Equiv.apply_symm_apply]
    · rfl
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp] theorem equiv_calls (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : Raw (C := C) rows slots) (k : Fin (Fintype.card C)) :
    (equiv rows slots x).1 k = x.1 ((Fintype.equivFin C).symm k) := rfl

@[simp] theorem equiv_arrays (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : Raw (C := C) rows slots) : (equiv rows slots x).2 = x.2 := rfl

@[simp] theorem equiv_symm_calls (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : ChildBlockCardinality.Raw (Fintype.card C) rows slots) (c : C) :
    ((equiv (C := C) rows slots).symm x).1 c = x.1 (Fintype.equivFin C c) := rfl

@[simp] theorem equiv_symm_arrays (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : ChildBlockCardinality.Raw (Fintype.card C) rows slots) :
    ((equiv (C := C) rows slots).symm x).2 = x.2 := rfl

def pullback (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Raw (C := C) rows projected →ₗ[F2] Raw (C := C) rows slots where
  toFun x := (fun c => ChildBlockProjection.squarePullback p (x.1 c),
    ChildBlockProjection.arraysPullback rows p x.2)
  map_add' x y := by
    apply Prod.ext
    · funext c
      exact map_add (ChildBlockProjection.squarePullback p) (x.1 c) (y.1 c)
    · exact map_add (ChildBlockProjection.arraysPullback rows p) x.2 y.2
  map_smul' a x := by
    apply Prod.ext
    · funext c
      exact map_smul (ChildBlockProjection.squarePullback p) a (x.1 c)
    · exact map_smul (ChildBlockProjection.arraysPullback rows p) a x.2

omit [Fintype C] in
@[simp] theorem pullback_calls (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Raw (C := C) rows projected) (c : C) :
    (pullback rows p x).1 c = ChildBlockProjection.squarePullback p (x.1 c) := rfl

omit [Fintype C] in
@[simp] theorem pullback_arrays (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Raw (C := C) rows projected) :
    (pullback rows p x).2 = ChildBlockProjection.arraysPullback rows p x.2 := rfl

theorem equiv_pullback (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Raw (C := C) rows projected) :
    equiv rows slots (pullback rows p x) =
      ChildBlockProjection.rawPullback (Fintype.card C) rows p
        (equiv rows projected x) := rfl

omit [Fintype C] in
theorem pullback_cast (rows : Nat → Nat)
    {slots target projected : Slots branch n → Fin t → MixedSupport.Slot}
    (h : slots = target)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Raw (C := C) rows projected) :
    cast (congrArg (Raw (C := C) rows) h) (pullback rows p x) =
      pullback rows
        (cast (congrArg
          (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
            ∀ s k, MixedSupport.Projection (ss s k) (projected s k)) h) p) x := by
  cases h
  rfl

theorem uniform_equiv (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (Raw (C := C) rows slots)).pushforward
        (equiv (C := C) rows slots) =
      FiniteDistribution.uniform (ChildBlockCardinality.Raw (Fintype.card C) rows slots) :=
  UniformLinearImage.uniform_pushforward_linearMap
    (equiv (C := C) rows slots).toLinearMap (equiv (C := C) rows slots).surjective

theorem card_le (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype.card (Raw (C := C) rows slots) ≤
      ChildBlockCardinality.bound branch n t (Fintype.card C) rows := by
  calc
    Fintype.card (Raw (C := C) rows slots) =
        Fintype.card (ChildBlockCardinality.Raw (Fintype.card C) rows slots) :=
      Fintype.card_congr (equiv (C := C) rows slots).toEquiv
    _ ≤ _ := by
      simpa only [Nat.card_eq_fintype_card] using
        ChildBlockCardinality.card_le (Fintype.card C) rows slots

end
end PerfectCompleteness.ChildCallNumbering

end

end OAI
