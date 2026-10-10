import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionAssembly
import OAI.Computability.PerfectCompleteness.Foundations.CutSlotOutside

namespace OAI

section

namespace PerfectCompleteness.CutProjectionGeometry

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem sourceProjection_eq_cast
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hs : slots = projected)
    (hk : ∀ s k, HEq (q s k) (MixedSupport.Projection.keep (slots s k)))
    (x : Domain slots) :
    sourceProjection q x = cast (congrArg Domain hs) x := by
  cases hs
  have hq : q = fun s k => MixedSupport.Projection.keep (slots s k) := by
    funext s k
    exact eq_of_heq (hk s k)
  subst q
  rfl

theorem HPullback_eq_cast
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hs : slots = projected)
    (hk : ∀ s k, HEq (q s k) (MixedSupport.Projection.keep (slots s k)))
    (f : H projected) :
    HPullback q f = cast (congrArg
      (fun ss : Slots branch n → Fin t → MixedSupport.Slot => (H ss : Type)) hs.symm) f := by
  cases hs
  have hq : q = fun s k => MixedSupport.Projection.keep (slots s k) := by
    funext s k
    exact eq_of_heq (hk s k)
  subst q
  apply Subtype.ext
  rfl

theorem squarePullback_eq_cast
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hs : slots = projected)
    (hk : ∀ s k, HEq (q s k) (MixedSupport.Projection.keep (slots s k)))
    (f : squareSpace (H projected)) :
    ChildBlockProjection.squarePullback q f = cast (congrArg
      (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
        (squareSpace (H ss) : Type)) hs.symm) f := by
  cases hs
  have hq : q = fun s k => MixedSupport.Projection.keep (slots s k) := by
    funext s k
    exact eq_of_heq (hk s k)
  subst q
  apply Subtype.ext
  rfl

theorem arraysPullback_eq_cast (rows : Nat → Nat)
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hs : slots = projected)
    (hk : ∀ s k, HEq (q s k) (MixedSupport.Projection.keep (slots s k)))
    (arrays : Arrays projected rows) :
    ChildBlockProjection.arraysPullback rows q arrays = cast (congrArg
      (fun ss : Slots branch n → Fin t → MixedSupport.Slot => Arrays ss rows) hs.symm) arrays := by
  cases hs
  have hq : q = fun s k => MixedSupport.Projection.keep (slots s k) := by
    funext s k
    exact eq_of_heq (hk s k)
  subst q
  funext node row
  apply Subtype.ext
  rfl

theorem rawPullback_eq_cast (calls : Nat) (rows : Nat → Nat)
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hs : slots = projected)
    (hk : ∀ s k, HEq (q s k) (MixedSupport.Projection.keep (slots s k)))
    (block : ChildBlockCardinality.Raw calls rows projected) :
    ChildBlockProjection.rawPullback calls rows q block = cast (congrArg
      (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
        ChildBlockCardinality.Raw calls rows ss) hs.symm) block := by
  cases hs
  have hq : q = fun s k => MixedSupport.Projection.keep (slots s k) := by
    funext s k
    exact eq_of_heq (hk s k)
  subst q
  apply Prod.ext
  · funext call
    apply Subtype.ext
    rfl
  · funext node row
    apply Subtype.ext
    rfl

theorem childPullback_heq {C : Type*} [Fintype C] (rows : Nat → Nat)
    {left right left' right' : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (hL : left = left') (hR : right = right')
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (q' : ∀ s k, MixedSupport.Projection (left' s k) (right' s k))
    (hq : ∀ s k, HEq (q s k) (q' s k)) (i : Fin (branch n))
    (block : CutChildGrouping.Child (C := C) right rows i)
    (block' : CutChildGrouping.Child (C := C) right' rows i)
    (hb : HEq block block') :
    HEq (ChildAssemblyProjection.childPullback rows q i block)
      (ChildAssemblyProjection.childPullback rows q' i block') := by
  cases hL
  cases hR
  have hqq' : q = q' := by
    funext s k
    exact eq_of_heq (hq s k)
  cases hqq'
  have hbb' : block = block' := eq_of_heq hb
  cases hbb'
  rfl

private theorem keep_heq {a b : MixedSupport.Slot} (h : a = b) :
    HEq (MixedSupport.Projection.keep a) (MixedSupport.Projection.keep b) := by
  cases h
  rfl

theorem fillProjection_outside {m : Nat} (p : Path branch n m)
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch m → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (s : Slots branch n) (hout : s ∉ Set.range p.slotEmbedding) (k : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q s k)
      (MixedSupport.Projection.keep (CutSlotAssembly.fill p outside left s k)) := by
  revert outside left right q s hout k
  induction p with
  | refl _ =>
      intro outside left right q s hout k
      exact False.elim (hout ⟨s, rfl⟩)
  | step i p ih =>
      intro outside left right q s hout k
      obtain ⟨j, s⟩ := s
      by_cases hji : j = i
      · subst j
        have htail : s ∉ Set.range p.slotEmbedding := by
          rintro ⟨a, ha⟩
          exact hout ⟨a, congrArg (fun b => (i, b)) ha⟩
        have hfill : CutSlotAssembly.fill (.step i p) outside left (i, s) =
            CutSlotAssembly.fill p (fun b => outside (i, b)) left s :=
          ite_eq_left (show i = i from rfl)
        simp only [CutProjectionAssembly.fillProjection]
        exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
          ((ih (fun b => outside (i, b)) left right q s htail k).trans
            (keep_heq (congrFun hfill k).symm))
      · have hfill : CutSlotAssembly.fill (.step i p) outside left (j, s) = outside (j, s) :=
          ite_eq_right hji
        simp only [CutProjectionAssembly.fillProjection, dite_eq_right hji]
        exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
          (keep_heq (congrFun hfill k).symm)

end
end PerfectCompleteness.CutProjectionGeometry

end

end OAI
