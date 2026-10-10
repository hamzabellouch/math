import OAI.Computability.PerfectCompleteness.Construction.CutChildGrouping
import OAI.Computability.PerfectCompleteness.Decoding.ChildBlockProjection

namespace OAI

section

namespace PerfectCompleteness.ChildAssemblyProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}

def childProjection
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) :
    ∀ s k, MixedSupport.Projection (childSlots slots i s k) (childSlots projected i s k) :=
  fun s k => p (i, s) k

theorem restrictChild_projection
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) (x : Domain slots) :
    sourceProjection (childProjection p i) (restrictChild slots i x) =
      restrictChild projected i (sourceProjection p x) := rfl

theorem recursiveSum_pullback
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (f : (i : Fin (branch n)) → squareSpace (H (childSlots projected i))) :
    UniformChildSum.recursiveSum (LeafDomain slots)
        (fun i => ChildBlockProjection.squarePullback (childProjection p i) (f i)) =
      HPullback p (UniformChildSum.recursiveSum (LeafDomain projected) f) := by
  apply Subtype.ext
  change (∑ i, PointwiseSpaces.pullback F2 (childRestriction (LeafDomain slots) i)
      (ChildBlockProjection.squarePullback (childProjection p i) (f i)).val) =
    PointwiseSpaces.pullback F2 (sourceProjection p)
      (∑ i, PointwiseSpaces.pullback F2 (childRestriction (LeafDomain projected) i) (f i).val)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

variable {C : Type*} [Fintype C]

def childPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) :
    CutChildGrouping.Child (C := C) projected rows i →ₗ[F2]
      CutChildGrouping.Child (C := C) slots rows i where
  toFun block :=
    (fun call => ChildBlockProjection.squarePullback (childProjection p i) (block.1 call),
      ChildBlockProjection.arraysPullback rows (childProjection p i) block.2)
  map_add' a b := by
    apply Prod.ext
    · funext call
      exact map_add (ChildBlockProjection.squarePullback (childProjection p i))
        (a.1 call) (b.1 call)
    · exact map_add (ChildBlockProjection.arraysPullback rows (childProjection p i)) a.2 b.2
  map_smul' c a := by
    apply Prod.ext
    · funext call
      exact map_smul (ChildBlockProjection.squarePullback (childProjection p i)) c (a.1 call)
    · exact map_smul (ChildBlockProjection.arraysPullback rows (childProjection p i)) c a.2

theorem childPullback_fin (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) :
    childPullback (C := Fin calls) rows p i =
      ChildBlockProjection.rawPullback calls rows (childProjection p i) := rfl

def rawPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    CutChildGrouping.Raw (C := C) projected rows →ₗ[F2]
      CutChildGrouping.Raw (C := C) slots rows where
  toFun block i := childPullback rows p i (block i)
  map_add' a b := by
    funext i
    exact map_add (childPullback rows p i) (a i) (b i)
  map_smul' c a := by
    funext i
    exact map_smul (childPullback rows p i) c (a i)

def assembledPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    CutChildGrouping.Assembled (C := C) projected rows →ₗ[F2]
      CutChildGrouping.Assembled (C := C) slots rows where
  toFun z := (fun call => HPullback p (z.1 call),
    fun i => ChildBlockProjection.arraysPullback rows (childProjection p i) (z.2 i))
  map_add' a b := by
    apply Prod.ext
    · funext call
      exact map_add (HPullback p) (a.1 call) (b.1 call)
    · funext i
      exact map_add (ChildBlockProjection.arraysPullback rows (childProjection p i)) (a.2 i) (b.2 i)
  map_smul' c a := by
    apply Prod.ext
    · funext call
      exact map_smul (HPullback p) c (a.1 call)
    · funext i
      exact map_smul (ChildBlockProjection.arraysPullback rows (childProjection p i)) c (a.2 i)

omit [Fintype C] in
theorem assemble_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (block : CutChildGrouping.Raw (C := C) projected rows) :
    CutChildGrouping.assemble slots rows (rawPullback rows p block) =
      assembledPullback rows p (CutChildGrouping.assemble projected rows block) := by
  apply Prod.ext
  · funext call
    exact recursiveSum_pullback p (fun i => (block i).1 call)
  · rfl

omit [Fintype C] in
theorem assemble_comp_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    (CutChildGrouping.assemble (C := C) slots rows).comp (rawPullback rows p) =
      (assembledPullback rows p).comp (CutChildGrouping.assemble projected rows) := by
  apply LinearMap.ext
  intro block
  exact assemble_pullback rows p block

def evaluate {rows : Nat → Nat}
    (z : CutChildGrouping.Assembled (C := C) slots rows) (x : Domain slots) :
    (C → F2) × (Fin (branch n) → Output branch n rows) :=
  (fun call => (z.1 call).val x,
    fun i => fullJoint (z.2 i) (restrictChild slots i x))

omit [Fintype C] in
theorem evaluate_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (z : CutChildGrouping.Assembled (C := C) projected rows) (x : Domain slots) :
    evaluate (assembledPullback rows p z) x = evaluate z (sourceProjection p x) := rfl

omit [Fintype C] in
theorem evaluate_assemble_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (block : CutChildGrouping.Raw (C := C) projected rows) (x : Domain slots) :
    evaluate (CutChildGrouping.assemble slots rows (rawPullback rows p block)) x =
      evaluate (CutChildGrouping.assemble projected rows block) (sourceProjection p x) := by
  rw [assemble_pullback]
  exact evaluate_pullback rows p _ x

theorem pushforward_assemble (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (μ : FiniteDistribution (CutChildGrouping.Raw (C := C) projected rows)) :
    (μ.pushforward (rawPullback rows p)).pushforward (CutChildGrouping.assemble slots rows) =
      (μ.pushforward (CutChildGrouping.assemble projected rows)).pushforward
        (assembledPullback rows p) := by
  rw [FiniteDistribution.pushforward_comp, FiniteDistribution.pushforward_comp]
  congr 1
  funext block
  exact assemble_pullback rows p block

theorem uniform_projected_assembly (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    ((CutChildGrouping.rawLaw (C := C) projected rows).pushforward
        (rawPullback rows p)).pushforward (CutChildGrouping.assemble slots rows) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := C) projected rows)).pushforward
        (assembledPullback rows p) := by
  rw [pushforward_assemble, CutChildGrouping.assemble_law]

end
end PerfectCompleteness.ChildAssemblyProjection

end

end OAI
