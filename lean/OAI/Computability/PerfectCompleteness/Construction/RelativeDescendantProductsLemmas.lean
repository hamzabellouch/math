import OAI.Computability.PerfectCompleteness.Construction.DescendantSpacesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GeometricPathLemmas

namespace OAI


namespace PerfectCompleteness.RelativeDescendantProducts

open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}

inductive Below (branch : Nat → Nat) :
    {n : Nat} → Nodes branch n → Nodes branch n → Prop
  | root {n : Nat} (i : Fin (branch n)) (lower : Nodes branch n) :
      Below branch (n := n + 1) (.inl ()) (.inr (i, lower))
  | child {n : Nat} {upper lower : Nodes branch n} (i : Fin (branch n)) :
      Below branch upper lower →
        Below branch (n := n + 1) (.inr (i, upper)) (.inr (i, lower))

theorem Below.height_lt {upper lower : Nodes branch n}
    (h : Below branch upper lower) : Nodes.height lower < Nodes.height upper := by
  induction h with
  | root i lower => exact Nat.lt_succ_of_le (Nodes.height_le lower)
  | child i h ih => exact ih

theorem Below.ne {upper lower : Nodes branch n}
    (h : Below branch upper lower) : lower ≠ upper := by
  intro heq
  have hlt := h.height_lt
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

def relativeNode : {n : Nat} → (upper : Nodes branch n) →
    Nodes branch (Nodes.height upper) → Nodes branch n
  | 0, upper, _ => nomatch upper
  | _ + 1, .inl _, lower => lower
  | _ + 1, .inr (i, upper), lower => .inr (i, relativeNode upper lower)

theorem relativeNode_height : ∀ {n : Nat} (upper : Nodes branch n)
    (lower : Nodes branch (Nodes.height upper)),
    Nodes.height (relativeNode upper lower) = Nodes.height lower := by
  intro n
  induction n with
  | zero => intro upper; exact nomatch upper
  | succ n ih =>
      intro upper lower
      cases upper with
      | inl _ => rfl
      | inr pair => exact ih pair.2 lower

theorem relativeNode_injective : ∀ {n : Nat} (upper : Nodes branch n),
    Function.Injective (relativeNode upper) := by
  intro n
  induction n with
  | zero => intro upper; exact nomatch upper
  | succ n ih =>
      intro upper
      cases upper with
      | inl _ => exact fun _ _ h => h
      | inr pair =>
          intro x y h
          exact ih pair.2 (congrArg Prod.snd (Sum.inr.inj h))

theorem relativeNode_below : ∀ {n : Nat} (upper : Nodes branch n)
    (lower : Nodes branch (Nodes.height upper)),
    Nodes.height lower < Nodes.height upper →
      Below branch upper (relativeNode upper lower) := by
  intro n
  induction n with
  | zero => intro upper; exact nomatch upper
  | succ n ih =>
      intro upper lower hproper
      cases upper with
      | inl u =>
          cases u
          cases lower with
          | inl _ => exact False.elim (Nat.lt_irrefl _ hproper)
          | inr pair => exact Below.root pair.1 pair.2
      | inr pair => exact Below.child pair.1 (ih pair.2 lower hproper)

abbrev RelativeDescendant (upper : Nodes branch n) :=
  {lower : Nodes branch (Nodes.height upper) // Nodes.height lower < Nodes.height upper}

def descendantIndex (upper : Nodes branch n) (lower : RelativeDescendant upper) :
    {j : Nodes branch n // j ≠ upper} :=
  ⟨relativeNode upper lower.val, (relativeNode_below upper lower.val lower.property).ne⟩

theorem descendantIndex_below (upper : Nodes branch n)
    (lower : RelativeDescendant upper) :
    Below branch upper (descendantIndex upper lower).val :=
  relativeNode_below upper lower.val lower.property

theorem descendantIndex_injective (upper : Nodes branch n) :
    Function.Injective (descendantIndex upper) := by
  intro x y h
  apply Subtype.ext
  exact relativeNode_injective upper
    (congrArg (fun z : {j : Nodes branch n // j ≠ upper} => z.val) h)

theorem pullback_square_exists {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    ∀ (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
      (_ : ∀ k < n, 0 < branch k)
      (f : Domain (nodeSlots slots lower) → F2),
      f ∈ PointwiseSpaces.squareSpace (NodeEmbedding.NodeH slots lower) →
        ∃ g ∈ NodeEmbedding.NodeH slots upper,
          PointwiseSpaces.pullback F2 (restrictNode slots upper) g =
            PointwiseSpaces.pullback F2 (restrictNode slots lower) f := by
  induction h with
  | @root n i lower =>
      intro slots hbranch f hf
      refine ⟨PointwiseSpaces.pullback F2 (restrictNode slots (.inr (i, lower))) f, ?_, rfl⟩
      exact DescendantSpaces.descendant_square_le_space
        (.step i (Nodes.path lower)) (LeafDomain slots) hbranch
        (Nat.lt_succ_of_le (Nodes.height_le lower)) (Submodule.mem_map_of_mem hf)
  | @child n upper lower i h ih =>
      intro slots hbranch f hf
      let childSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
        fun s => slots (i, s)
      have hb : ∀ k < n, 0 < branch k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      obtain ⟨g, hg, heq⟩ := ih childSlots hb f hf
      refine ⟨g, hg, ?_⟩
      exact congrArg
        (PointwiseSpaces.pullback F2 (RecursiveSpaces.childRestriction (LeafDomain slots) i)) heq

noncomputable section

theorem squareSpace_le_rowSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n, 0 < branch k) {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    PointwiseSpaces.squareSpace (NodeEmbedding.RowSpace slots lower) ≤
      NodeEmbedding.RowSpace slots upper := by
  rw [NodeEmbedding.squareSpace_eq]
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  obtain ⟨u, hu, heq⟩ := pullback_square_exists h slots hbranch g hg
  refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
  funext x
  exact congrFun heq ((TreeCanonical.assignmentEquiv slots).symm x)

theorem one_mem_rowSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n, 0 < branch k) (upper : Nodes branch n) :
    (1 : NodeEmbedding.NumberedDomain slots → F2) ∈ NodeEmbedding.RowSpace slots upper := by
  have hb : ∀ k < Nodes.height upper, 0 < branch k :=
    fun k hk => hbranch k (Nat.lt_of_lt_of_le hk (Nodes.height_le upper))
  exact Submodule.mem_map_of_mem (TreeSourceSpaces.one_mem_H (nodeSlots slots upper) hb)

variable {rows : Nat → Nat} {D : Type*}

theorem knownSpace_le_rowSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n, 0 < branch k) (upper : Nodes branch n)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (descendant : D → {j : Nodes branch n // j ≠ upper})
    (hbelow : ∀ d, Below branch upper (descendant d).val) :
    HierarchicalKnownRows.knownSpace slots upper background descendant ≤
      NodeEmbedding.RowSpace slots upper := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | ⟨d, i, j, rfl⟩
  · exact one_mem_rowSpace slots hbranch upper
  · have hi : PointwiseSpaces.pullback F2
          (NodeEmbedding.numberedRestriction slots (descendant d).val)
          (background (descendant d) i).val ∈ NodeEmbedding.RowSpace slots (descendant d).val :=
      Submodule.mem_map_of_mem (background (descendant d) i).property
    have hj : PointwiseSpaces.pullback F2
          (NodeEmbedding.numberedRestriction slots (descendant d).val)
          (background (descendant d) j).val ∈ NodeEmbedding.RowSpace slots (descendant d).val :=
      Submodule.mem_map_of_mem (background (descendant d) j).property
    exact squareSpace_le_rowSpace slots hbranch (hbelow d)
      (PointwiseSpaces.mul_mem_squareSpace _ hi hj)

theorem relative_knownSpace_le_rowSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n, 0 < branch k) (upper : Nodes branch n)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (descendant : D → RelativeDescendant upper) :
    HierarchicalKnownRows.knownSpace slots upper background
        (fun d => descendantIndex upper (descendant d)) ≤
      NodeEmbedding.RowSpace slots upper :=
  knownSpace_le_rowSpace slots hbranch upper background
    (fun d => descendantIndex upper (descendant d))
    (fun d => descendantIndex_below upper (descendant d))

end
end PerfectCompleteness.RelativeDescendantProducts



namespace PerfectCompleteness.GeometricDescendants

open TreeSourceSpaces HierarchicalArrays RelativeDescendantProducts

variable {branch : Nat → Nat}

theorem below_nodeAtLevel : ∀ {n : Nat} (leaf : RecursiveSpaces.Slots branch n)
    (upper lower : Fin n), lower < upper →
      Below branch (GeometricPath.nodeAtLevel leaf upper)
        (GeometricPath.nodeAtLevel leaf lower) := by
  intro n
  induction n with
  | zero => intro leaf upper; exact Fin.elim0 upper
  | succ n ih =>
      intro leaf upper
      refine Fin.lastCases ?_ (fun upper' => ?_) upper
      · intro lower
        refine Fin.lastCases ?_ (fun lower' => ?_) lower
        · intro h
          exact False.elim (lt_irrefl _ h)
        · intro _
          simpa only [GeometricPath.nodeAtLevel_last, GeometricPath.nodeAtLevel_castSucc] using
            (Below.root leaf.1 (GeometricPath.nodeAtLevel leaf.2 lower'))
      · intro lower
        refine Fin.lastCases ?_ (fun lower' => ?_) lower
        · intro h
          exact False.elim ((not_lt_of_ge (Fin.le_last upper'.castSucc)) h)
        · intro h
          simpa only [GeometricPath.nodeAtLevel_castSucc] using
            (Below.child leaf.1 (ih leaf.2 upper' lower' h))

variable {n t : Nat}

def lowerLevel (upper : Fin n) (lower : Fin upper.val) : Fin n :=
  ⟨lower.val, Nat.lt_trans lower.isLt upper.isLt⟩

theorem lowerLevel_lt (upper : Fin n) (lower : Fin upper.val) :
    lowerLevel upper lower < upper := lower.isLt

theorem lowerLevel_injective (upper : Fin n) : Function.Injective (lowerLevel upper) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin n => z.val) h

def pathDescendant (leaf : RecursiveSpaces.Slots branch n) (upper : Fin n)
    (lower : Fin upper.val) :
    {j : Nodes branch n // j ≠ GeometricPath.nodeAtLevel leaf upper} :=
  ⟨GeometricPath.nodeAtLevel leaf (lowerLevel upper lower),
    (below_nodeAtLevel leaf upper (lowerLevel upper lower) (lowerLevel_lt upper lower)).ne⟩

theorem pathDescendant_below (leaf : RecursiveSpaces.Slots branch n) (upper : Fin n)
    (lower : Fin upper.val) :
    Below branch (GeometricPath.nodeAtLevel leaf upper) (pathDescendant leaf upper lower).val :=
  below_nodeAtLevel leaf upper (lowerLevel upper lower) (lowerLevel_lt upper lower)

theorem pathDescendant_injective (leaf : RecursiveSpaces.Slots branch n) (upper : Fin n) :
    Function.Injective (pathDescendant leaf upper) := by
  intro i j h
  apply lowerLevel_injective upper
  apply GeometricPath.nodeAtLevel_injective leaf
  exact congrArg
    (fun z : {j : Nodes branch n // j ≠ GeometricPath.nodeAtLevel leaf upper} => z.val) h

noncomputable section

variable {rows : Nat → Nat}

theorem knownSpace_le_rowSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n, 0 < branch k) (leaf : RecursiveSpaces.Slots branch n)
    (upper : Fin n)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots
      (GeometricPath.nodeAtLevel leaf upper)) :
    HierarchicalKnownRows.knownSpace slots (GeometricPath.nodeAtLevel leaf upper) background
        (pathDescendant leaf upper) ≤
      NodeEmbedding.RowSpace slots (GeometricPath.nodeAtLevel leaf upper) :=
  RelativeDescendantProducts.knownSpace_le_rowSpace slots hbranch
    (GeometricPath.nodeAtLevel leaf upper) background (pathDescendant leaf upper)
    (pathDescendant_below leaf upper)

theorem knownSpace_le_factoringSpace
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (leaf : RecursiveSpaces.Slots branch n) (upper : Fin n)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots
      (GeometricPath.nodeAtLevel leaf upper)) :
    HierarchicalKnownRows.knownSpace slots (GeometricPath.nodeAtLevel leaf upper) background
        (pathDescendant leaf upper) ≤
      FactoredFunctions.factoringSpace
        (HierarchicalMatrixTable.other slots (GeometricPath.nodeAtLevel leaf upper) background) :=
  HierarchicalKnownRows.knownSpace_le_factoringSpace slots
    (GeometricPath.nodeAtLevel leaf upper) background (pathDescendant leaf upper)

end
end PerfectCompleteness.GeometricDescendants

end OAI
