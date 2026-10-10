import Mathlib.Data.Fin.Tuple.Basic
import OAI.Computability.PerfectCompleteness.Algebra.HierarchicalMatrixTable
import OAI.Computability.PerfectCompleteness.Algebra.MatrixTriangularFoldingLemmas
import OAI.Computability.PerfectCompleteness.Construction.FactoredFunctionsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalArrays
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI


namespace PerfectCompleteness.GeometricPath

open RecursiveSpaces DescendantSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat}

def leafPath : {n : Nat} → Slots branch n → Path branch n 0
  | 0, _ => .refl 0
  | _ + 1, leaf => .step leaf.1 (leafPath leaf.2)

theorem leafPath_endpoint : ∀ {n : Nat} (leaf : Slots branch n),
    (leafPath leaf).slotEmbedding () = leaf := by
  intro n
  induction n with
  | zero => intro leaf; cases leaf; rfl
  | succ n ih =>
    intro leaf
    exact Prod.ext rfl (ih leaf.2)

def nodeAtLevel : {n : Nat} → Slots branch n → Fin n → Nodes branch n
  | 0, _, level => Fin.elim0 level
  | _ + 1, leaf, level =>
      Fin.lastCases (.inl ()) (fun lower => .inr (leaf.1, nodeAtLevel leaf.2 lower)) level

@[simp] theorem nodeAtLevel_last {n : Nat} (leaf : Slots branch (n + 1)) :
    nodeAtLevel leaf (Fin.last n) = (.inl () : Nodes branch (n + 1)) := by
  exact Fin.lastCases_last (n := n) (motive := fun _ => Nodes branch (n + 1))
    (last := (.inl () : Nodes branch (n + 1)))
    (cast := fun lower : Fin n => (.inr (leaf.1, nodeAtLevel leaf.2 lower) : Nodes branch (n + 1)))

@[simp] theorem nodeAtLevel_castSucc {n : Nat} (leaf : Slots branch (n + 1))
    (lower : Fin n) :
    nodeAtLevel leaf lower.castSucc =
      (.inr (leaf.1, nodeAtLevel leaf.2 lower) : Nodes branch (n + 1)) := by
  exact Fin.lastCases_castSucc (n := n) (motive := fun _ => Nodes branch (n + 1))
    (last := (.inl () : Nodes branch (n + 1)))
    (cast := fun j : Fin n => (.inr (leaf.1, nodeAtLevel leaf.2 j) : Nodes branch (n + 1))) lower

theorem nodeAtLevel_height : ∀ {n : Nat} (leaf : Slots branch n) (level : Fin n),
    Nodes.height (nodeAtLevel leaf level) = level.val + 1 := by
  intro n
  induction n with
  | zero => intro leaf level; exact Fin.elim0 level
  | succ n ih =>
    intro leaf level
    refine Fin.lastCases ?_ (fun lower => ?_) level
    · simp only [nodeAtLevel_last, Nodes.height, Fin.val_last]
    · simpa only [nodeAtLevel_castSucc, Nodes.height, Fin.val_castSucc]
        using ih leaf.2 lower

theorem nodeAtLevel_injective {n : Nat} (leaf : Slots branch n) :
    Function.Injective (nodeAtLevel leaf) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Nodes.height h
  rw [nodeAtLevel_height, nodeAtLevel_height] at hh
  exact Nat.add_right_cancel hh

theorem slots_nonempty : ∀ (n : Nat), (∀ k < n, 0 < branch k) → Nonempty (Slots branch n) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨()⟩
  | succ n ih =>
    intro hbranch
    obtain ⟨leaf⟩ := ih (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    exact ⟨(⟨0, hbranch n (Nat.lt_succ_self n)⟩, leaf)⟩

noncomputable def law (n : Nat) (hbranch : ∀ k < n, 0 < branch k) :
    FiniteDistribution (Slots branch n) := by
  letI := slots_nonempty n hbranch
  exact FiniteDistribution.uniform (Slots branch n)

theorem law_step (n : Nat) (hbranch : ∀ k < n + 1, 0 < branch k) :
    law (n + 1) hbranch =
      (by
        letI : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch n (Nat.lt_succ_self n)⟩⟩
        exact (FiniteDistribution.uniform (Fin (branch n))).product
          (law n (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))))) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro leaf
  change (1 : ℝ) / (Fintype.card (Fin (branch n) × Slots branch n) : ℝ) =
    ((1 : ℝ) / (Fintype.card (Fin (branch n)) : ℝ)) *
      ((1 : ℝ) / (Fintype.card (Slots branch n) : ℝ))
  simp [Fintype.card_prod, Nat.cast_mul, one_div, mul_inv_rev, mul_comm]

end PerfectCompleteness.GeometricPath



namespace PerfectCompleteness.HierarchicalKnownRows

noncomputable section

open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat} {D : Type*}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
  (descendant : D → {j : Nodes branch n // j ≠ upper})

def lower (x : NodeEmbedding.NumberedDomain slots) (d : D) :
    Fin (rows (Nodes.height (descendant d).val)) → F2 :=
  (HierarchicalMatrixTable.other slots upper background x).1 (descendant d)

@[simp] theorem lower_apply (x : NodeEmbedding.NumberedDomain slots)
    (d : D) (i : Fin (rows (Nodes.height (descendant d).val))) :
    lower slots upper background descendant x d i =
      (background (descendant d) i).val
        (NodeEmbedding.numberedRestriction slots (descendant d).val x) := rfl

def knownSpace : Submodule F2 (NodeEmbedding.NumberedDomain slots → F2) :=
  FactoredFunctionsDependent.dependentQuadraticSpan (lower slots upper background descendant)

theorem one_mem_knownSpace :
    (1 : NodeEmbedding.NumberedDomain slots → F2) ∈ knownSpace slots upper background descendant :=
  FactoredFunctionsDependent.one_mem_dependentQuadraticSpan _

theorem product_mem_knownSpace (d : D)
    (i j : Fin (rows (Nodes.height (descendant d).val))) :
    (fun x => lower slots upper background descendant x d i *
      lower slots upper background descendant x d j) ∈ knownSpace slots upper background descendant :=
  FactoredFunctionsDependent.product_mem_dependentQuadraticSpan
    (𝕜 := F2) (Ω := NodeEmbedding.NumberedDomain slots) (I := D)
    (J := fun d => Fin (rows (Nodes.height (descendant d).val)))
    (lower slots upper background descendant) d i j

theorem knownSpace_le_factoringSpace :
    knownSpace slots upper background descendant ≤
      FactoredFunctions.factoringSpace (HierarchicalMatrixTable.other slots upper background) := by
  intro f hf x y hxy
  apply FactoredFunctionsDependent.dependentQuadraticSpan_le_factoringSpace
    (lower slots upper background descendant) hf x y
  funext d i
  exact congrArg (fun z : HierarchicalMatrixTable.SideOutput (rows := rows) upper =>
    z.1 (descendant d) i) hxy

theorem determined :
    RepresentativeMatrixTable.Determined (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
      ((knownSpace slots upper background descendant).comap
        (NodeEmbedding.RowSpace slots upper).subtype) :=
  RepresentativeMatrixTable.determined_comap (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
    (knownSpace slots upper background descendant)
    (knownSpace_le_factoringSpace slots upper background descendant)

end
end PerfectCompleteness.HierarchicalKnownRows

end OAI
