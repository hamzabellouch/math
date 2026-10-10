import OAI.Computability.PerfectCompleteness.Repetition.CleanTreeFactors
import OAI.Computability.PerfectCompleteness.Sampling.UniformChildSum

namespace OAI

section

namespace PerfectCompleteness.CutChildGrouping

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

abbrev Child (i : Fin (branch n)) :=
  (C → squareSpace (H (childSlots slots i))) × Arrays (childSlots slots i) rows

instance childFintype (i : Fin (branch n)) : Fintype (Child (C := C) slots rows i) :=
  Fintype.ofFinite _

abbrev Raw := (i : Fin (branch n)) → Child (C := C) slots rows i

abbrev Assembled :=
  (C → H slots) × ((i : Fin (branch n)) → Arrays (childSlots slots i) rows)

instance assembledFintype : Fintype (Assembled (C := C) slots rows) := Fintype.ofFinite _

def rawLaw : FiniteDistribution (Raw (C := C) slots rows) :=
  FiniteProduct.law (fun i => FiniteDistribution.uniform (Child (C := C) slots rows i))

def assemble : Raw (C := C) slots rows →ₗ[F2] Assembled (C := C) slots rows where
  toFun x :=
    (fun q => UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots)
      (fun i => (x i).1 q), fun i => (x i).2)
  map_add' x y := by
    apply Prod.ext
    · funext q
      exact map_add (UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots))
        (fun i => (x i).1 q) (fun i => (y i).1 q)
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · funext q
      exact map_smul (UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots)) c
        (fun i => (x i).1 q)
    · rfl

omit [Fintype C] in
@[simp] theorem assemble_calls (x : Raw (C := C) slots rows) (q : C) :
    (assemble slots rows x).1 q =
      UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots)
        (fun i => (x i).1 q) := rfl

omit [Fintype C] in
@[simp] theorem assemble_arrays (x : Raw (C := C) slots rows) (i : Fin (branch n)) :
    (assemble slots rows x).2 i = (x i).2 := rfl

omit [Fintype C] in
theorem assemble_surjective : Function.Surjective (assemble (C := C) slots rows) := by
  rintro ⟨calls, arrays⟩
  have hex : ∀ q : C, ∃ u : (i : Fin (branch n)) → squareSpace (H (childSlots slots i)),
      UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots) u = calls q := by
    intro q
    exact UniformChildSum.recursiveSum_surjective (TreeSourceSpaces.LeafDomain slots) (calls q)
  choose u hu using hex
  refine ⟨fun i => (fun q => u q i, arrays i), ?_⟩
  apply Prod.ext
  · funext q
    exact hu q
  · rfl

theorem assemble_law :
    (rawLaw (C := C) slots rows).pushforward (assemble slots rows) =
      FiniteDistribution.uniform (Assembled (C := C) slots rows) := by
  unfold rawLaw
  rw [UniformLinearImage.law_uniform]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (assemble slots rows) (assemble_surjective slots rows)

theorem projected_child_type (calls : Nat)
    (ids : RecursiveSpaces.Slots branch (n + 1) → Fin t → Nat)
    (i : Fin (branch n)) :
    Child (C := Fin calls) (ProjectedCardinality.projectedSlots ids) rows i =
      CleanTreeFactors.Raw calls rows (fun s k => ids (i, s) k) := rfl

end
end PerfectCompleteness.CutChildGrouping

end

end OAI
