import OAI.Computability.PerfectCompleteness.Foundations.WholeCutGrouping

namespace OAI

section

namespace PerfectCompleteness.CutCallExtension

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

abbrev Extended := CutChildGrouping.Raw (C := Option C) slots rows

def original (x : Extended (C := C) slots rows) :
    CutChildGrouping.Raw (C := C) slots rows :=
  fun i => (fun c => (x i).1 (some c), (x i).2)

def fresh (x : Extended (C := C) slots rows) : H slots :=
  UniformChildSum.recursiveSum (LeafDomain slots) (fun i => (x i).1 none)

def observe (x : Extended (C := C) slots rows) :
    CutChildGrouping.Assembled (C := C) slots rows × H slots :=
  (CutChildGrouping.assemble slots rows (original slots rows x), fresh slots rows x)

def splitAssembled : CutChildGrouping.Assembled (C := Option C) slots rows →ₗ[F2]
    CutChildGrouping.Assembled (C := C) slots rows × H slots where
  toFun x := ((fun c => x.1 (some c), x.2), x.1 none)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype C] in
theorem splitAssembled_surjective : Function.Surjective
    (splitAssembled (C := C) slots rows) := by
  rintro ⟨⟨old, arrays⟩, extra⟩
  refine ⟨(fun c => match c with | none => extra | some c => old c, arrays), ?_⟩
  rfl

omit [Fintype C] in
@[simp] theorem split_assemble (x : Extended (C := C) slots rows) :
    splitAssembled slots rows (CutChildGrouping.assemble slots rows x) =
      observe slots rows x := rfl

theorem observe_law :
    (CutChildGrouping.rawLaw (C := Option C) slots rows).pushforward
        (observe slots rows) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := C) slots rows)).product
        (FiniteDistribution.uniform (H slots)) := by
  change (CutChildGrouping.rawLaw (C := Option C) slots rows).pushforward
    (fun x => splitAssembled slots rows (CutChildGrouping.assemble slots rows x)) = _
  rw [← FiniteDistribution.pushforward_comp, CutChildGrouping.assemble_law,
    UniformLinearImage.uniform_pushforward_linearMap
      (splitAssembled slots rows) (splitAssembled_surjective slots rows)]
  exact WholeCutSampler.uniform_product.symm

theorem call_count : Fintype.card (Option C) = Fintype.card C + 1 :=
  Fintype.card_option

end
end PerfectCompleteness.CutCallExtension

end

end OAI
