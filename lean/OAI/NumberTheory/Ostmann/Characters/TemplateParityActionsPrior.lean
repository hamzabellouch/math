import OAI.NumberTheory.Ostmann.Characters.TemplateParityActionsPermutation
import OAI.NumberTheory.Ostmann.Characters.WordSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.ParityActions
open Construction
attribute [local instance] Classical.propDecidable

def assignmentEquiv {α : Type*} (k n m : ℕ) (σ : Reassignments k n m) :
    (BulkSlot k n m → α) ≃ (BulkSlot k n m → α) where
  toFun x i := x ((bulkPermutation k n m σ).symm i)
  invFun x i := x (bulkPermutation k n m σ i)
  left_inv x := by funext i; exact congrArg x ((bulkPermutation k n m σ).symm_apply_apply i)
  right_inv x := by funext i; exact congrArg x ((bulkPermutation k n m σ).apply_symm_apply i)

@[simp] theorem assignmentEquiv_apply {α : Type*} (k n m : ℕ)
    (σ : Reassignments k n m) (x : BulkSlot k n m → α) (i : BulkSlot k n m) :
    assignmentEquiv k n m σ x i = x ((bulkPermutation k n m σ).symm i) := rfl

@[simp] theorem assignmentEquiv_moves {α : Type*} (k n m : ℕ)
    (σ : Reassignments k n m) (x : BulkSlot k n m → α) (i : BulkSlot k n m) :
    assignmentEquiv k n m σ x (bulkPermutation k n m σ i) = x i := by
  change x ((bulkPermutation k n m σ).symm (bulkPermutation k n m σ i)) = x i
  rw [Equiv.symm_apply_apply]

theorem productPrior_mass_invariant {α : Type*} [Fintype α] (k n m : ℕ)
    (μ : Fin m → FinitePrior α) (σ : Reassignments k n m) (x : BulkSlot k n m → α) :
    (productPrior (fun i : BulkSlot k n m => μ i.2)).mass (assignmentEquiv k n m σ x) =
      (productPrior (fun i : BulkSlot k n m => μ i.2)).mass x := by
  classical
  change (∏ i : BulkSlot k n m, (μ i.2).mass (x ((bulkPermutation k n m σ).symm i))) =
    ∏ i : BulkSlot k n m, (μ i.2).mass (x i)
  have hh := (bulkPermutation k n m σ).symm.prod_comp
    (fun i : BulkSlot k n m => (μ i.2).mass (x i))
  calc
    _ = ∏ i : BulkSlot k n m, (μ ((bulkPermutation k n m σ).symm i).2).mass
        (x ((bulkPermutation k n m σ).symm i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [bulkPermutation_symm_position k n m σ i]
    _ = _ := hh

theorem productPrior_cmean_invariant {α : Type*} [Fintype α] (k n m : ℕ)
    (μ : Fin m → FinitePrior α) (σ : Reassignments k n m)
    (F : (BulkSlot k n m → α) → ℂ) :
    (productPrior (fun i : BulkSlot k n m => μ i.2)).cmean
      (fun x => F (assignmentEquiv k n m σ x)) =
    (productPrior (fun i : BulkSlot k n m => μ i.2)).cmean F := by
  classical
  let P := productPrior (fun i : BulkSlot k n m => μ i.2)
  change (∑ x, (P.mass x:ℂ)*F (assignmentEquiv k n m σ x)) =
    ∑ x, (P.mass x:ℂ)*F x
  have hh := (assignmentEquiv (α:=α) k n m σ).sum_comp
    (fun x => (P.mass x:ℂ)*F x)
  have hm (x : BulkSlot k n m → α) : P.mass (assignmentEquiv k n m σ x) = P.mass x :=
    productPrior_mass_invariant k n m μ σ x
  simpa only [hm] using hh

end Ostmann.Characters.Template.ParityActions

end

end OAI
