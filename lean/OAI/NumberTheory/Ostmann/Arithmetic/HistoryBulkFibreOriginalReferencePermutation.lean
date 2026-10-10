import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryBulkSourceDisintegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def bulkDrawPermutation (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    SelectedBulkSample C l ≃ SelectedBulkSample C l :=
  Equiv.arrowCongr σ.symm (Equiv.refl C.bulk.Sample)

@[simp] theorem bulkDrawPermutation_apply
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (y : SelectedBulkSample C l)
    (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    bulkDrawPermutation C σ y u = y (σ u) := rfl

theorem bulkDrawPermutation_mass
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (y : SelectedBulkSample C l) :
    (selectedBulkPrior C l).mass (bulkDrawPermutation C σ y) = (selectedBulkPrior C l).mass y :=
  Equiv.prod_comp σ (fun u => C.bulk.law.mass (y u))

theorem bulk_cmean_permutation
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (F : SelectedBulkSample C l → ℂ) :
    (selectedBulkPrior C l).cmean (fun y => F (fun u => y (σ u))) =
      (selectedBulkPrior C l).cmean F := by
  let W : WeightEquiv (selectedBulkPrior C l).mass (selectedBulkPrior C l).mass :=
    ⟨bulkDrawPermutation C σ,fun y => (bulkDrawPermutation_mass C σ y).symm⟩
  exact W.csum_comp F

theorem bulk_cmean_relative_permutation
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (F : SelectedBulkSample C l → SelectedBulkSample C l → ℂ) :
    (selectedBulkPrior C l).cmean (fun y => F (fun u => y (σ u)) (fun u => y (τ u))) =
      (selectedBulkPrior C l).cmean (fun y => F y (fun u => y ((σ⁻¹*τ) u))) := by
  have h := bulk_cmean_permutation C σ (fun y => F y (fun u => y ((σ⁻¹*τ) u)))
  simpa only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h

theorem permute_fibreAssignment
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l) (y : SelectedBulkSample C l) :
    permuteAssignment C σ (fibreAssignment C a y) =
      fibreAssignment C a (fun u => y (σ u)) :=
  selectedSourceEquiv_symm_permutation C l σ a y

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
