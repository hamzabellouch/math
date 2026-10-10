import OAI.Algebra.AuslanderReiten.Coordinates.BranchHomProfile
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBranchDetector
import OAI.Algebra.AuslanderReiten.Fibers.FiberBranchConsequences

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
variable (H₁ H₂ : kˣ)
local notation "P₀" => A.simpleComplete q

include hq hq1 h

theorem normalizedBranches_equal : branchHom q H₁ = branchHom q H₂ :=
  branchHom_common_of_scalarCoordinate q hq1 (branchPlainScalarEquiv q hq hq1 h) H₁ H₂

theorem normalizedBranch_ne_zero (H : kˣ) : branchHom q H ≠ 0 :=
  branchHom_ne_zero_of_scalarCoordinate q hq1 (branchPlainScalarEquiv q hq hq1 h) H

theorem fiberPositiveRhoPair_bijective (n : ℤ) (hn : 0 < n) :
    Function.Bijective (fiberFullRhoPair q H₁ H₂ n) :=
  fiberFullRhoPair_positive_bijective q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁)
    (fun a ha => branchHom_subsingleton q hq hq1 h a (by omega) (by omega)) n hn

def fiberDiagonalClass : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0 := by
  letI := branchHom_subsingleton q hq hq1 h (-1) (by omega) (by omega)
  exact fiberZeroClassOfBranches q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁)

theorem fiberDiagonalClass_image :
    fiberFullRhoPair q H₁ H₂ 0 (fiberDiagonalClass q hq hq1 h H₁ H₂) =
      (fullHomIdentity P₀, fullHomIdentity P₀) := by
  let := branchHom_subsingleton q hq hq1 h (-1) (by omega) (by omega)
  exact fiberZeroClassOfBranches_image q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁)

theorem fiberDiagonalClass_spans (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0) :
    ∃ c : k, x = c • fiberDiagonalClass q hq hq1 h H₁ H₂ := by
  let := branchHom_subsingleton q hq hq1 h (-1) (by omega) (by omega)
  exact fiberZeroClassOfBranches_spans q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁) x

theorem fiberDiagonalClass_ne_zero : fiberDiagonalClass q hq hq1 h H₁ H₂ ≠ 0 := by
  intro hz
  have hp := fiberDiagonalClass_image q hq hq1 h H₁ H₂
  rw [hz, map_zero] at hp
  have hs := congrArg (fun z => A.fullHomZeroScalarEquiv q hq1 z.1) hp
  simp only [Prod.fst_zero, map_zero, fullHomIdentity, A.fullHomZeroScalarEquiv_identity] at hs
  exact zero_ne_one hs

end ArExplicit.T

end

end OAI
