import OAI.Algebra.AuslanderReiten.Fibers.FiberProductCoordinates
import OAI.Algebra.AuslanderReiten.Fibers.FiberDiagonalGenerator

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)
local notation "T₀" => fiberProductTriangle q H₁ H₂
local notation "X₀" => simpleHomotopyObject q
local notation "P₀" => A.simpleComplete q

theorem branchZeroHom_ne_zero (H : kˣ) (hn : branchHom q H ≠ 0) :
    branchZeroHom q H ≠ 0 := by
  intro h
  apply hn
  apply (cancel_mono ((shiftFunctorZero HC ℤ).inv.app (branchTargetObject q))).1
  simpa only [branchZeroHom, Limits.zero_comp] using h

variable (hq1 : 1+q ≠ 0) (e : BranchHom q 0 ≃ₗ[k] k)
variable (hg : branchHom q H₁ = branchHom q H₂) (hn : branchHom q H₁ ≠ 0)

include hn in
theorem branchScalar_ne_zero : e (branchZeroHom q H₁) ≠ 0 := by
  intro hz
  exact branchZeroHom_ne_zero q H₁ hn (e.injective (hz.trans (map_zero e).symm))

include hq1 e hg hn

theorem fiberSecondZero_surjective :
    Function.Surjective (TriangleGradedSequence.second k T₀ X₀ 0) :=
  TriangleGradedSequence.second_zero_surjective k T₀ X₀
    (fiberProductMiddleScalarEquiv q H₁ H₂ hq1) e
    (e (branchZeroHom q H₁)) (branchScalar_ne_zero q H₁ e hn)
    (fiberProductSecond_zero_common q H₁ H₂ hq1 e hg)

theorem fiberFullRhoPair_positive_bijective
    (hpos : ∀ n : ℤ, 0 < n → Subsingleton (BranchHom q n))
    (n : ℤ) (hnpos : 0 < n) :
    Function.Bijective (fiberFullRhoPair q H₁ H₂ n) := by
  apply fiberFullRhoPair_bijective_of_rho
  apply fiberRhoPair_bijective_of_productFirst
  exact TriangleGradedSequence.first_positive_bijective k T₀
    (fiberProductTriangle_distinguished q H₁ H₂) X₀ hpos
    (fiberSecondZero_surjective q H₁ H₂ hq1 e hg hn) n hnpos

variable [Subsingleton (BranchHom q (-1))]
local instance : Subsingleton (TriangleGradedSequence.Top T₀ X₀ (-1)) :=
  inferInstanceAs (Subsingleton (BranchHom q (-1)))

def fiberZeroScalarEquivOfBranches : FiberHom q H₁ H₂ 0 ≃ₗ[k] k :=
  TriangleGradedSequence.zeroScalarEquiv k T₀
    (fiberProductTriangle_distinguished q H₁ H₂) X₀
    (fiberProductMiddleScalarEquiv q H₁ H₂ hq1) e
    (e (branchZeroHom q H₁)) (branchScalar_ne_zero q H₁ e hn)
    (fiberProductSecond_zero_common q H₁ H₂ hq1 e hg)

def fiberZeroClassOfBranches : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0 :=
  (fiberFullHomEquiv q H₁ H₂ 0).symm
    ((fiberZeroScalarEquivOfBranches q H₁ H₂ hq1 e hg hn).symm 1)

omit e hg hn [Subsingleton (BranchHom q (-1))] in
theorem fiberFullRhoPair_zero_coordinates
    (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0) :
    ((A.fullHomZeroScalarEquiv q hq1).prodCongr (A.fullHomZeroScalarEquiv q hq1))
      (fiberFullRhoPair q H₁ H₂ 0 x) =
    fiberProductMiddleScalarEquiv q H₁ H₂ hq1
      (TriangleGradedSequence.first k T₀ X₀ 0 (fiberFullHomEquiv q H₁ H₂ 0 x)) := by
  change _ = ((simpleZeroScalarEquiv q hq1).prodCongr (simpleZeroScalarEquiv q hq1))
    (fiberProductMiddleEquiv q H₁ H₂ 0 _)
  rw [fiberProductFirst_coordinates]
  rfl

theorem fiberZeroClassOfBranches_image :
    fiberFullRhoPair q H₁ H₂ 0 (fiberZeroClassOfBranches q H₁ H₂ hq1 e hg hn) =
      (fullHomIdentity P₀, fullHomIdentity P₀) := by
  apply ((A.fullHomZeroScalarEquiv q hq1).prodCongr (A.fullHomZeroScalarEquiv q hq1)).injective
  rw [fiberFullRhoPair_zero_coordinates]
  simp only [LinearEquiv.prodCongr_apply, fullHomIdentity, A.fullHomZeroScalarEquiv_identity]
  rw [fiberZeroClassOfBranches, LinearEquiv.apply_symm_apply]
  change fiberProductMiddleScalarEquiv q H₁ H₂ hq1
    (TriangleGradedSequence.first k T₀ X₀ 0
      ((fiberZeroScalarEquivOfBranches q H₁ H₂ hq1 e hg hn).symm 1)) = (1, 1)
  exact TriangleGradedSequence.diagonalGenerator_image k T₀
    (fiberProductTriangle_distinguished q H₁ H₂) X₀
    (fiberProductMiddleScalarEquiv q H₁ H₂ hq1) e
    (e (branchZeroHom q H₁)) (branchScalar_ne_zero q H₁ e hn)
    (fiberProductSecond_zero_common q H₁ H₂ hq1 e hg)

theorem fiberZeroClassOfBranches_spans
    (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) 0) :
    ∃ c : k, x = c • fiberZeroClassOfBranches q H₁ H₂ hq1 e hg hn := by
  let f := (fiberFullHomEquiv q H₁ H₂ 0).trans
    (fiberZeroScalarEquivOfBranches q H₁ H₂ hq1 e hg hn)
  refine ⟨f x, f.injective ?_⟩
  rw [map_smul]
  change f x = f x • f (f.symm 1)
  rw [f.apply_symm_apply]
  exact (mul_one _).symm

end ArExplicit.T

end

end OAI
