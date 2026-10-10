import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberComponentMaps
import OAI.Algebra.AuslanderReiten.Coordinates.MappedBiproductRow
import OAI.Algebra.AuslanderReiten.Algebras.SimpleHomScalars
import OAI.Algebra.AuslanderReiten.Homology.TriangleConnectingProduct

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)
local notation "X₀" => simpleHomotopyObject q
local notation "T₀" => fiberProductTriangle q H₁ H₂

def fiberProductMiddleEquiv (n : ℤ) :
    TriangleGradedSequence.Middle T₀ X₀ n ≃ₗ[k] (SimpleHom q n × SimpleHom q n) :=
  mappedBiproductHomEquiv k (CategoryTheory.shiftFunctor HC n) X₀ X₀ X₀

def fiberProductMiddleScalarEquiv (hq1 : 1+q ≠ 0) :
    TriangleGradedSequence.Middle T₀ X₀ 0 ≃ₗ[k] k × k :=
  (fiberProductMiddleEquiv q H₁ H₂ 0).trans
    ((simpleZeroScalarEquiv q hq1).prodCongr (simpleZeroScalarEquiv q hq1))

def branchZeroHom (H : kˣ) : BranchHom q 0 :=
  branchHom q H ≫ (shiftFunctorZero HC ℤ).inv.app (branchTargetObject q)

theorem fiberProductSecond_row (n : ℤ)
    (m : TriangleGradedSequence.Middle T₀ X₀ n) :
    TriangleGradedSequence.second k T₀ X₀ n m =
      (fiberProductMiddleEquiv q H₁ H₂ n m).1 ≫ (branchHom q H₁)⟦n⟧' +
      (fiberProductMiddleEquiv q H₁ H₂ n m).2 ≫ (branchHom q H₂)⟦n⟧' := by
  erw [TriangleGradedSequence.second_eq_shift,
    mappedBiproduct_row k (CategoryTheory.shiftFunctor HC n) X₀ X₀ X₀,
    fiberProductTriangle_inl_second, fiberProductTriangle_inr_second]
  rfl

theorem fiberProductSecond_zero (hq1 : 1+q ≠ 0)
    (m : TriangleGradedSequence.Middle T₀ X₀ 0) :
    TriangleGradedSequence.second k T₀ X₀ 0 m =
      (fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).1 • branchZeroHom q H₁ +
      (fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).2 • branchZeroHom q H₂ := by
  have h₁ := congrArg (fun v => v ≫ (branchHom q H₁)⟦(0 : ℤ)⟧')
    (simpleHom_eq_scalar_unit q hq1 (fiberProductMiddleEquiv q H₁ H₂ 0 m).1)
  have h₂ := congrArg (fun v => v ≫ (branchHom q H₂)⟦(0 : ℤ)⟧')
    (simpleHom_eq_scalar_unit q hq1 (fiberProductMiddleEquiv q H₁ H₂ 0 m).2)
  refine (fiberProductSecond_row q H₁ H₂ 0 m).trans ((congrArg₂ (· + ·) h₁ h₂).trans ?_)
  rw [Linear.smul_comp, Linear.smul_comp, simpleZeroUnit_postcomp, simpleZeroUnit_postcomp]
  rfl

theorem fiberProductSecond_zero_common (hq1 : 1+q ≠ 0)
    (e : BranchHom q 0 ≃ₗ[k] k) (hg : branchHom q H₁ = branchHom q H₂)
    (m : TriangleGradedSequence.Middle T₀ X₀ 0) :
    e (TriangleGradedSequence.second k T₀ X₀ 0 m) =
      e (branchZeroHom q H₁) *
        ((fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).1 +
          (fiberProductMiddleScalarEquiv q H₁ H₂ hq1 m).2) := by
  have hz : branchZeroHom q H₁ = branchZeroHom q H₂ :=
    congrArg (fun f => f ≫ (shiftFunctorZero HC ℤ).inv.app (branchTargetObject q)) hg
  rw [fiberProductSecond_zero q H₁ H₂ hq1, ← hz, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

end ArExplicit.T

end

end OAI
