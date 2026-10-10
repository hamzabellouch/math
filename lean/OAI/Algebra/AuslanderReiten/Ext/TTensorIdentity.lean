import OAI.Algebra.AuslanderReiten.Ext.TTensorActions

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

theorem tTensorCoefficient_identity :
    tTensorCoefficientEquiv q hq hq1 h 0
      (Pi.single ⟨(0,0),rfl⟩ (Ext.mk₀ (𝟙 S) ⊗ₜ[k] Ext.mk₀ (𝟙 S))) = fun _ => 1 := by
  funext i
  obtain rfl : i=0 := Fin.eq_zero i
  rw [tTensorCoefficientEquiv_apply]
  change tTensorScalarEquiv q hq hq1 h 0 0
    ((Pi.single ⟨(0,0),rfl⟩ (Ext.mk₀ (𝟙 S) ⊗ₜ[k] Ext.mk₀ (𝟙 S)) : tTensorCoefficients q 0)
      ⟨(0,0),rfl⟩) = 1
  rw [Pi.single_eq_same, tTensorScalarEquiv_tmul]
  have hc : (tExplicitCoefficientEquiv q hq hq1 h 0).symm (Ext.mk₀ (𝟙 S)) = 1 := by
    rw [← tExplicitPower_zero q hq hq1 h]
    exact LinearEquiv.symm_apply_apply _ _
  rw [hc, one_mul]

end ArExplicit.Resolution

end

end OAI
