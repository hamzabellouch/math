import OAI.Algebra.AuslanderReiten.Ext.ExternalNativeBarInclusion
import OAI.Algebra.AuslanderReiten.Ext.ExternalFreeEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ

def totalFreeEvaluation : (evaluatedTotal k A B X Y P Q).X 0 ⟶
    ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) :=
  (nativeTotalBarIso k A B M N).hom.f 0 ≫
    ExternalTensor.barTotalFreeCoordinate k A B M N e f

private theorem postcompose_square {C : Type*} [Category C]
    {U V W V₁ V₂ V₃ : C} {a : U ⟶ V} {b : V ⟶ W} {c : W ⟶ V₁}
    {d : U ⟶ V₂} {h : V₂ ⟶ V₃} {i : V₃ ⟶ W} {j : V₃ ⟶ V₁}
    (h₁ : a ≫ b = d ≫ h ≫ i) (h₂ : i ≫ c = j) :
    a ≫ (b ≫ c) = d ≫ h ≫ j := by
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc, h₂]

theorem inclusion_totalFreeEvaluation :
    (productEvaluation k A B X Y).map (ExternalTensor.inclusion k Ae Be P Q 0 0 0 rfl) ≫
      totalFreeEvaluation k A B M N e f =
    (summandEvaluationIso k A B X Y P Q 0 ⟨(0,0),rfl⟩).hom ≫
      ExternalTensor.mapHom k A B ((BarBalanced.nativeComplexIso k A M).hom.f 0)
        ((BarBalanced.nativeComplexIso k B N).hom.f 0) ≫
          ExternalTensor.barFreeCoordinate k A B M N e f :=
  postcompose_square (nativeTotalBarIso_inclusion_zero k A B M N)
    (ExternalTensor.inclusion_barTotalFreeCoordinate k A B M N e f)

end ArExplicit.ExternalBalanced

end

end OAI
