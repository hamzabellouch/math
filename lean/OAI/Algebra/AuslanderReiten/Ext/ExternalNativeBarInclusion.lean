import OAI.Algebra.AuslanderReiten.Bar.ExternalBarEvaluation
import OAI.Algebra.AuslanderReiten.Bar.ExternalBarTotalFree
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationComparison

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
private theorem chain_two {C : Type*} [Category C]
    {P Q R S T U : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S}
    {d : P ⟶ T} {e : T ⟶ R} {f : T ⟶ U} {g : U ⟶ S}
    (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) :
    a ≫ (b ≫ c) = d ≫ (f ≫ g) := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B
local notation "PM" => ModuleBar.complex k A M
local notation "QN" => ModuleBar.complex k B N

theorem nativeTotalBarIso_f (n : ℕ) :
    (nativeTotalBarIso k A B M N).hom.f n =
      (totalEvaluationTermIso k A B X Y P Q n).hom ≫
        (ExternalTensor.complexMap k A B (BarBalanced.nativeComplexIso k A M).hom
          (BarBalanced.nativeComplexIso k B N).hom).f n := rfl

omit [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N] in
theorem barSummandEvaluationIso_hom :
    (summandEvaluationIso k A B X Y P Q 0 ⟨(0,0),rfl⟩).hom =
      (shuffle k A B ((P).X 0) ((Q).X 0) X Y).toModuleIso.hom := rfl

theorem nativeTotalBarIso_inclusion_zero :
    (productEvaluation k A B X Y).map (ExternalTensor.inclusion k Ae Be P Q 0 0 0 rfl) ≫
      (nativeTotalBarIso k A B M N).hom.f 0 =
    (summandEvaluationIso k A B X Y P Q 0 ⟨(0,0),rfl⟩).hom ≫
      ExternalTensor.mapHom k A B ((BarBalanced.nativeComplexIso k A M).hom.f 0)
        ((BarBalanced.nativeComplexIso k B N).hom.f 0) ≫
      ExternalTensor.inclusion k A B PM QN 0 0 0 rfl := by
  rw [nativeTotalBarIso_f]
  exact inclusion_evaluatedComparison k A B X Y P Q PM QN
    (BarBalanced.nativeComplexIso k A M).hom (BarBalanced.nativeComplexIso k B N).hom
    0 0 0 rfl

end ArExplicit.ExternalBalanced

end

end OAI
