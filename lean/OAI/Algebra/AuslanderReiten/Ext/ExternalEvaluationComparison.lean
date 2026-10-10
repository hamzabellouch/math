import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationDifferential
import OAI.Algebra.AuslanderReiten.Ext.ExternalComplexIso

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
variable (P' : ChainComplex (ModuleCat.{u} A) ℕ) (Q' : ChainComplex (ModuleCat.{u} B) ℕ)
variable (a : factorEvaluation k X P ⟶ P') (b : factorEvaluation k Y Q ⟶ Q')

theorem summandEvaluationIso_hom_eq (i j n : ℕ) (h : i+j=n) :
    (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
      (shuffle k A B (P.X i) (Q.X j) X Y).toModuleIso.hom := rfl

private theorem compose_after {C : Type*} [Category C]
    {U V W X Y Z : C} {a : U ⟶ V} {b : V ⟶ W} {c : W ⟶ X}
    {d : U ⟶ Y} {e : Y ⟶ W} {f : Y ⟶ Z} {g : Z ⟶ X}
    (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) :
    a ≫ (b ≫ c) = d ≫ (f ≫ g) := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

@[reassoc] theorem inclusion_evaluatedComparison (i j n : ℕ) (h : i+j=n) :
    (productEvaluation k A B X Y).map
      (ExternalTensor.inclusion k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) P Q i j n h) ≫
      ((totalEvaluationTermIso k A B X Y P Q n).hom ≫
        (ExternalTensor.complexMap k A B a b).f n) =
    (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom ≫
      ExternalTensor.mapHom k A B (a.f i) (b.f j) ≫
        ExternalTensor.inclusion k A B P' Q' i j n h :=
  compose_after (inclusion_totalEvaluationTermIso k A B X Y P Q i j n h)
    (ExternalTensor.inclusion_complexMap k A B a b i j n h)

end ArExplicit.ExternalBalanced

end

end OAI
