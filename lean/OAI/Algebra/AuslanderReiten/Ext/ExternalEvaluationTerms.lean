import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingEvaluationFunctor
import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedNaturality
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorDifferential
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)

abbrev productEvaluation := ExternalTensor.envelopingFunctor k A B ⋙
  EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B) (ExternalTensor.moduleObject k A B X Y)

abbrev factorEvaluation {S : Type u} [Ring S] [Algebra k S] (Z : ModuleCat.{u} S)
    (P : ChainComplex (ModuleCat.{u} (S ⊗[k] Sᵐᵒᵖ)) ℕ) :=
  ((EnvelopingBimodule.evaluationFunctor k S Z).mapHomologicalComplex (ComplexShape.down ℕ)).obj P

variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ

abbrev evaluatedTotal := ((productEvaluation k A B X Y).mapHomologicalComplex
  (ComplexShape.down ℕ)).obj (ExternalTensor.complex k Ae Be P Q)

abbrev totalEvaluated := ExternalTensor.complex k A B
  (factorEvaluation k X P) (factorEvaluation k Y Q)

def summandEvaluationIso (n : ℕ) (ij : ExternalTensor.Diagonal n) :
    (productEvaluation k A B X Y).obj (ExternalTensor.summands k Ae Be P Q n ij) ≅
      ExternalTensor.summands k A B (factorEvaluation k X P) (factorEvaluation k Y Q) n ij :=
  (shuffle k A B (P.X ij.val.1) (Q.X ij.val.2) X Y).toModuleIso

def totalEvaluationTermIso (n : ℕ) : (evaluatedTotal k A B X Y P Q).X n ≅
    (totalEvaluated k A B X Y P Q).X n :=
  (PreservesCoproduct.iso (productEvaluation k A B X Y)
    (ExternalTensor.summands k Ae Be P Q n)) ≪≫
      Sigma.mapIso (summandEvaluationIso k A B X Y P Q n)

private theorem map_coproduct_inclusion
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {ι : Type*} (Z : ι → C) [HasCoproduct Z] [HasCoproduct (fun i => F.obj (Z i))]
    [PreservesColimit (Discrete.functor Z) F] (i : ι) :
    F.map (Sigma.ι Z i) ≫ (PreservesCoproduct.iso F Z).hom =
      Sigma.ι (fun i => F.obj (Z i)) i := by
  apply (cancel_mono (PreservesCoproduct.iso F Z).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [PreservesCoproduct.inv_hom, sigmaComparison, Sigma.ι_comp_desc]

@[reassoc] theorem inclusion_totalEvaluationTermIso (i j n : ℕ) (h : i+j=n) :
    (productEvaluation k A B X Y).map (ExternalTensor.inclusion k Ae Be P Q i j n h) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom ≫
      ExternalTensor.inclusion k A B (factorEvaluation k X P) (factorEvaluation k Y Q) i j n h := by
  dsimp only [totalEvaluationTermIso]
  have hι := map_coproduct_inclusion (productEvaluation k A B X Y)
    (ExternalTensor.summands k Ae Be P Q n) ⟨(i,j),h⟩
  erw [Iso.trans_hom, ← Category.assoc, hι, Sigma.ι_mapIso_hom]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
