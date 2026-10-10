import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationTerms
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationNaturality

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
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q

theorem horizontal_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+1+j=n+1) :
    (E).map (ExternalTensor.mapHom k Ae Be (P.d (i+1) i) (𝟙 (Q.X j))) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i+1,j),h'⟩).hom ≫
      ExternalTensor.mapHom k A B ((PE).d (i+1) i) (𝟙 ((QE).X j)) := by
  have hs := shuffle_natural_fixed k A B X Y (P.d (i+1) i) (𝟙 (Q.X j))
  rw [(EnvelopingBimodule.evaluationFunctor k B Y).map_id] at hs
  convert! hs using 1

theorem vertical_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+(j+1)=n+1) :
    (E).map (ExternalTensor.mapHom k Ae Be (𝟙 (P.X i)) (Q.d (j+1) j)) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i,j+1),h'⟩).hom ≫
      ExternalTensor.mapHom k A B (𝟙 ((PE).X i)) ((QE).d (j+1) j) := by
  have hs := shuffle_natural_fixed k A B X Y (𝟙 (P.X i)) (Q.d (j+1) j)
  rw [(EnvelopingBimodule.evaluationFunctor k A X).map_id] at hs
  convert! hs using 1

end ArExplicit.ExternalBalanced

end

end OAI
