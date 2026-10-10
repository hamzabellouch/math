import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationSquare

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

theorem firstCubic_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+3+j=n+3)
    (p : P.X (i+3) ⟶ P.X i) :
    (E).map (ExternalTensor.mapHom k Ae Be p (𝟙 (Q.X j))) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+3) ⟨(i+3,j),h'⟩).hom ≫
      ExternalTensor.mapHom k A B ((EnvelopingBimodule.evaluationFunctor k A X).map p)
        (𝟙 ((QE).X j)) := by
  have hs := shuffle_natural_fixed k A B X Y p (𝟙 (Q.X j))
  rw [(EnvelopingBimodule.evaluationFunctor k B Y).map_id] at hs
  convert! hs using 1

theorem secondCubic_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+(j+3)=n+3)
    (r : Q.X (j+3) ⟶ Q.X j) :
    (E).map (ExternalTensor.mapHom k Ae Be (𝟙 (P.X i)) r) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+3) ⟨(i,j+3),h'⟩).hom ≫
      ExternalTensor.mapHom k A B (𝟙 ((PE).X i))
        ((EnvelopingBimodule.evaluationFunctor k B Y).map r) := by
  have hs := shuffle_natural_fixed k A B X Y (𝟙 (P.X i)) r
  rw [(EnvelopingBimodule.evaluationFunctor k A X).map_id] at hs
  convert! hs using 1

end ArExplicit.ExternalBalanced

end

end OAI
