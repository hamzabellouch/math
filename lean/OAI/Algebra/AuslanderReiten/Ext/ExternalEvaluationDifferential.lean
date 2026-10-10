import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationTerms
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationSquare

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
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

theorem evaluatedTotal_hom_ext {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    {f g : (evaluatedTotal k A B X Y P Q).X n ⟶ N}
    (h : ∀ i j (hij : i+j=n), (E).map (ExternalTensor.inclusion k Ae Be P Q i j n hij) ≫ f =
      (E).map (ExternalTensor.inclusion k Ae Be P Q i j n hij) ≫ g) : f=g := by
  apply (isColimitOfHasCoproductOfPreservesColimit E
    (ExternalTensor.summands k Ae Be P Q n)).hom_ext
  rintro ⟨⟨⟨i,j⟩,hij⟩⟩
  exact h i j hij

theorem horizontal_totalEvaluation (i j n : ℕ) (h : i+j=n+1) :
    (E).map (ExternalTensor.horizontal k Ae Be P Q i j n) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i,j),h⟩).hom ≫
      ExternalTensor.horizontal k A B PE QE i j n := by
  cases i with
  | zero => erw [ExternalTensor.horizontal_zero, Functor.map_zero,
      zero_comp, ExternalTensor.horizontal_zero k A B PE QE, comp_zero]
  | succ i =>
    have hij : i+j=n := by omega
    erw [ExternalTensor.horizontal_succ k Ae Be P Q i j n hij,
      (E).map_comp, Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q i j n hij]
    erw [ExternalTensor.horizontal_succ k A B PE QE i j n hij, ← Category.assoc]
    exact congrArg (fun f => f ≫ ExternalTensor.inclusion k A B PE QE i j n hij)
      (horizontal_summand_natural k A B X Y P Q i j n hij h)

theorem vertical_totalEvaluation (i j n : ℕ) (h : i+j=n+1) :
    (E).map (ExternalTensor.vertical k Ae Be P Q i j n) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i,j),h⟩).hom ≫
      ExternalTensor.vertical k A B PE QE i j n := by
  cases j with
  | zero => erw [ExternalTensor.vertical_zero, Functor.map_zero,
      zero_comp, ExternalTensor.vertical_zero k A B PE QE, comp_zero]
  | succ j =>
    have hij : i+j=n := by omega
    erw [ExternalTensor.vertical_succ k Ae Be P Q i j n hij,
      (E).map_units_smul, Linear.units_smul_comp, (E).map_comp, Category.assoc,
      inclusion_totalEvaluationTermIso k A B X Y P Q i j n hij]
    erw [ExternalTensor.vertical_succ k A B PE QE i j n hij, Linear.comp_units_smul,
      ← Category.assoc]
    apply congrArg (fun f => ((-1 : ℤˣ)^i) • f)
    exact congrArg (fun f => f ≫ ExternalTensor.inclusion k A B PE QE i j n hij)
      (vertical_summand_natural k A B X Y P Q i j n hij h)

theorem totalEvaluationTermIso_d (m : ℕ) :
    (totalEvaluationTermIso k A B X Y P Q (m+1)).hom ≫
      (totalEvaluated k A B X Y P Q).d (m+1) m =
    (evaluatedTotal k A B X Y P Q).d (m+1) m ≫
      (totalEvaluationTermIso k A B X Y P Q m).hom := by
  apply evaluatedTotal_hom_ext k A B X Y P Q
  intro i j hij
  symm
  change (E).map (ExternalTensor.inclusion k Ae Be P Q i j (m+1) hij) ≫
    ((E).map ((ExternalTensor.complex k Ae Be P Q).d (m+1) m) ≫
      (totalEvaluationTermIso k A B X Y P Q m).hom) =
    (E).map (ExternalTensor.inclusion k Ae Be P Q i j (m+1) hij) ≫
      ((totalEvaluationTermIso k A B X Y P Q (m+1)).hom ≫
        (totalEvaluated k A B X Y P Q).d (m+1) m)
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_d, (E).map_add,
    Preadditive.add_comp, horizontal_totalEvaluation k A B X Y P Q i j m hij,
    vertical_totalEvaluation k A B X Y P Q i j m hij]
  erw [← Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q i j (m+1) hij,
    Category.assoc, ExternalTensor.inclusion_d, Preadditive.comp_add]

def totalEvaluationIso : evaluatedTotal k A B X Y P Q ≅ totalEvaluated k A B X Y P Q :=
  HomologicalComplex.Hom.isoOfComponents (totalEvaluationTermIso k A B X Y P Q)
    (fun n m h => by
      have hnm : m+1=n := h
      subst n
      exact totalEvaluationTermIso_d k A B X Y P Q m)

end ArExplicit.ExternalBalanced

end

end OAI
