import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationDifferential
import OAI.Algebra.AuslanderReiten.Ext.ExternalCubicInclusion
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationCubicSquare

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
private theorem post_natural {C : Type*} [Category C]
    {A B D A' : C} {f : A ⟶ B} {g : B ⟶ D} {u : A ⟶ A'} {v : A' ⟶ D}
    (h : f ≫ g = u ≫ v) {Z : C} (w : D ⟶ Z) :
    f ≫ (g ≫ w) = u ≫ (v ≫ w) := by
  rw [← Category.assoc, h, Category.assoc]

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (r : ∀ n, Q.X (n+3) ⟶ Q.X n)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q

def evaluatedFirstComparison (n : ℕ) : (PE).X (n+3) ⟶ (PE).X n :=
  (EnvelopingBimodule.evaluationFunctor k A X).map (p n)

def evaluatedSecondComparison (n : ℕ) : (QE).X (n+3) ⟶ (QE).X n :=
  (EnvelopingBimodule.evaluationFunctor k B Y).map (r n)

theorem firstCubic_totalEvaluation (n : ℕ) :
    (E).map (ModuleCat.ofHom (ExternalTensor.firstCubic k Ae Be P Q p n)) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (totalEvaluationTermIso k A B X Y P Q (n+3)).hom ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k A B PE QE
        (evaluatedFirstComparison k A X P p) n) := by
  apply evaluatedTotal_hom_ext k A B X Y P Q
  intro i j hij
  have hpost := post_natural (inclusion_totalEvaluationTermIso k A B X Y P Q i j (n+3) hij)
    (ModuleCat.ofHom (ExternalTensor.firstCubic k A B PE QE (evaluatedFirstComparison k A X P p) n))
  erw [hpost, ExternalTensor.inclusion_firstCubic k A B PE QE (evaluatedFirstComparison k A X P p) i j n hij]
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_firstCubic k Ae Be P Q p i j n hij]
  by_cases hi : i < 3
  · have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;>
      change (E).map (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals erw [Functor.map_zero, zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, i=a+3 := ⟨i-3, by omega⟩
    subst i
    erw [ExternalTensor.firstCubicEntry_high k Ae Be P Q p a j n hij,
      ExternalTensor.firstCubicEntry_high k A B PE QE (evaluatedFirstComparison k A X P p) a j n hij,
      (E).map_comp, Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q a j n (by omega)]
    erw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun z => z ≫ ExternalTensor.inclusion k A B PE QE a j n (by omega))
      (firstCubic_summand_natural k A B X Y P Q a j n (by omega) hij (p a))

theorem secondCubic_totalEvaluation (n : ℕ) :
    (E).map (ModuleCat.ofHom (ExternalTensor.secondCubic k Ae Be P Q r n)) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (totalEvaluationTermIso k A B X Y P Q (n+3)).hom ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k A B PE QE
        (evaluatedSecondComparison k B Y Q r) n) := by
  apply evaluatedTotal_hom_ext k A B X Y P Q
  intro i j hij
  have hpost := post_natural (inclusion_totalEvaluationTermIso k A B X Y P Q i j (n+3) hij)
    (ModuleCat.ofHom (ExternalTensor.secondCubic k A B PE QE (evaluatedSecondComparison k B Y Q r) n))
  erw [hpost, ExternalTensor.inclusion_secondCubic k A B PE QE (evaluatedSecondComparison k B Y Q r) i j n hij]
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_secondCubic k Ae Be P Q r i j n hij]
  by_cases hj : j < 3
  · have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj with rfl | rfl | rfl <;>
      change (E).map (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals erw [Functor.map_zero, zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, j=a+3 := ⟨j-3, by omega⟩
    subst j
    erw [ExternalTensor.secondCubicEntry_high k Ae Be P Q r i a n hij,
      ExternalTensor.secondCubicEntry_high k A B PE QE (evaluatedSecondComparison k B Y Q r) i a n hij,
      (E).map_comp, Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q i a n (by omega)]
    erw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun z => z ≫ ExternalTensor.inclusion k A B PE QE i a n (by omega))
      (secondCubic_summand_natural k A B X Y P Q i a n (by omega) hij (r a))

end ArExplicit.ExternalBalanced

end

end OAI
