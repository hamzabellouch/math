import OAI.Algebra.AuslanderReiten.Bar.NativeBarEvaluation
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationCubic
import OAI.Algebra.AuslanderReiten.Ext.ExternalComplexCubicNatural

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
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
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q
local notation "PM" => ModuleBar.complex k A M
local notation "QN" => ModuleBar.complex k B N

def barCubic (p : AbsoluteBar.Cochain3 k A) (n : ℕ) : (P).X (n+3) ⟶ (P).X n :=
  ConcreteCategory.ofHom (C := ModuleCat (A ⊗[k] Aᵐᵒᵖ))
    (AbsoluteBar.suffixComparisonMap k A p n)

def nativeTotalBarIso : evaluatedTotal k A B X Y P Q ≅ ExternalTensor.complex k A B PM QN :=
  totalEvaluationIso k A B X Y P Q ≪≫
    ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
      (BarBalanced.nativeComplexIso k B N)

private theorem compose_squares {C : Type*} [Category C]
    {A B C' A' B' C'' : C} {f : A ⟶ A'} {g : B ⟶ B'} {h : C' ⟶ C''}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : B ⟶ C'} {b' : B' ⟶ C''}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) :
    f ≫ (a' ≫ b') = (a ≫ b) ≫ h := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

theorem firstCubic_nativeFactors (p : AbsoluteBar.Cochain3 k A) (n : ℕ) :
    ModuleCat.ofHom (ExternalTensor.firstCubic k A B PE QE
      (evaluatedFirstComparison k A X P (barCubic k A p)) n) ≫
      (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f n =
    (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k A B PM QN (ModuleBar.cubicMap k A M p) n) := by
  apply ExternalTensor.firstCubic_complexMap k A B
  intro j
  exact BarBalanced.nativeComplexIso_cubic k A M p j

theorem secondCubic_nativeFactors (p : AbsoluteBar.Cochain3 k B) (n : ℕ) :
    ModuleCat.ofHom (ExternalTensor.secondCubic k A B PE QE
      (evaluatedSecondComparison k B Y Q (barCubic k B p)) n) ≫
      (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f n =
    (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k A B PM QN (ModuleBar.cubicMap k B N p) n) := by
  apply ExternalTensor.secondCubic_complexMap k A B
  intro j
  exact BarBalanced.nativeComplexIso_cubic k B N p j

theorem nativeTotalBarIso_first (p : AbsoluteBar.Cochain3 k A) (n : ℕ) :
    (productEvaluation k A B X Y).map
      (ModuleCat.ofHom (ExternalTensor.firstCubic k Ae Be P Q (barCubic k A p) n)) ≫
      (nativeTotalBarIso k A B M N).hom.f n =
    (nativeTotalBarIso k A B M N).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k A B PM QN (ModuleBar.cubicMap k A M p) n) := by
  exact compose_squares
    (firstCubic_totalEvaluation k A B X Y P Q (barCubic k A p) n)
    (firstCubic_nativeFactors k A B M N p n)

theorem nativeTotalBarIso_second (p : AbsoluteBar.Cochain3 k B) (n : ℕ) :
    (productEvaluation k A B X Y).map
      (ModuleCat.ofHom (ExternalTensor.secondCubic k Ae Be P Q (barCubic k B p) n)) ≫
      (nativeTotalBarIso k A B M N).hom.f n =
    (nativeTotalBarIso k A B M N).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k A B PM QN (ModuleBar.cubicMap k B N p) n) := by
  exact compose_squares
    (secondCubic_totalEvaluation k A B X Y P Q (barCubic k B p) n)
    (secondCubic_nativeFactors k A B M N p n)

end ArExplicit.ExternalBalanced

end

end OAI
