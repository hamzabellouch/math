import OAI.NumberTheory.Ostmann.Characters.TemplateBranchProducts
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseTransport
import OAI.NumberTheory.Ostmann.Characters.TemplatePivotCollapse
import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeCharacterTransport
import OAI.NumberTheory.Ostmann.Characters.TemplateSharedCharacterTransport

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

def branchSurvivingPhase (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i))
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (ν:H⊕Y→ℂ) (P:ℕ) (v:ℤ) (t:Bool) : ℂ :=
  ∏i:H⊕Y,survivingPrimeRow (fun h => p (survivingBranchIndex t h)) i
    (χ (survivingBranchIndex t i)) (a (survivingBranchIndex t i)) (ν i)
    (fun h => b (some i) (some h)) (b (some i) none) P v

def branchCopiedTranslation (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (a:∀i,ZMod (p i)) (P v:ℤ) (t:Bool) (i:H) : ℂ :=
  translatedAdditivePhase (a (.inl (i,t))) (v:ZMod (p (.inl (i,t))))
    ((P:ZMod (p (.inl (i,t))))*primeCopyOther p i t*primeOutsideProduct p)

omit [DecidableEq Y] in
@[simp] theorem branchCopiedTranslation_true [DecidableEq Y] (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (a:∀i,ZMod (p i)) (P v:ℤ) (i:H) :
    branchCopiedTranslation p a P v true i=leftTranslation p a P v i := rfl
omit [DecidableEq Y] in
@[simp] theorem branchCopiedTranslation_false [DecidableEq Y] (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (a:∀i,ZMod (p i)) (P v:ℤ) (i:H) :
    branchCopiedTranslation p a P v false i=rightTranslation p a P v i := rfl

theorem branchSurvivingPhase_rows (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i))
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (ν:H⊕Y→ℂ) (P:ℕ) (v:ℤ) (t:Bool) :
    branchSurvivingPhase p χ a b ν P v t =
    ((∏i:H,branchCopiedTranslation p a (P:ℤ) v t i)*
      (∏i:Y,outsideTranslation p a (P:ℤ) v t i))*
    ((∏i:H,ν (.inl i)*oldPrimeCopiedRow p i t (χ (.inl (i,t))) b (P:ℤ))*
      (∏i:Y,ν (.inr i)*oldPrimeSharedRow p i t (χ (.inr i)) b (P:ℤ))) := by
  have hdH (i:H) := otherProduct_branch_copied p t i (Fact.out : (p (.inl (i,t))).Prime).ne_zero
  have hdY (i:Y) := otherProduct_branch_outside p t i (Fact.out : (p (.inr i)).Prime).ne_zero
  simp only [branchSurvivingPhase,Fintype.prod_sum_type,survivingPrimeRow]
  simp_rw [hdH,hdY]
  simp only [survivingBranchIndex,oldPrimeCopiedRow,oldPrimeSharedRow,branchCopiedTranslation,
    outsideTranslation,Int.cast_natCast,mul_assoc,Finset.prod_mul_distrib]
  have hH : (∏ i : H, translatedAdditivePhase (a (.inl (i,t))) (v : ZMod (p (.inl (i,t))))
      ((P : ZMod (p (.inl (i,t)))) * ↑(primeCopyOther p i t * primeOutsideProduct p))) =
      ∏ i : H, translatedAdditivePhase (a (.inl (i,t))) (v : ZMod (p (.inl (i,t))))
        ((P : ZMod (p (.inl (i,t)))) * ↑(primeCopyOther p i t) * ↑(primeOutsideProduct p)) := by
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    rw [Nat.cast_mul, mul_assoc]
  have hY : (∏ i : Y, translatedAdditivePhase (a (.inr i)) (v : ZMod (p (.inr i)))
      ((P : ZMod (p (.inr i))) * ↑(primeCopyProduct p t * primeOutsideOther p i))) =
      ∏ i : Y, translatedAdditivePhase (a (.inr i)) (v : ZMod (p (.inr i)))
        ((P : ZMod (p (.inr i))) * ↑(primeCopyProduct p t) * ↑(primeOutsideOther p i)) := by
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    rw [Nat.cast_mul, mul_assoc]
  erw [hH, hY]
  ac_rfl

end Ostmann.Characters.Template

end

end OAI
