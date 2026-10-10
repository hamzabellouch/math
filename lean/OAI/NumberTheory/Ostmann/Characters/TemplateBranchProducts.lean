import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseProducts

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {H Y:Type*}

def survivingBranchIndex (t:Bool) : H⊕Y→OutputPrimeIndex H Y
  | .inl i => .inl (i,t)
  | .inr i => .inr i

@[simp] theorem survivingBranchIndex_inl [Fintype H] [Fintype Y]
    [DecidableEq H] [DecidableEq Y] (t:Bool) (i:H) :
    survivingBranchIndex (Y:=Y) t (.inl i)=.inl (i,t) := rfl
@[simp] theorem survivingBranchIndex_inr [Fintype H] [Fintype Y]
    [DecidableEq H] [DecidableEq Y] (t:Bool) (i:Y) :
    survivingBranchIndex (H:=H) t (.inr i)=.inr i := rfl

theorem branch_prime_product [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]
    (p:OutputPrimeIndex H Y→ℕ) (t:Bool) :
    (∏i:H⊕Y,p (survivingBranchIndex t i))=primeCopyProduct p t*primeOutsideProduct p := by
  simp only [Fintype.prod_sum_type,survivingBranchIndex,primeCopyProduct,primeOutsideProduct]

variable [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

theorem otherProduct_branch_copied (p:OutputPrimeIndex H Y→ℕ) (t:Bool) (i:H)
    (hi:p (.inl (i,t))≠0) :
    Construction.otherProduct (fun j => p (survivingBranchIndex t j)) (.inl i)=
      primeCopyOther p i t*primeOutsideProduct p := by
  apply mul_right_cancel₀ hi
  change Construction.otherProduct (fun j => p (survivingBranchIndex t j)) (.inl i)*
    p (survivingBranchIndex t (.inl i))=_
  rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _),branch_prime_product]
  rw [← primeCopyOther_mul p i t]
  ring

theorem otherProduct_branch_outside (p:OutputPrimeIndex H Y→ℕ) (t:Bool) (i:Y)
    (hi:p (.inr i)≠0) :
    Construction.otherProduct (fun j => p (survivingBranchIndex t j)) (.inr i)=
      primeCopyProduct p t*primeOutsideOther p i := by
  apply mul_right_cancel₀ hi
  change Construction.otherProduct (fun j => p (survivingBranchIndex t j)) (.inr i)*
    p (survivingBranchIndex t (.inr i))=_
  rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _),branch_prime_product]
  rw [← primeOutsideOther_mul p i]
  ring

end Ostmann.Characters.Template

end

end OAI
