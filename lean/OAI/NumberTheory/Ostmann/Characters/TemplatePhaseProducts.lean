import OAI.NumberTheory.Ostmann.Construction.CRTDFT

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

abbrev OutputPrimeIndex (H Y:Type*) := (H×Bool)⊕Y

def primeCopyProduct (p:OutputPrimeIndex H Y→ℕ) (t:Bool) : ℕ := ∏h:H,p (.inl (h,t))
def primeOutsideProduct (p:OutputPrimeIndex H Y→ℕ) : ℕ := ∏y:Y,p (.inr y)
def primeCopyOther (p:OutputPrimeIndex H Y→ℕ) (i:H) (t:Bool) : ℕ :=
  ∏h∈Finset.univ.erase i,p (.inl (h,t))
def primeOutsideOther (p:OutputPrimeIndex H Y→ℕ) (i:Y) : ℕ :=
  ∏h∈Finset.univ.erase i,p (.inr h)

omit [DecidableEq H] [DecidableEq Y] in
theorem outputPrimeProduct [DecidableEq H] [DecidableEq Y] (p:OutputPrimeIndex H Y→ℕ) :
    (∏i,p i)=primeCopyProduct p true*primeCopyProduct p false*primeOutsideProduct p := by
  simp only [Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_bool,
    primeCopyProduct,primeOutsideProduct,Finset.prod_mul_distrib]

omit [Fintype Y] [DecidableEq H] [DecidableEq Y] in
theorem primeCopyOther_mul [Fintype Y] [DecidableEq H] [DecidableEq Y]
    (p:OutputPrimeIndex H Y→ℕ) (i:H) (t:Bool) :
    primeCopyOther p i t*p (.inl (i,t))=primeCopyProduct p t :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ i)

omit [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y] in
theorem primeOutsideOther_mul [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]
    (p:OutputPrimeIndex H Y→ℕ) (i:Y) :
    primeOutsideOther p i*p (.inr i)=primeOutsideProduct p :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem otherProduct_copied (p:OutputPrimeIndex H Y→ℕ) (i:H) (t:Bool)
    (hp:p (.inl (i,t))≠0) :
    Construction.otherProduct p (.inl (i,t)) =
      primeCopyOther p i t*primeCopyProduct p (!t)*primeOutsideProduct p := by
  apply mul_right_cancel₀ hp
  rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _),outputPrimeProduct]
  calc
    _ = (primeCopyOther p i t*p (.inl (i,t)))*primeCopyProduct p (!t)*primeOutsideProduct p := by
      rw [primeCopyOther_mul]
      cases t <;> simp only [Bool.not_true,Bool.not_false]
      ac_rfl
    _ = _ := by ring

theorem otherProduct_outside (p:OutputPrimeIndex H Y→ℕ) (i:Y) (hp:p (.inr i)≠0) :
    Construction.otherProduct p (.inr i)=
      primeCopyProduct p true*primeCopyProduct p false*primeOutsideOther p i := by
  apply mul_right_cancel₀ hp
  rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _),outputPrimeProduct]
  calc
    _ = primeCopyProduct p true*primeCopyProduct p false*(primeOutsideOther p i*p (.inr i)) := by
      rw [primeOutsideOther_mul]
    _ = _ := by ring

end Ostmann.Characters.Template

end

end OAI
