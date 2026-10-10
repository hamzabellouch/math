import OAI.NumberTheory.Ostmann.Characters.ParityPermutations
import OAI.NumberTheory.Ostmann.Characters.TemplateGraphFibers

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.ParityActions
attribute [local instance] Classical.propDecidable

def copyUnitEquiv : Bool ≃ ℤˣ := Equiv.ofBijective copyUnit ⟨copyUnit_injective,by
  intro ε
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨true,rfl⟩
  · exact ⟨false,rfl⟩⟩

abbrev ParityFiber (k n : ℕ) (ε : ℤˣ) :=
  {w : Word k (n+1) // rowSign k (n+1) w.val = ε}

def parityFiberEquiv (k n : ℕ) (ε : ℤˣ) : ParityFiber k n ε ≃ Word k n where
  toFun w := ((wordEquiv (schedule k n) n) w.val).1
  invFun w := ⟨(wordEquiv (schedule k n) n).symm
    (w,copyUnitEquiv.symm (ε*(rowSign k n w.val)⁻¹)),by
      rw [rowSign_word_step]
      simp only [Equiv.apply_symm_apply]
      change copyUnitEquiv (copyUnitEquiv.symm (ε*(rowSign k n w.val)⁻¹))*
        rowSign k n w.val = ε
      simp only [Equiv.apply_symm_apply,mul_assoc,inv_mul_cancel,mul_one]⟩
  left_inv w := by
    apply Subtype.ext
    apply (wordEquiv (schedule k n) n).injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    apply copyUnitEquiv.injective
    rw [Equiv.apply_symm_apply]
    have hs := w.property
    rw [rowSign_word_step] at hs
    change ε*(rowSign k n ((wordEquiv (schedule k n) n) w.val).1.val)⁻¹ =
      copyUnit ((wordEquiv (schedule k n) n) w.val).2
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using
      congrArg (fun z : ℤˣ => z*(rowSign k n
        ((wordEquiv (schedule k n) n) w.val).1.val)⁻¹) hs.symm
  right_inv w := by simp only [Equiv.apply_symm_apply]

theorem parityFiber_card (k n : ℕ) (ε : ℤˣ) :
    Fintype.card (ParityFiber k n ε) = 2^n := by
  rw [Fintype.card_congr (parityFiberEquiv k n ε)]
  exact active_word_card k n

abbrev Reassignments (k n m : ℕ) :=
  Fin m → (ε : ℤˣ) → Equiv.Perm (ParityFiber k n ε)

theorem reassignments_card (k n m : ℕ) :
    Fintype.card (Reassignments k n m) = ((Nat.factorial (2^n))^2)^m := by
  have hc (ε : ℤˣ) : Nat.card (ParityFiber k n ε) = 2^n := by
    rw [Nat.card_eq_fintype_card]
    exact parityFiber_card k n ε
  simp only [Reassignments,Fintype.card_fun,Fintype.card_pi,Fintype.card_perm,Fintype.card_fin]
  simp_rw [← Nat.card_eq_fintype_card,hc]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_units_int]

end Ostmann.Characters.Template.ParityActions

end

end OAI
