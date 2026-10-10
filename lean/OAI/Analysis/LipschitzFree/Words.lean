import Mathlib

namespace OAI

/-!
# Finite words of prescribed length
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical

def Words (D : Type*) (n : ℕ) := {w : List D // w.length = n}

namespace Words
variable {D : Type*} {n : ℕ}

def equivFun : Words D n ≃ (Fin n → D) where
  toFun w i := w.val.get ⟨i.val, by rw [w.property]; exact i.isLt⟩
  invFun f := ⟨List.ofFn f, List.length_ofFn⟩
  left_inv w := by
    rcases w with ⟨w, rfl⟩
    apply Subtype.ext
    simp
  right_inv f := by funext i; simp

instance [Fintype D] : Fintype (Words D n) := Fintype.ofEquiv _ equivFun.symm

@[simp] theorem card [Fintype D] : Fintype.card (Words D n) = Fintype.card D ^ n := by
  rw [Fintype.card_congr equivFun, Fintype.card_fun, Fintype.card_fin]

end Words
end DiscreteFree
end

end

end OAI
