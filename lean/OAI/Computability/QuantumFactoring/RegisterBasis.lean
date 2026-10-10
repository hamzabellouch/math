import Mathlib
import OAI.Computability.QuantumFactoring.RegisterCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Replace just one placed register, keeping every other physical wire. -/
noncomputable def Register.replace {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p) : Basis q :=
  w.split.symm (y, (w.split x).2)

lemma Register.replace_inside {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p)
    (i : Fin p) : w.replace x y (w i) = y i := by
  have h := congrArg Prod.fst (w.split.apply_symm_apply (y, (w.split x).2))
  exact congrFun h i

lemma Register.replace_outside {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p)
    (i : w.Unused) : w.replace x y i.val = x i.val := by
  have h := congrArg Prod.snd (w.split.apply_symm_apply (y, (w.split x).2))
  exact congrFun h i

lemma Register.pairState_basis {p q : ℕ} (w : Register p q) (x : Basis q) :
    w.pairState (basisVector (x ∘ w)) (basisVector (w.split x).2) = basisVector x := by
  classical
  funext y
  change (if (w.split y).1 = (w.split x).1 then (1 : ℂ) else 0) *
    (if (w.split y).2 = (w.split x).2 then 1 else 0) = if y = x then 1 else 0
  by_cases hy : y = x
  · subst y; simp
  · have hh : ¬ ((w.split y).1 = (w.split x).1 ∧ (w.split y).2 = (w.split x).2) := by
      intro h; exact hy (w.split.injective (Prod.ext h.1 h.2))
    rcases not_and_or.mp hh with h | h <;> simp [hy,h]

lemma Register.pairState_replace_basis {p q : ℕ} (w : Register p q) (x : Basis q) (v : Basis p) :
    w.pairState (basisVector v) (basisVector (w.split x).2) = basisVector (w.replace x v) := by
  have h := w.pairState_basis (w.replace x v)
  have he : w.split (w.replace x v) = (v, (w.split x).2) := w.split.apply_symm_apply _
  change w.pairState (basisVector (w.split (w.replace x v)).1)
    (basisVector (w.split (w.replace x v)).2) = _ at h
  simpa only [he] using h

lemma placed_basis {p q : ℕ} (w : Register p q) (ops : List (Instruction p))
    (x : Basis q) (v : Basis p)
    (h : (programMatrix ops).mulVec (basisVector (x ∘ w)) = basisVector v) :
    (programMatrix (ops.map (Instruction.place w))).mulVec (basisVector x) =
      basisVector (w.replace x v) := by
  rw [programMatrix_place, ← w.pairState_basis x, w.liftMatrix_pairState, h,
    w.pairState_replace_basis]

/-- SWAP is three named CNOT gates, not an extra primitive. -/
def swapAt {q : ℕ} (a b : Fin q) (h : a ≠ b) : List (Instruction q) :=
  [cnotAt a b h, cnotAt b a h.symm, cnotAt a b h]

lemma swapAt_basis {q : ℕ} (a b : Fin q) (h : a ≠ b) (x : Basis q) :
    (programMatrix (swapAt a b h)).mulVec (basisVector x) =
      basisVector (x ∘ Equiv.swap a b) := by
  rw [swapAt, programMatrix_cons, programMatrix_cons, programMatrix_singleton,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    cnotAt_basis, cnotAt_basis, cnotAt_basis]
  congr 1
  funext i
  by_cases ha : i = a
  · subst i; simp only [Function.comp_apply, Function.update_self,
      Function.update_of_ne h, Function.update_of_ne h.symm, Equiv.swap_apply_left]
    cases x a <;> cases x b <;> rfl
  · by_cases hb : i = b
    · subst i; simp [Function.comp_apply, h, h.symm]
    · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne ha hb,
        Function.update_of_ne ha, Function.update_of_ne hb]

end ExactQuantumFactoring


end

end OAI
