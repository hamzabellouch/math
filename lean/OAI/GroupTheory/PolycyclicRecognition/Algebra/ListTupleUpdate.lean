import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! # A tuple update as a prefix, one entry, and a suffix -/

namespace PolycyclicRecognition
variable {A : Type}

theorem list_ofFn_update_set {n : ℕ} (v : Fin n → A) (i : Fin n) (a : A) :
    List.ofFn (Function.update v i a) = (List.ofFn v).set i.val a := by
  classical
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j < n := by simpa using hj
    by_cases hi : j = i.val
    · subst j
      simp [List.getElem_ofFn, Function.update]
    · simp [List.getElem_ofFn, Function.update, Fin.ext_iff,
        hi, Ne.symm hi]

theorem list_ofFn_update_split {n : ℕ} (v : Fin n → A) (i : Fin n) (a : A) :
    List.ofFn (Function.update v i a) =
      (List.ofFn v).take i.val ++ a :: (List.ofFn v).drop (i.val + 1) := by
  classical
  rw [list_ofFn_update_set, List.set_eq_take_append_cons_drop]
  simp only [List.length_ofFn, i.isLt, ↓reduceIte]

end PolycyclicRecognition

end OAI
