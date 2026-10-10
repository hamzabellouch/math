import Mathlib
import OAI.Computability.QuantumFactoring.PackedPrograms

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

lemma packed_injective {n m r : ℕ} :
    Function.Injective (fun xy : Basis n × Basis m => packed r xy.1 xy.2) := by
  intro x y h
  apply Prod.ext
  · funext i
    have hh := congrFun h (⟨i.val,by omega⟩ : Fin (n+m+r))
    simpa only [packed_input] using hh
  · funext i
    have hh := congrFun h (⟨n+i.val,by omega⟩ : Fin (n+m+r))
    simpa only [packed_target] using hh

lemma packed_update_input {n m r : ℕ} (x : Basis n) (y : Basis m) (j : Fin n) (c : Bool) :
    Function.update (packed r x y) (⟨j.val,by omega⟩ : Fin (n+m+r)) c =
      packed r (Function.update x j c) y := by
  funext i
  by_cases hi : i.val=j.val
  · have he : i = (⟨j.val,by omega⟩ : Fin (n+m+r)) := Fin.ext hi
    simp only [he, Function.update_self, packed_input]
  · rw [Function.update_of_ne (by intro h; exact hi (congrArg Fin.val h))]
    unfold packed
    split_ifs with hn hm
    · rw [Function.update_of_ne]
      intro h; exact hi (congrArg Fin.val h)
    · rfl
    · rfl

lemma packed_update_target {n m r : ℕ} (x : Basis n) (y : Basis m) (j : Fin m) (c : Bool) :
    Function.update (packed r x y) (⟨n+j.val,by omega⟩ : Fin (n+m+r)) c =
      packed r x (Function.update y j c) := by
  funext i
  by_cases hi : i.val=n+j.val
  · have he : i = (⟨n+j.val,by omega⟩ : Fin (n+m+r)) := Fin.ext hi
    simp only [he, Function.update_self, packed_target]
  · rw [Function.update_of_ne (by intro h; exact hi (congrArg Fin.val h))]
    unfold packed
    split_ifs with hn hm
    · rfl
    · rw [Function.update_of_ne]
      intro h
      have hh := congrArg Fin.val h
      dsimp at hh
      omega
    · rfl

lemma append_update_left {p b : ℕ} (d : Basis p) (z : Basis b) (j : Fin p) (c : Bool) :
    Function.update (Fin.append d z) (j.castAdd b) c = Fin.append (Function.update d j c) z := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · by_cases hk : k = j
    · subst k; simp
    · rw [Function.update_of_ne (by intro h; apply hk; apply Fin.ext; exact congrArg (fun i : Fin (p+b) => i.val) h),
        Fin.append_left, Fin.append_left, Function.update_of_ne hk]
  · rw [Function.update_of_ne (by intro h; have hh := congrArg Fin.val h; simp at hh; omega),
      Fin.append_right, Fin.append_right]

/-- Taking an adjoint and reading a basis outcome implements exactly the
correlation with the prepared state, without an idealized projection gate. -/
lemma encoded_adjoint_test {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e)
    (U : Matrix (Basis q) (Basis q) ℂ) (v : Basis q) (χ ψ : α → ℂ)
    (h : U.mulVec (basisVector v) = encodeState e χ) :
    U.conjTranspose.mulVec (encodeState e ψ) v = ∑ a, star (χ a)*ψ a := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    matrix_basisVector, Matrix.conjTranspose_apply]
  rw [matrix_basisVector] at h
  apply Finset.sum_congr rfl
  intro a _
  have ha := congrFun h (e a)
  rw [encodeState_at e he] at ha
  rw [ha]
  ring

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
