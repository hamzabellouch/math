import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActionWordFiltration

namespace OAI

/-! # Transport of mixed operator words through a linear map -/

namespace PolycyclicRecognition

variable {K V U I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]

theorem actionOperatorWord_intertwines
    (D : I → Module.End K V) (E : I → Module.End K U) (q : V →ₗ[K] U)
    (h : ∀ i v, q (D i v) = E i (q v)) (w : List I) (v : V) :
    q (actionOperatorWord D w v) = actionOperatorWord E w (q v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change q (D i (actionOperatorWord D w v)) = E i (actionOperatorWord E w (q v))
    rw [h, ih]

end PolycyclicRecognition

namespace PolycyclicRecognition

variable {K L V U I : Type*} [Field K] [Field L] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module L U]

theorem actionOperatorWord_intertwines_function
    (D : I → Module.End K V) (E : I → Module.End L U) (q : V → U)
    (h : ∀ i v, q (D i v) = E i (q v)) (w : List I) (v : V) :
    q (actionOperatorWord D w v) = actionOperatorWord E w (q v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change q (D i (actionOperatorWord D w v)) = E i (actionOperatorWord E w (q v))
    rw [h, ih]

theorem actionOperatorWord_zero_of_matching_generators
    {J : Type*} (D : I → Module.End K V) (E : J → Module.End K V)
    (hmatch : ∀ i, ∃ j, D i = E j) (c : ℕ)
    (hE : ∀ w : List J, w.length = c → actionOperatorWord E w = 0) :
    ∀ w : List I, w.length = c → actionOperatorWord D w = 0 := by
  classical
  choose f hf using hmatch
  have he (w : List I) : actionOperatorWord D w = actionOperatorWord E (w.map f) := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      change D i * actionOperatorWord D w = E (f i) * actionOperatorWord E (w.map f)
      rw [hf, ih]
  intro w hw
  rw [he]
  exact hE _ (by simpa only [List.length_map] using hw)

end PolycyclicRecognition

end OAI
