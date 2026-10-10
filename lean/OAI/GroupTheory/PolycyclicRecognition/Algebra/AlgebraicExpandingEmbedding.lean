import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

namespace OAI

/-! # An expanding complex embedding of a nontorsion algebraic integer

This is the integral number-field case of the norm-changing step. General
finitely generated coefficient fields and nonintegral elements remain
separate obligations.
-/

noncomputable section
namespace PolycyclicRecognition

theorem integral_nontorsion_has_expanding_complex_embedding
    {K : Type*} [Field K] [NumberField K] (z : K) (hz : z ≠ 0)
    (hi : IsIntegral ℤ z) (hnt : ∀ m : ℕ, 0 < m → z ^ m ≠ 1) :
    ∃ σ : K →+* ℂ, 1 < ‖σ z‖ := by
  by_contra! h
  obtain ⟨m, hm, he⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hz hi h
  exact hnt m hm he

end PolycyclicRecognition

end

end OAI
