import OAI.Analysis.KadisonSimilarity.Tracial.TracialExpectations

namespace OAI

/-! The base expectation kills every reduced word starting in the other
free factor. This is derived from scalar freeness by trace tests. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {τ : P →ₗ[ℂ] ℂ}
  {A D : StarSubalgebra ℂ P}

namespace TracialExpectation

/-- A reduced word beginning in the other factor has zero base expectation,
including when its final letter belongs to the base algebra. -/
theorem map_reduced_word (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (x : P) (xs : List P) (hword : AlternatingCenteredWord τ D A true (x :: xs)) :
    E.map ((x :: xs).prod) = 0 := by
  apply E.eq_of_pairings hfaithful _ 0 A.zero_mem
  intro c hc
  have hzero := hfree true x xs hword
  have htest : τ (traceCentered τ c * (x :: xs).prod) = 0 := by
    have h := hfree false (traceCentered τ c) (x :: xs)
      (.cons (by simpa using traceCentered_mem τ A hc)
        (traceCentered_trace τ hτ c) hword)
    exact h
  rw [mul_zero, map_zero]
  calc
    τ (c * (x :: xs).prod) =
        τ ((traceCentered τ c + τ c • 1) * (x :: xs).prod) := by
      rw [traceCentered_add]
    _ = 0 := by
      rw [add_mul, smul_mul_assoc, one_mul, map_add, map_smul, htest, hzero]
      simp

/-- A base letter at the front of such a word is removed by bimodularity. -/
theorem map_base_mul_reduced_word (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (a : P) (ha : a ∈ A) (x : P) (xs : List P)
    (hword : AlternatingCenteredWord τ D A true (x :: xs)) :
    E.map (a * (x :: xs).prod) = 0 := by
  rw [E.map_mul_left hfaithful a _ ha, E.map_reduced_word hfaithful hτ hfree x xs hword,
    mul_zero]

end TracialExpectation
end KadisonSimilarity

end

end OAI
