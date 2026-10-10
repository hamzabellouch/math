import OAI.RepresentationTheory.FoulkesHowe.ShiftInjectivity
import OAI.RepresentationTheory.FoulkesHowe.ShiftNilpotence

namespace OAI

noncomputable section

namespace Problem346

open MvPolynomial

variable {K σ : Type*} [Field K] [CharZero K]

/-- An algebraic form of the positive-weight injectivity criterion for polynomial
derivations. The generator condition admits arbitrary spectator variables. -/
theorem derivation_eq_zero_of_positive_weight
    (D E H : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (hED : ⁅E, D⁆ = H) (hHE : ⁅H, E⁆ = (2 : K) • E)
    (hEX : ∀ i : σ, E (E (X i)) = 0)
    (f : MvPolynomial σ K) (p q : ℕ) (hpq : q < p)
    (hf : H f = ((p : K) - q) • f) (hDf : D f = 0) : f = 0 := by
  refine ShiftInjectivity.eq_zero_of_positive_weight D.toLinearMap E.toLinearMap
    H.toLinearMap ?_ ?_ f (p - q) (Nat.sub_pos_of_lt hpq) ?_ hDf ?_
  · intro z
    have hz := congrArg (fun F : Derivation K (MvPolynomial σ K)
      (MvPolynomial σ K) => F z) hED
    simp only [Derivation.commutator_apply] at hz
    change D (E z) = E (D z) - H z
    linear_combination -hz
  · intro z
    have hz := congrArg (fun F : Derivation K (MvPolynomial σ K)
      (MvPolynomial σ K) => F z) hHE
    simp only [Derivation.commutator_apply, Derivation.smul_apply] at hz
    change H (E z) = E (H z) + (2 : K) • E z
    linear_combination hz
  · change H f = ((p - q : ℕ) : K) • f
    simpa only [Nat.cast_sub (Nat.le_of_lt hpq)] using hf
  · exact mvPolynomial_derivation_locally_nilpotent_of_square_zero_X E hEX f

end Problem346

end

end OAI
