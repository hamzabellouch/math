import Mathlib
import OAI.Analysis.FreeWords.RestrictedDerivationDefinitions
import OAI.Analysis.FreeWords.ScalarMatrixCommutator

namespace OAI

noncomputable section

namespace KKMatrixHilbert

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem controlled_lift_commutator {n d : ℕ}
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ a, ρ a ∈ S) (h : H →L[ℂ] H) (_ : IsSelfAdjoint h)
    (s : unitary (Matrix (Fin n) (Fin n) (H →L[ℂ] H)))
    (hs : ∀ i j, s.val i j ∈ ρ.range) :
    ‖matrixOperator (Matrix.diagonal fun _ : Fin n => h) * matrixOperator s.val -
      matrixOperator s.val * matrixOperator (Matrix.diagonal fun _ : Fin n => h)‖ ≤
        2 * ‖restrictedDerivation S h‖ := by
  apply scalar_matrix_commutator_bound ρ h _ _ s hs
  intro u
  let a : S := ⟨ρ u.val,hρ u.val⟩
  have ha : a ∈ unitary S := by
    constructor
    · apply Subtype.ext
      change star (ρ u.val) * ρ u.val = 1
      rw [←map_star,←map_mul,u.property.1,map_one]
    · apply Subtype.ext
      change ρ u.val * star (ρ u.val) = 1
      rw [←map_star,←map_mul,u.property.2,map_one]
  have hnorm : ‖a‖ ≤ 1 := by
    cases subsingleton_or_nontrivial S with
    | inl h => have := h; simp [Subsingleton.elim a 0]
    | inr h => have := h; exact (CStarRing.norm_of_mem_unitary ha).le
  change ‖restrictedDerivation S h a‖ ≤ ‖restrictedDerivation S h‖
  calc
    _ ≤ ‖restrictedDerivation S h‖ * ‖a‖ := (restrictedDerivation S h).le_opNorm a
    _ ≤ ‖restrictedDerivation S h‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := mul_one _

end

end KKMatrixHilbert
end

end OAI
