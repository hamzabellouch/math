import OAI.MeasureTheory.Falconer.Graphs.GraphEnergyEstimate
import OAI.MeasureTheory.Falconer.Graphs.GraphTwoErrors

namespace OAI

/-!
# Arbitrary power decay of the explicit graph-energy error

The derivative order is chosen first. The constants obtained at that order
may then be used in the uniform graph estimate. Both cap and row counts,
and the four model-mass inverses, are included in the polynomial cost.
-/

namespace Falconer
open Set MeasureTheory

theorem capGraphError_arbitrary_power (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ m : ℕ, minOrder ≤ m ∧ ∀ {A C W H B : ℝ},
      0 ≤ A → 0 ≤ C → 0 ≤ W → 0 ≤ H → 0 ≤ B →
      ∀ {R P M₁ M₂ D v τ Cap Q : ℝ} {K S : ℕ},
      1 ≤ R → 0 ≤ P → 0 ≤ D → 0 < τ → 0 ≤ Cap → 0 ≤ Q →
      (K : ℝ) ≤ Cap*R^d → (S : ℝ) ≤ R^(2*d) →
      P*|(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| ≤ R^(5*d) →
      16*D/((2 : ℝ)^v*τ) ≤ Q*R^(-(26*σ)) →
      P*capGraphError d m A C W R (T+(11*d : ℕ)) M₁ M₂ H B D v τ K S ≤
        Cap^2 *
          ((A*(4^m*H*B*B)*(B*B)*(sphereMeasure d).real univ*(4*W))*Q^m +
            (B*B)*(B*B)*C*((sphereMeasure d).real univ)^2) * R^(-T) := by
  obtain ⟨m,hmin,hm⟩ := graph_two_errors_absorption d hσ T minOrder
  refine ⟨m,hmin,?_⟩
  intro A C W H B hA hC hW hH hB R P M₁ M₂ D v τ Cap Q K S
    hR hP hD hτ hCap hQ hK hS hmass hratio
  have hmain := hm hR (Nat.cast_nonneg K) (Nat.cast_nonneg S) hP
    (abs_nonneg ((M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹))) hCap hQ
    (show 0 ≤ A*(4^m*H*B*B)*(B*B)*(sphereMeasure d).real univ*(4*W) by positivity)
    (show 0 ≤ (B*B)*(B*B)*C*((sphereMeasure d).real univ)^2 by positivity)
    (show 0 ≤ 16*D/((2 : ℝ)^v*τ) by positivity) hK hS hmass hratio
  convert hmain using 1
  dsimp [capGraphError]
  ring

end Falconer

end OAI
