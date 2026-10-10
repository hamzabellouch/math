import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialMomentBound

namespace OAI

/-! Polynomial moments with a constant chosen before the packet dimension
and scale count, including for replacement derivative packets. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal

namespace LipschitzHilbert.LinePacketFamily

theorem uniform_polynomial_line_moment (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ),
      0 ≤ B → P.HasLocalBudget B →
      (∀ j i k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k) ξ = 0) →
      (∀ j i k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k) ξ = 0) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching → P.topLength ≤ grid.width →
      ∀ n : ℕ, 1 ≤ n →
      (∫⁻ x, ENNReal.ofReal (P.variation x)^n ∂grid.lineMeasure) ≤
        ENNReal.ofReal ((lineMomentBase P.constant (A*P.constant^2*B+1)
          grid.branching*(n:ℝ))^n)*grid.lineMeasure Set.univ := by
  obtain ⟨A,hA,hm⟩ := uniform_line_moment hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh grid hb hwidth n hn
  have h := hm N κ ι P B hB hbudget hlow hhigh grid hb hwidth n (Nat.cast_nonneg n)
  have hp := line_moment_expression_le P.constant (A*P.constant^2*B+1) grid.branching
    P.constant_pos.le (Nat.cast_nonneg _) n hn
  have hs := h.trans (mul_le_mul' hp le_rfl)
  have hnonneg (x : ℝ) : 0 ≤ P.variation x := cubicVariation_nonneg _ _
  simpa only [ENNReal.rpow_natCast, abs_of_nonneg (hnonneg _)] using hs

end LipschitzHilbert.LinePacketFamily

end

end OAI
