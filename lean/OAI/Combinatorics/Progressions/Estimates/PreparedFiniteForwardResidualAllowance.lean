import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardMaskBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForward_local_error_budget
    (Pmask Presidual : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog maskLog Eres : ℝ}, C ≤ A → 0 ≤ x →
      maskLog ≤ Pmask.eval₂ (Nat.castRingHom ℝ)
        (preparedFiniteForwardParameter A stageCountConstant n x) →
      Eres ≤ Presidual.eval₂ (Nat.castRingHom ℝ)
        (preparedFiniteForwardParameter A stageCountConstant n x) →
      (preparedFiniteForwardPrefixLog A stageCountConstant n x + maskLog) +
        gainLog + Eres + stageLog + 6 ≤
          preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog := by
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget (Pmask + Presidual)
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog maskLog Eres hCA hx hmask herr
  have hb := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hpoly' := hpoly (preparedFiniteForwardParameter A stageCountConstant n x) hb
  simp only [Polynomial.eval₂_add] at hpoly'
  have hwork : (preparedFiniteForwardParameter A stageCountConstant n x + C) ^ C ≤
      preparedFiniteForwardWork A stageCountConstant n x := by
    have h := preparedFiniteForward_shiftedPower_le_work A C stageCountConstant 0
      (hC.trans hCA) hCA hb
    simpa only [preparedFiniteForwardWork_eq, preparedFiniteForwardParameter_zero] using h
  unfold preparedFiniteForwardModelPrecision
  linarith only [hpoly', hwork, hmask, herr]

end Erdos3.VectorPolynomial

end

end OAI
