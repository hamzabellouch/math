import OAI.NumberTheory.CubicMoment.Estimates.CoprimeOuterComplete

namespace OAI

/-! Keep the unit zero mode separate when shortening arbitrary rows. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem coprimeGramForm_outer_nonzero {ε R : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 1 ≤ R) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Z N : ℝ),
      0 < Z → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ R*N) →
      ‖coprimeGramForm S u W Z-coprimePoissonDyad S {0} u W Z‖ ≤
        C*(N^3/Z)^ε*(N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ))*
          ∑ a ∈ S, (2:ℝ)^(primaryPrimeFactors a).card*‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimeGramForm_outer_dual_bound hε hε1 hR W hW hW'
  have hRp : 0 < R := zero_lt_one.trans_le hR
  refine ⟨C*outerPowerConstant ε R,mul_pos hC (outerPowerConstant_pos hε hε1 hRp),?_⟩
  intro S u Z N hZ hN hS
  exact (hbound S u Z N hZ hN hS).trans
    (mul_le_mul_of_nonneg_right
      (outer_primal_scale_bound hZ (zero_lt_one.trans_le hN) hRp hC.le hε hε1)
      (Finset.sum_nonneg (fun _ _ => by positivity)))

end CubicFirstMoment

end

end OAI
