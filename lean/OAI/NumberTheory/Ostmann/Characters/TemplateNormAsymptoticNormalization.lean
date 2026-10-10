import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetCancellation
import OAI.NumberTheory.Ostmann.Characters.TemplateRetainedSquareSum

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateNormAsymptotic
open Filter HistoryFrequencyBudget HistoryFrequencyLabels Arithmetic

theorem leaf_normalization (a m W : ℝ) (j : ℕ) :
    (leafFourierBound*Real.exp ((-a*m+W)/2))^((2^j)*2) =
      (leafFourierBound^((2^j)*2)*Real.exp ((2:ℝ)^j*W))*
        Real.exp (-(2:ℝ)^j*a*m) := by
  rw [mul_pow,← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
  congr 1
  push_cast
  ring_nf

theorem normalized_retained_factor_eventually (j : ℕ) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A : NNReal, ∀ W : ℝ,
      ∀ᶠ m : ℝ in atTop,
        (leafFourierBound*Real.exp ((-a*m+W)/2))^((2^j)*2)*
          historyTotal (ranges a m j) (ReducedFrequencyTree.factor ε A) j [] ≤
          Real.exp (δ*m) := by
  obtain ⟨ε,hε,hbound⟩ := normalized_historyTotal_eventually j ha hδ
  refine ⟨ε,hε,?_⟩
  intro A W
  filter_upwards [hbound A A.property
    (leafFourierBound^((2^j)*2)*Real.exp ((2:ℝ)^j*W))
    (mul_nonneg (pow_nonneg leafFourierBound_pos.le _) (Real.exp_pos _).le)] with m hm
  simpa only [leaf_normalization] using hm

end Ostmann.Characters.TemplateNormAsymptotic

end

end OAI
