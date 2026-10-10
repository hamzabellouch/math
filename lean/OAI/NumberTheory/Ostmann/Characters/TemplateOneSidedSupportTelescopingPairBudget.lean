import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping

def fixedPairBound (j : ℕ) (W Wc : ℝ) : ℝ :=
  Real.exp Wc*(Arithmetic.leafFourierBound*Real.exp (W/2))^(2^(j+1))

theorem fixedPairBound_nonneg (j : ℕ) (W Wc : ℝ) : 0≤fixedPairBound j W Wc := by
  unfold fixedPairBound
  exact mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (mul_nonneg Arithmetic.leafFourierBound_pos.le (Real.exp_pos _).le) _)

theorem fixedPairBound_le_budget (j : ℕ) (W Wc z L : ℝ) (d : ℕ) {C : ℝ}
    (hC : fixedPairBound j W Wc≤C) :
    fixedPairBound j W Wc≤Real.exp (historyPolynomialCost C z d L) := by
  have hc : 0≤C := (fixedPairBound_nonneg j W Wc).trans hC
  have hm : (1:ℝ)≤(1+(⌊z*L⌋₊:ℝ))^d := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) ⌊z*L⌋₊])
  have hp : C≤historyPolynomialCost C z d L := by
    simpa only [mul_one,historyPolynomialCost] using mul_le_mul_of_nonneg_left hm hc
  exact (hC.trans hp).trans (by linarith [Real.add_one_le_exp (historyPolynomialCost C z d L)])

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
