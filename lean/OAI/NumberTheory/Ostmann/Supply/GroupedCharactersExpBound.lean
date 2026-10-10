import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersBound
import OAI.NumberTheory.Ostmann.Supply.UnitWeightTruncation

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))

theorem localWeightCoefficient_one_eq_mean (K : ℕ) :
    weightCoefficient (fun i => ZMod (p i)) (fun i => localKernel (S i) sparseKernelScale) K 1 =
      (unitWeightMean p S K : ℂ) := by
  rw [localWeightCoefficient_one, ← unitWeightMean_eq_truncation]

theorem norm_localWeightCoefficient_le_exp_band (K : ℕ) (ρ : ∀ i, MulChar (ZMod (p i)) ℂ)
    (hlo : ∀ i, (1/3 : ℝ) ≤ density (S i)) (hhi : ∀ i, density (S i) ≤ 2/3)
    (hg : ∀ i, gamma (S i) ≤ supplyEpsilon^2) {L : ℝ} (hL : 1 ≤ L)
    (hH : (∑ i, 1/(p i : ℝ)) ≤ L) :
    ‖weightCoefficient (fun i => ZMod (p i))
      (fun i => localKernel (S i) sparseKernelScale) K ρ‖ ≤
      Real.exp ((Real.log 1200 + 8*supplyEpsilon)*L) := by
  apply (norm_localWeightCoefficient_le p S K ρ hlo hhi hg).trans
  calc
    _ = Real.exp (Real.log 1200 + 8*supplyEpsilon*(∑ i, 1/(p i : ℝ))) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 1200)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hH
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) supplyEpsilon_pos.le)
      have hc := mul_le_mul_of_nonneg_left hL (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1200))
      nlinarith

end Ostmann.Supply.GroupedCharacters

end

end OAI
