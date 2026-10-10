import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryCostSum

namespace OAI

/-! # Actual logarithmic bins in a fixed power auxiliary band -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

noncomputable def auxiliaryLogBins (H α β X : ℝ) : Finset ℕ :=
  Icc ⌊H*Real.log (X^α)⌋₊ ⌊H*Real.log (X^β)⌋₊

lemma auxiliary_log_bins_card {H α β X : ℝ} (hH : 0 ≤ H)
    (hβ : 0 ≤ β) (hX : 0 < X) (hlog : 1 ≤ Real.log X) :
    ((auxiliaryLogBins H α β X).card:ℝ) ≤ (H*β+1)*Real.log X := by
  have hX1 : 1 ≤ X := by linarith [Real.log_le_sub_one_of_pos hX]
  have hQ : 1 ≤ X^β := Real.one_le_rpow hX1 hβ
  have hh := mrt_log_bin_card (P := X^α) hH hQ
  change ((auxiliaryLogBins H α β X).card:ℝ) ≤ _ at hh
  rw [Real.log_rpow hX] at hh
  nlinarith

lemma auxiliary_log_bins_endpoints {H α β X : ℝ} (hH : 1 ≤ H)
    (hβ : 0 ≤ β) (hX : 1 ≤ X) {k : ℕ} (hk : k ∈ auxiliaryLogBins H α β X) :
    Real.exp (-1)*X^α ≤ mrtPrimeLogLower H k ∧ mrtPrimeLogLower H k ≤ X^β := by
  exact mrt_log_bin_endpoints hH (Real.rpow_pos_of_pos (by linarith) _)
    (Real.one_le_rpow hX hβ) hk

lemma auxiliary_log_bins_mem {H α β X : ℝ} (hH : 0 ≤ H) (hX : 0 < X)
    {p : ℕ} (hp : p ∈ mrtPrimeBand (X^α) (X^β)) :
    mrtPrimeLogBin H p ∈ auxiliaryLogBins H α β X := by
  have ha := Real.rpow_pos_of_pos hX α
  have hb := Real.rpow_pos_of_pos hX β
  have hh := mrtPrimeBand_bounds ha.le hb.le hp
  exact mrt_prime_log_bin_range hH ha hh.1.le hh.2

end JointDickman

end OAI
