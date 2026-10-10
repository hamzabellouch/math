import OAI.NumberTheory.SiegelZeros.Selection.SelectionBridge

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W62

theorem mem_cutoff_floor {H : ℕ} (hH : 0 < H) {T : ℝ} (hT : 0 ≤ T)
    (a : Index H) : a ∈ cutoff H ⌊T⌋₊ ↔
      SiegelZerosAwei.W31.weight (H : ℝ) a.coords ≤ T := by
  rw [mem_cutoff hH, Nat.le_floor_iff hT, real_weight_eq]

theorem rectangle_mem_cutoff {H : ℕ} (hH : 0 < H) {U : ℝ} (hU : 0 ≤ U)
    (a : Index H)
    (h0 : (a.coords 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U)
    (h1 : (a.coords 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U)
    (h2 : (a.coords 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U) :
    a ∈ cutoff H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  apply (mem_cutoff_floor hH (by positivity) a).mpr
  exact SiegelZerosAwei.W31.rectangle_weight_le hH' a.coords h0 h1 h2

theorem rectangle_row_enumerated {H : ℕ} (hH : 0 < H) {U : ℝ} (hU : 0 ≤ U)
    (a : Index H)
    (h0 : (a.coords 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U)
    (h1 : (a.coords 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U)
    (h2 : (a.coords 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U) :
    ∃ n < (cutoff H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊).card,
      enumeration H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ n = a := by
  exact W29.finiteEnumeration_complete _ _ (rectangle_mem_cutoff hH hU a h0 h1 h2)

end WeightedTorusJets.W62


end SiegelZeros

end OAI
