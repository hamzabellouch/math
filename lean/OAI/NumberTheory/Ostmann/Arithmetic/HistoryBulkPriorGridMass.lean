import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeProgression PrimeCellReplacement
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def bulkNormalizer (L : ℝ) (E : Finset ℕ) : ℝ := harmonicPrimeMass (bulkPrimeBand L E)
def bulkWeight (L : ℝ) (E : Finset ℕ) (p : ℕ) : ℝ := (bulkNormalizer L E*(p : ℝ))⁻¹
def bulkPointCap (L : ℝ) (E : Finset ℕ) : ℝ := Real.exp (-bulkLogLower L)/bulkNormalizer L E
def bulkRestorationCap (L : ℝ) (E : Finset ℕ) : ℝ := ((E.card : ℝ)+1)*bulkPointCap L E

theorem bulkWeight_nonneg (L : ℝ) (E : Finset ℕ) (p : ℕ) : 0 ≤ bulkWeight L E p := by
  apply inv_nonneg.mpr
  apply mul_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))

theorem bulkWeight_le_pointCap (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < bulkNormalizer L E) {p : ℕ} (hp : p ∈ bulkClosedSupport L) :
    bulkWeight L E p ≤ bulkPointCap L E := by
  have hm := (mem_bulkClosedSupport L p).mp hp
  have hl := Real.exp_le_exp.mpr hm.2.1
  rw [Real.exp_log (by exact_mod_cast hm.1.pos : (0 : ℝ) < p)] at hl
  have hi := one_div_le_one_div_of_le (Real.exp_pos (bulkLogLower L)) hl
  rw [one_div, one_div, ← Real.exp_neg] at hi
  unfold bulkWeight bulkPointCap
  rw [mul_inv_rev, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr hZ.le)

theorem bulkWeight_source_sum (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < bulkNormalizer L E) :
    ∑ p ∈ bulkPrimeBand L E, bulkWeight L E p = 1 := by
  have he (p : ℕ) : bulkWeight L E p = ((1 : ℝ)/p)/bulkNormalizer L E := by
    simp only [bulkWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
  simp_rw [he]
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

theorem bulkWeight_restoration_bound (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < bulkNormalizer L E) :
    0 ≤ (∑ p ∈ bulkClosedSupport L, bulkWeight L E p)-1 ∧
    (∑ p ∈ bulkClosedSupport L, bulkWeight L E p)-1 ≤ bulkRestorationCap L E := by
  have hc : 0 ≤ bulkPointCap L E := div_nonneg (Real.exp_pos _).le hZ.le
  have hd := deletion_error (bulkClosedSupport L) (bulkRemoved L E) (bulkWeight L E) hc
    (fun p hp => ⟨bulkWeight_nonneg L E p, bulkWeight_le_pointCap L E hZ hp⟩)
  rw [← bulkPrimeBand_eq_closed_sdiff, bulkWeight_source_sum L E hZ] at hd
  refine ⟨hd.1, hd.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast bulkRemoved_card_le L E) hc

theorem bulkRestorationCap_le_three (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < bulkNormalizer L E) (hE : E.card ≤ 2) :
    bulkRestorationCap L E ≤ 3*Real.exp (-bulkLogLower L)/bulkNormalizer L E := by
  have he : (E.card : ℝ)+1 ≤ 3 := by exact_mod_cast (by omega : E.card+1 ≤ 3)
  simpa only [bulkRestorationCap, bulkPointCap, mul_div_assoc] using
    mul_le_mul_of_nonneg_right he (div_nonneg (Real.exp_pos _).le hZ.le)

theorem bulkSource_mass (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (p : (bulkPrimeSource L E hZ).Sample) :
    (bulkPrimeSource L E hZ).law.mass p = bulkWeight L E p.val := by
  simp only [bulkPrimeSource] at p ⊢
  rw [harmonicPrimeSource_mass]
  simp only [bulkWeight, bulkNormalizer, one_div, mul_comm]

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
