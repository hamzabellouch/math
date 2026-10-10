import OAI.Analysis.PlanarEndpoint.Information.ChainRule
import OAI.Analysis.PlanarEndpoint.Information.Conditioning
import OAI.Analysis.PlanarEndpoint.Information.FiniteTables
import OAI.Analysis.PlanarEndpoint.Information.Logarithms
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {V W Y S : Type*} [Fintype V] [Fintype W] [Fintype Y] [Fintype S]

lemma expected_conditioning_decrement_nonneg_mass (q : V → Y → ℝ)
    (hq : ∀ v y, 0 ≤ q v y) {L : ℝ} (hL : 1 < L) :
    0 ≤ ∑ v, ∑ y, q v y * (information L (colMass q y / totalMass q) -
      information L (conditionalMass q v y)) := by
  by_cases ht : totalMass q = 0
  · have hzero : ∀ v y, q v y = 0 := by
      intro v y
      apply le_antisymm _ (hq v y)
      exact (le_rowMass q hq v y).trans ((rowMass_le_totalMass q hq v).trans_eq ht)
    simp only [hzero, zero_mul, Finset.sum_const_zero, le_refl]
  have htpos : 0 < totalMass q := lt_of_le_of_ne (totalMass_nonneg q hq) (Ne.symm ht)
  have hcol : ∑ y, colMass q y / totalMass q = 1 := by
    rw [← Finset.sum_div, colMass_sum, div_self ht]
  have hsum : ∑ v, ∑ y, (q v y - rowMass q v * (colMass q y / totalMass q)) = 0 := by
    simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcol, mul_one]
    exact sub_self _
  calc
    _ = ∑ v, ∑ y, (q v y - rowMass q v * (colMass q y / totalMass q)) /
        Real.log L := by
      simp_rw [← Finset.sum_div]
      rw [hsum, zero_div]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro y _
      by_cases hq0 : q v y = 0
      · simp only [hq0, zero_sub, zero_mul]
        exact div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_nonneg (rowMass_nonneg q hq v)
            (div_nonneg (colMass_nonneg q hq y) htpos.le))) (Real.log_pos hL).le
      · have hqy : 0 < q v y := lt_of_le_of_ne (hq v y) (Ne.symm hq0)
        have hr : 0 < rowMass q v := hqy.trans_le (le_rowMass q hq v y)
        have hc : 0 < colMass q y := hqy.trans_le (le_colMass q hq v y)
        have hp : 0 < colMass q y / totalMass q := div_pos hc htpos
        have h := sub_le_mul_log_div (hq v y) (mul_nonneg hr.le hp.le)
          (fun _ => mul_pos hr hp)
        have h' := div_le_div_of_nonneg_right h (Real.log_pos hL).le
        unfold information conditionalMass
        rw [Real.log_div hq0 (mul_pos hr hp).ne', Real.log_mul hr.ne' hp.ne',
          Real.log_div hc.ne' ht] at h'
        rw [Real.log_div hc.ne' ht, Real.log_div hq0 hr.ne']
        convert h' using 1
        ring

def sampledEntropy (L : ℝ) (a : S → ℝ) (v : S → V) (y : S → Y) : ℝ :=
  ∑ s, a s * sampledInformation L a v y s

lemma sampledEntropy_eq (L : ℝ) (a : S → ℝ) (v : S → V) (y : S → Y) :
    sampledEntropy L a v y = conditionalEntropy L (sampledTable a v y) := by
  exact (sampledTable_sum a v y (fun b z =>
    information L (conditionalMass (sampledTable a v y) b z))).symm

lemma sampledEntropy_nonneg (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (v : S → V) (y : S → Y) {L : ℝ} (hL : 1 < L) :
    0 ≤ sampledEntropy L a v y := by
  rw [sampledEntropy_eq]
  exact conditionalEntropy_nonneg _ (sampledTable_nonneg a ha v y) hL

lemma sampledEntropy_conditioning_le (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (v : S → V) (u : S → W) (y : S → Y) {L : ℝ} (hL : 1 < L) :
    sampledEntropy L a (fun s => (v s,u s)) y ≤ sampledEntropy L a v y := by
  apply sub_nonneg.mp
  let q : V → W → Y → ℝ := fun b c z =>
    sampledTable a (fun s => (v s,u s)) y (b,c) z
  let F : (V × W) → Y → ℝ := fun b z =>
    information L (conditionalMass (sampledTable a v y) b.1 z) -
      information L (conditionalMass (sampledTable a (fun s => (v s,u s)) y) b z)
  have heq : sampledEntropy L a v y - sampledEntropy L a (fun s => (v s,u s)) y =
      ∑ s, a s * F (v s,u s) (y s) := by
    simp only [sampledEntropy, sampledInformation, F, Finset.sum_sub_distrib, mul_sub]
  rw [heq, ← sampledTable_sum a (fun s => (v s,u s)) y F, Fintype.sum_prod_type]
  apply Finset.sum_nonneg
  intro b _
  have h := expected_conditioning_decrement_nonneg_mass (q b)
    (fun c z => sampledTable_nonneg a ha _ y (b,c) z) hL
  have hcol : ∀ z, colMass (q b) z = sampledTable a v y b z :=
    sampledTable_pair_first a v u y b
  have ht : totalMass (q b) = rowMass (sampledTable a v y) b :=
    sampledTable_pair_total a v u y b
  simp_rw [hcol, ht] at h
  exact h

omit [Fintype V] in
lemma sampledEntropy_chain (a : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (v : S → V) (u : S → W) (y : S → Y) (L : ℝ) :
    sampledEntropy L a v (fun s => (u s,y s)) =
      sampledEntropy L a v u + sampledEntropy L a (fun s => (v s,u s)) y := by
  unfold sampledEntropy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : a s = 0
  · simp only [hs, zero_mul, zero_add]
  · rw [sampledInformation_chain a ha v u y (lt_of_le_of_ne (ha s) (Ne.symm hs)) L]
    ring

end PlanarEndpoint.TransverseInformation
end

end OAI
