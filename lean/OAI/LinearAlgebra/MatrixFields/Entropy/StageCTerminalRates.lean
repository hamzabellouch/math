import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistorySums
import OAI.LinearAlgebra.MatrixFields.Tensors.CWStageCPlacements

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCTerminalRates

open AllFieldHistory AllFieldParameters CWStageCProducts
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sum_populationHistory_rate {K : ℕ} (allocation : Allocation) :
    (∑ h : PopulationHistory K,
      (amount allocation (.partC h.1, h.2) : ℝ) *
        (2 - (binaryParameter (cParameterParent h.1) (cShapeParent h.1) : ℝ)) *
          Real.log 5) =
      ∑ h : BPositive K, (bAmount h.val : ℝ) *
        (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
          Real.log 5 := by
  calc
    _ = ∑ h : PartC K, (partAmount allocation h : ℝ) *
        (2 - (binaryParameter (cParameterParent h) (cShapeParent h) : ℝ)) *
          Real.log 5 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      dsimp only
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hm : (∑ phi : Placement, (amount allocation (.partC h, phi) : ℝ)) =
          (partAmount allocation h : ℝ) := by
        exact_mod_cast sum_placement_amount allocation (.partC h)
      rw [hm]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      simp only [cParameterParent, cShapeParent]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hm : (∑ i : Fin 3, (partAmount allocation (h, i) : ℝ)) =
          (bAmount h.val : ℝ) := by
        exact_mod_cast part_transition allocation h
      rw [hm]

theorem log_populationVolume_eq_bPositive {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : BPositive K, (bAmount h.val : ℝ) *
          (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
            Real.log 5 := by
  rw [log_populationVolume, sum_populationHistory_rate]

theorem normalized_log_populationVolume_eq_bPositive {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (hd : 0 < dilation) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) /
        populationLength (K := K) allocation dilation =
      ∑ h : BPositive K, (bAmount h.val : ℝ) *
        (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
          Real.log 5 := by
  rw [normalized_log_populationVolume allocation dilation hd,
    sum_populationHistory_rate]

theorem normalized_log_populationVolume_allocation_independent {K : ℕ}
    (allocation₁ allocation₂ : Allocation) (dilation₁ dilation₂ : ℕ)
    (hd₁ : 0 < dilation₁) (hd₂ : 0 < dilation₂) :
    Real.log (populationVolume (K := K) allocation₁ dilation₁ : ℝ) /
        populationLength (K := K) allocation₁ dilation₁ =
      Real.log (populationVolume (K := K) allocation₂ dilation₂ : ℝ) /
        populationLength (K := K) allocation₂ dilation₂ := by
  rw [normalized_log_populationVolume_eq_bPositive allocation₁ dilation₁ hd₁,
    normalized_log_populationVolume_eq_bPositive allocation₂ dilation₂ hd₂]

theorem tendsto_normalized_log_populationVolume {K : ℕ} (allocation : Allocation) :
    Filter.Tendsto (fun dilation : ℕ =>
      Real.log (populationVolume (K := K) allocation dilation : ℝ) /
        populationLength (K := K) allocation dilation) Filter.atTop
      (𝓝 (∑ h : BPositive K, (bAmount h.val : ℝ) *
        (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
          Real.log 5)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (normalized_log_populationVolume_eq_bPositive allocation dilation hd).symm

def interiorS2 : ℝ :=
  (positiveSecond.map (fun t =>
    (((below t).filter positive).map (fun u =>
      2 * (secondMass t : ℝ) * (stageBLaw t u : ℝ) *
        (2 - (binaryParameter t u : ℝ)) * Real.log 5)).sum)).sum

theorem bPositive_rate_eq_interior (K : ℕ) :
    (∑ h : BPositive K, (bAmount h.val : ℝ) *
      (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
        Real.log 5) = (K : ℝ) * interiorS2 := by
  simpa only [interiorS2, littleMass_cast, mul_assoc] using
    b_positive_history_sum K
      (fun t u => (2 - (binaryParameter t u : ℝ)) * Real.log 5)

theorem log_populationVolume_eq_interior {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) =
      (K : ℝ) * populationLength (K := K) allocation dilation * interiorS2 := by
  rw [log_populationVolume_eq_bPositive, bPositive_rate_eq_interior]
  ring

theorem normalized_log_populationVolume_eq_interior {K : ℕ} (hK : 0 < K)
    (allocation : Allocation) (dilation : ℕ) (hd : 0 < dilation) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) /
        ((K : ℝ) * populationLength (K := K) allocation dilation) = interiorS2 := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  have hn : (populationLength (K := K) allocation dilation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (AllFieldPopulationCounts.blockLength_pos _ hd))
  rw [log_populationVolume_eq_interior]
  exact mul_div_cancel_left₀ _ (mul_ne_zero hk hn)

end MatrixMultiplication.AllFieldStageCTerminalRates

end

end MatrixAllFields

end OAI
