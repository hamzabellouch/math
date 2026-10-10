import OAI.Probability.SLE.Angle.TargetFlowInjectivity

namespace OAI

/-! Identification of the raw selected flow with any positive trajectory.
No geometric trace witness is needed. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma flow_eq_of_positive_trajectory
    (κ : ℝ) (b : Driver) (z : ℂ) (T : ℝ) (hT : 0 ≤ T)
    (Y : ℝ → ℂ) (hY : ContinuousOn Y (Icc 0 T)) (hY0 : Y 0=z)
    (m : ℝ) (hm : 0 < m) (hheight : ∀ t ∈ Icc 0 T, m ≤ (Y t).im)
    (hYd : ∀ t ∈ Ico 0 T, HasDerivWithinAt Y
      ((a κ:ℂ)/(Y t-driverValue b t)) (Ici t) t) :
    Surviving κ b z T ∧ flow κ b z T=Y T := by
  have hs := surviving_of_positive_trajectory κ b z T hT Y hY hY0 m hm hheight hYd
  obtain ⟨k,hk,hkm⟩ := Real.exists_nat_pos_inv_lt hm
  have hk1 : 1 ≤ k := hk
  let j := max k (Nat.find hs)
  have hj : 1 ≤ j := hk1.trans (le_max_left _ _)
  have hinv : (j:ℝ)⁻¹ ≤ (k:ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast (Nat.succ_le_iff.mp hk) : (0:ℝ)<k)
      (by exact_mod_cast (show k ≤ j from le_max_left _ _))
  refine ⟨hs,?_⟩
  rw [← surviving_common_cutoff κ b z T hT hs j (le_max_right _ _)]
  exact cutoffFlow_eq_of_positive_trajectory κ b j hj z T hT Y hY hY0
    (fun t ht => hinv.trans (hkm.le.trans (hheight t ht))) hYd T ⟨hT,le_rfl⟩

end SLEExactGauge.Target

end

end OAI
