import OAI.Probability.SLE.Angle.TargetDiskMass
import OAI.Probability.SLE.Loewner.ActualApproachAtRadius

namespace OAI

/-! A fixed relative half-plane ball lies inside the prescribed disk compact.
Reaching a sufficiently small radius level forces a positive-time visit there. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma diskMapInv_zero (θ : ℝ) : diskMapInv θ 0=Complex.exp (θ*Complex.I) := by
  simp [diskMapInv]

lemma marked_ball_subset_diskSource {θ : ℝ} (hθ : θ∈Ioo (0:ℝ) Real.pi) :
    ball (diskMapInv θ 0) ((diskMapInv θ 0).im/4) ⊆ diskSourceCompact θ := by
  intro z hz
  rw [diskMapInv_zero] at hz
  let c := Complex.exp (θ*Complex.I)
  have hc : 0<c.im := disk_center_height hθ
  have hnorm : ‖z-c‖<c.im/4 := mem_ball_iff_norm.mp hz
  have hzH : z∈upperHalfPlane := ball_subset_upperHalfPlane (by linarith) hz
  have htri : 2*c.im≤‖z-c‖+‖z-star c‖ := by
    calc
      2*c.im=‖c-star c‖ := (norm_sub_conj_of_im_pos hc).symm
      _=‖(c-z)+(z-star c)‖ := by congr 1; abel
      _≤‖c-z‖+‖z-star c‖ := norm_add_le _ _
      _=‖z-c‖+‖z-star c‖ := by rw [norm_sub_rev c z]
  have hden := norm_pos_iff.mpr (diskMap_denominator_ne hθ hzH)
  have hsmall : ‖diskMap θ z‖<1/4 := by
    rw [diskMap,norm_div]
    apply (div_lt_iff₀ hden).2
    rw [disk_exp_conj]
    change ‖z-c‖ < 1/4*‖z-star c‖
    nlinarith
  refine ⟨diskMap θ z,?_,diskMapInv_diskMap hθ hzH⟩
  exact ball_subset_closedBall (mem_ball_zero_iff.mpr hsmall)

lemma radius_level_visits_diskSource
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (u : ℝ)
    (hu : Real.exp (-u)<1/8)
    (hf : radiusLevelTime γ G (diskMapInv θ 0) u≠∞) :
    ∃ s : ℝ≥0, 0<s ∧ s≤(radiusLevelTime γ G (diskMapInv θ 0) u).toNNReal ∧
      γ s∈ball (diskMapInv θ 0) ((diskMapInv θ 0).im/4) := by
  let z := diskMapInv θ 0
  have hz : 0<z.im := diskMapInv_maps hθ (show (0:ℂ)∈ball 0 1 by simp)
  obtain ⟨hlive,hR⟩ := actual_radius_level_finite_state hw hU z u hf
  have hsmall : fullRadius G (radiusLevelTime γ G z u).toNNReal z<z.im/4 := by
    rw [hR]
    nlinarith
  obtain ⟨s,hs,hnear⟩ := hw.trace_approach_of_radius_lt hU _ z hlive (z.im/4)
    (by positivity) (by linarith) hsmall
  have hmem : γ s∈ball z (z.im/4) := hnear
  refine ⟨s,?_,hs.2,hmem⟩
  apply pos_iff_ne_zero.mpr
  intro he
  rw [he,hw.2.1] at hmem
  have hzero := ball_subset_upperHalfPlane (by linarith : z.im/4≤z.im) hmem
  exact (lt_irrefl (0:ℝ)) hzero

end SLEExactGauge.Target

end

end OAI
