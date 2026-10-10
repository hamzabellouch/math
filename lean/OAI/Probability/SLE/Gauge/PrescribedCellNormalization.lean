import OAI.Probability.SLE.Gauge.PrescribedRadiusLevels
import OAI.Probability.SLE.Geometry.ArbitraryDiskTail
import OAI.Probability.SLE.Geometry.CenteredCellTail

namespace OAI

/-! The lower-bound grid uses doubled cell radii around each sampled
point. These identities match its threshold with the exact gauge weights. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma cell_subset_ball_at_member {K : Set ℂ} {c x : ℂ} {r : ℝ}
    (hK : K⊆closedBall c (2*r)) (hx : x∈K) : K⊆closedBall x (2*(2*r)) := by
  intro y hy
  have hxc := mem_closedBall.mp (hK hx)
  have hyc := mem_closedBall.mp (hK hy)
  apply mem_closedBall.mpr
  calc
    dist y x ≤ dist y c+dist c x := dist_triangle _ _ _
    _ ≤ 2*r+2*r := add_le_add hyc (by simpa only [dist_comm] using hxc)
    _ = 2*(2*r) := by ring

lemma prescribed_lower_threshold (κ r w : ℝ) (hr : 0<r) :
    ((32768*Real.pi)*(2*r))^dimension κ*(16*w) =
      (16*(65536*Real.pi)^dimension κ)*w*r^Target.d κ := by
  have hd : Target.d κ=dimension κ := by rw [Target.dimension_eq]; rfl
  rw [show (32768*Real.pi)*(2*r)=(65536*Real.pi)*r by ring,
    Real.mul_rpow (by positivity : 0≤65536*Real.pi) hr.le,hd]
  ring

lemma prescribed_lower_radius (κ : ℝ) (W : Target.WienerLaw) (e : Target.Entry)
    {z : ℂ} (hz : 0<z.im) :
    (2*z.im)*Real.exp (-Target.entryPhysicalLevel κ W e (4096*Real.pi) z)=
      (2048*Real.pi)*(2*Target.entryRadius κ W e) := by
  rw [Target.entryPhysicalLevel_radius κ W e (by positivity) hz]
  ring

end SLEExactGauge.Multipoint

end

end OAI
