import OAI.Analysis.CircleDomains.Probability.MeasurableRaySides
import OAI.Analysis.CircleDomains.Selection.GeometricIndexLocal

namespace OAI

/-! The actual greatest-translate index is Borel in a compact arc sample.
Its definition may use arbitrary Jordan charts; measurability does not. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem measurableSet_rayRightIndices (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) (k : ℤ) :
    MeasurableSet {γ : K | k ∈ rayRightIndices hsch γ.val (hKS γ.property) z} := by
  let : PolishSpace K := hK.isClosed.polishSpace
  apply measurableSet_rayRightFamily hsep
    (fun γ : K => translatedHalfPlaneRay γ.val (hKS γ.property) k)
    (fun γ : K => rayJordan hsch γ.val (hKS γ.property) k)
    (fun γ => rayJordan_spec hsch γ.val (hKS γ.property) k)
    (measurable_translatedCrosscut_family K hKS k)
    (Complex.continuous_re.measurable.comp (measurable_translatedRay_family K hKS k ⟨0, bot_lt_top⟩))
    (fun _ => halfPlaneDisk z) measurable_const
  intro γ
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz)

 theorem measurable_geometricRayIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    Measurable (fun γ : K => geometricRayIndex hsch γ.val (hKS γ.property) z) := by
  apply measurable_of_Ioi
  intro k
  have hm := measurableSet_rayRightIndices hsch hsep K hK hKS z hz (k + 1)
  have he : {γ : K | k + 1 ∈ rayRightIndices hsch γ.val (hKS γ.property) z} =
      (fun γ : K => geometricRayIndex hsch γ.val (hKS γ.property) z) ⁻¹' Ioi k := by
    ext γ
    rw [mem_ofPred_eq, mem_rayRightIndices_iff_le hsch hsep γ.val (hKS γ.property) z hz]
    change k + 1 ≤ geometricRayIndex hsch γ.val (hKS γ.property) z ↔
      k < geometricRayIndex hsch γ.val (hKS γ.property) z
    omega
  exact he ▸ hm

end CircleDomainRigidity

end

end OAI
