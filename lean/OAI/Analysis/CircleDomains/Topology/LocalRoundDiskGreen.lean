import OAI.Analysis.CircleDomains.Topology.RoundDiskGreenProof
import OAI.Analysis.CircleDomains.Topology.CollarExtension

namespace OAI

/-! The proved disk Green identity requires smoothness only on a
neighborhood of the closed disk, exactly as in the finite-hole application. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma round_disk_green_on (R : ℝ) (hR : 0 < R) (O : Set ℂ) (hO : IsOpen O)
    (hRO : closedBall (0 : ℂ) R ⊆ O) (P Q : ℂ → ℝ)
    (hP : ContDiffOn ℝ ∞ P O) (hQ : ContDiffOn ℝ ∞ Q O) :
    planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ z in ball (0 : ℂ) R, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  obtain ⟨p,hp,hep,_⟩ := exists_smooth_collar_extension hO isClosed_closedBall hRO hP 0
  obtain ⟨q,hq,heq,_⟩ := exists_smooth_collar_extension hO isClosed_closedBall hRO hQ 0
  have hboundary : planarFormIntegral p q (unitCircleParam 0 R) =
      planarFormIntegral P Q (unitCircleParam 0 R) := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have ht : unitCircleParam 0 R t ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff]
      simp only [unitCircleParam,norm_circleMap_zero,abs_of_pos hR,le_refl]
    dsimp only
    rw [hep.self_of_nhdsSet ht,heq.self_of_nhdsSet ht]
  rw [← hboundary,roundDiskGreen hp hq hR]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro z hz
  have hzK : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
  have hpz := hep.filter_mono (nhds_le_nhdsSet hzK)
  have hqz := heq.filter_mono (nhds_le_nhdsSet hzK)
  dsimp only
  rw [hpz.fderiv_eq,hqz.fderiv_eq]

end CircleDomainRigidity

end

end OAI
