import OAI.Geometry.RCD.Sobolev.LocalCutoffLipschitz
import OAI.Geometry.RCD.Sobolev.CompactLipschitzSobolevBound

namespace OAI

/-! # Compact Sobolev realization on a metric ball -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

def radialLocalSobolev (z : X) {r : ℝ} (hr : 0 < r)
    {f : X → ℝ} {L A : ℝ≥0}
    (hf : LipschitzOnWith L f (closedBall z (2*r)))
    (hb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A) : SobolevSpace μ Q :=
  SobolevSpace.ofLipschitzCompact μ Q (radial_local_lipschitz_cutoff z hr hf hb).1
    ((radialCutoff_hasCompactSupport z hr).mul_right)

theorem radialLocalSobolev_coe (z : X) {r : ℝ} (hr : 0 < r)
    {f : X → ℝ} {L A : ℝ≥0}
    (hf : LipschitzOnWith L f (closedBall z (2*r)))
    (hb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A) :
    SobolevSpace.toLp μ Q (radialLocalSobolev μ Q z hr hf hb) =ᵐ[μ]
      fun x => radialCutoff z r x*f x :=
  SobolevSpace.ofLipschitzCompact_coe μ Q _ _

theorem radialLocalSobolev_eq_on_ball (z : X) {r : ℝ} (hr : 0 < r)
    {f : X → ℝ} {L A : ℝ≥0}
    (hf : LipschitzOnWith L f (closedBall z (2*r)))
    (hb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A) :
    SobolevSpace.toLp μ Q (radialLocalSobolev μ Q z hr hf hb) =ᵐ[μ.restrict (closedBall z r)] f := by
  filter_upwards [ae_restrict_of_ae (radialLocalSobolev_coe μ Q z hr hf hb),
    ae_restrict_mem measurableSet_closedBall] with x hx hm
  rw [hx,radialCutoff_eq_one z hr (mem_closedBall'.mp hm),one_mul]

theorem radialLocalSobolev_uniform_bound (z : X) {r : ℝ} (hr : 0 < r)
    (L A : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : X → ℝ)
      (hf : LipschitzOnWith L f (closedBall z (2*r)))
      (hb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A),
      ‖radialLocalSobolev μ Q z hr hf hb‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := compact_lipschitz_sobolev_uniform_bound μ Q
    (isCompact_closedBall z (2*r)) A (A*⟨r⁻¹,inv_nonneg.mpr hr.le⟩+L)
  refine ⟨C,hC,?_⟩
  intro f hf hb
  apply hbound _ (fun x => radialCutoff z r x*f x)
    (radial_local_lipschitz_cutoff z hr hf hb).1
    (radial_local_lipschitz_cutoff z hr hf hb).2
  · intro x hx
    rw [radialCutoff_eq_zero z hr
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hx)),zero_mul]
  · exact radialLocalSobolev_coe μ Q z hr hf hb

end RegularPointCoordinates

end

end OAI
