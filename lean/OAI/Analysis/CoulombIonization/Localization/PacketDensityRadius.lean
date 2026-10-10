import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpatialRotation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
namespace CoulombAtom

lemma packetDensity_radius (p : Space) {r : ℝ} (hr : 0 < r) (g : SpatialRotation)
    {x : Space} (hx : packetDensity (rotate g p) r x ≠ 0) : ‖x‖ ≤ ‖p‖+r := by
  have hd := packetDensity_support (rotate g p) hr hx
  have hh := norm_add_le (x-rotate g p) (rotate g p)
  rw [sub_add_cancel,(rotate g).norm_map] at hh
  linarith

lemma rotationPacket_kernel_integrable (p z : Space) {r : ℝ} (hr : 0 < r)
    (hz : ‖p‖+r < ‖z‖) :
    Integrable (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2 / ‖z-q.2‖)
      (rotationMeasure.prod volume) := by
  have hc := (rotationalPacket_continuous p r).measurable
  have hd : Measurable (fun q : SpatialRotation × Space => ‖z-q.2‖) :=
    (continuous_const.sub continuous_snd).norm.measurable
  apply ((rotationalPacket_integrable p hr).div_const (‖z‖-(‖p‖+r))).mono'
    (hc.div hd).aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  change ‖packetDensity (rotate q.1 p) r q.2 / ‖z-q.2‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg
    (packetDensity_nonneg _ _ _) (norm_nonneg _))]
  by_cases hq : packetDensity (rotate q.1 p) r q.2 = 0
  · simp only [hq,zero_div,le_refl]
  · have hp := packetDensity_radius p hr q.1 hq
    have hn := norm_add_le (z-q.2) q.2
    rw [sub_add_cancel] at hn
    exact div_le_div_of_nonneg_left (packetDensity_nonneg _ _ _) (by linarith) (by linarith)

theorem rotation_kernel_newton (p z : Space) (hz : ‖p‖ < ‖z‖) :
    (∫ g : SpatialRotation, 1 / ‖z-rotate g p‖ ∂rotationMeasure) = 1 / ‖z‖ := by
  let r : ℝ := (‖z‖-‖p‖)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hzr : ‖p‖+r < ‖z‖ := by dsimp [r]; linarith
  have he (g : SpatialRotation) : r < ‖z-rotate g p‖ := by
    have hn := norm_add_le (z-rotate g p) (rotate g p)
    rw [sub_add_cancel,(rotate g).norm_map] at hn
    linarith
  have hn := CoulombAnalysis.tfPotential_newton_exterior
    (averagedPacket_integrable p hr) (averagedPacket_memLp p hr) (averagedPacket_radial p r)
    (show 0 ≤ ‖p‖+r by positivity) (fun x hx => averagedPacket_support p hr hx) hzr
  rw [averagedPacket_mass p hr] at hn
  calc
    _ = ∫ g : SpatialRotation, ∫ x : Space,
        packetDensity (rotate g p) r x / ‖z-x‖ ∂volume ∂rotationMeasure := by
      apply integral_congr_ae (Eventually.of_forall fun g => ?_)
      exact (packetDensity_potential (rotate g p) hr (he g)).symm
    _ = ∫ x : Space, ∫ g : SpatialRotation,
        packetDensity (rotate g p) r x / ‖z-x‖ ∂rotationMeasure :=
      integral_integral_swap (rotationPacket_kernel_integrable p z hr hzr)
    _ = _ := by
      simp_rw [integral_div]
      exact hn

lemma rotation_kernel_integrable (p z : Space) (hz : ‖p‖ < ‖z‖) :
    Integrable (fun g : SpatialRotation => 1 / ‖z-rotate g p‖) rotationMeasure := by
  have hc : Continuous (fun g : SpatialRotation => rotate g p) :=
    continuous_subtype_val.clm_apply continuous_const
  have hd : ∀ g : SpatialRotation, ‖z-rotate g p‖ ≠ 0 := by
    intro g hg
    have he := sub_eq_zero.mp (norm_eq_zero.mp hg)
    have hh : ‖z‖ = ‖p‖ := by rw [he,(rotate g).norm_map]
    linarith
  exact (continuous_const.div (continuous_const.sub hc).norm hd).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
