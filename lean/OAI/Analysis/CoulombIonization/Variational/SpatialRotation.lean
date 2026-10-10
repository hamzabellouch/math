import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketDensity

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
namespace CoulombAtom

abbrev SpatialRotation := unitary (Space →L[ℝ] Space)

instance spatialOperatorContinuousStar : ContinuousStar (Space →L[ℝ] Space) :=
  ⟨ContinuousLinearMap.adjoint.continuous⟩

instance spatialRotationCompact : CompactSpace SpatialRotation := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Space →L[ℝ] Space) 1).of_isClosed_subset isClosed_unitary
  intro g hg
  rw [mem_closedBall_zero_iff]
  exact (CStarRing.norm_of_mem_unitary hg).le

instance spatialRotationMeasurable : MeasurableSpace SpatialRotation := borel SpatialRotation
instance spatialRotationBorel : BorelSpace SpatialRotation := ⟨rfl⟩

def rotationMeasure : Measure SpatialRotation := Measure.haarMeasure (⊤ : PositiveCompacts SpatialRotation)

instance rotationMeasureProbability : IsProbabilityMeasure rotationMeasure := by
  constructor
  exact Measure.haarMeasure_self

instance rotationMeasureLeftInvariant : rotationMeasure.IsMulLeftInvariant :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts SpatialRotation)).IsMulLeftInvariant

def rotate (g : SpatialRotation) : Space ≃ₗᵢ[ℝ] Space := Unitary.linearIsometryEquiv g

lemma rotate_continuous : Continuous (fun p : SpatialRotation × Space => rotate p.1 p.2) :=
  continuous_subtype_val.fst'.clm_apply continuous_snd

@[simp] lemma rotate_mul (g h : SpatialRotation) (x : Space) :
    rotate (g*h) x = rotate g (rotate h x) := rfl

@[simp] lemma rotate_one (x : Space) : rotate 1 x = x := rfl

lemma exists_rotate_norm_eq (x y : Space) (hxy : ‖x‖ = ‖y‖) :
    ∃ g : SpatialRotation, rotate g x = y := by
  obtain ⟨e,he⟩ := exists_orthogonal_map_norm_eq x y hxy
  exact ⟨Unitary.linearIsometryEquiv.symm e, by simpa [rotate] using he⟩

lemma rotation_integral_left (f : SpatialRotation → ℝ) (g : SpatialRotation) :
    (∫ h, f (g*h) ∂rotationMeasure) = ∫ h, f h ∂rotationMeasure :=
  integral_mul_left_eq_self f g

lemma packetDensity_rotate (g : SpatialRotation) (p x : Space) (r : ℝ) :
    packetDensity (rotate g p) r (rotate g x) = packetDensity p r x := by
  simp only [packetDensity_formula,radialPacketBase,norm_smul]
  rw [← (rotate g).map_sub,(rotate g).norm_map]

lemma packetDensity_joint_continuous (r : ℝ) :
    Continuous (fun p : Space × Space => packetDensity p.1 r p.2) := by
  simp_rw [packetDensity_formula]
  exact continuous_const.mul ((radialPacketBase_smooth.continuous.comp
    ((continuous_snd.sub continuous_fst).const_smul r⁻¹)).norm.pow 2)

def averagedPacket (p : Space) (r : ℝ) (x : Space) : ℝ :=
  ∫ g : SpatialRotation, packetDensity (rotate g p) r x ∂rotationMeasure

lemma averagedPacket_radial (p : Space) (r : ℝ) :
    CoulombAnalysis.IsRadial (averagedPacket p r) := by
  intro x y hxy
  obtain ⟨g,hg⟩ := exists_rotate_norm_eq x y hxy
  unfold averagedPacket
  rw [← rotation_integral_left (fun h => packetDensity (rotate h p) r y) g]
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  rw [← hg,rotate_mul,packetDensity_rotate]

lemma averagedPacket_support (p : Space) {r : ℝ} (hr : 0 < r) {x : Space}
    (hx : averagedPacket p r x ≠ 0) : ‖x‖ ≤ ‖p‖+r := by
  by_contra hh
  apply hx
  unfold averagedPacket
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro g
  by_contra hg
  have hdist := packetDensity_support (rotate g p) hr hg
  have hn := norm_add_le (x-rotate g p) (rotate g p)
  rw [sub_add_cancel,(rotate g).norm_map] at hn
  exact hh (by linarith)

lemma rotationalPacket_continuous (p : Space) (r : ℝ) :
    Continuous (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2) := by
  have ha : Continuous (fun q : SpatialRotation × Space => rotate q.1 p) :=
    (continuous_subtype_val.comp continuous_fst).clm_apply continuous_const
  simp_rw [packetDensity_formula]
  exact continuous_const.mul ((radialPacketBase_smooth.continuous.comp
    ((continuous_snd.sub ha).const_smul r⁻¹)).norm.pow 2)

lemma averagedPacket_continuous (p : Space) (r : ℝ) : Continuous (averagedPacket p r) := by
  have hf : Continuous (Function.uncurry (fun x : Space => fun g : SpatialRotation =>
      packetDensity (rotate g p) r x)) := by
    change Continuous (fun q : Space × SpatialRotation => packetDensity (rotate q.2 p) r q.1)
    have ha : Continuous (fun q : Space × SpatialRotation => rotate q.2 p) :=
      (continuous_subtype_val.comp continuous_snd).clm_apply continuous_const
    simp_rw [packetDensity_formula]
    exact continuous_const.mul ((radialPacketBase_smooth.continuous.comp
      ((continuous_fst.sub ha).const_smul r⁻¹)).norm.pow 2)
  have hh := continuous_parametric_integral_of_continuous (μ := rotationMeasure)
    (f := fun x : Space => fun g : SpatialRotation => packetDensity (rotate g p) r x)
    hf isCompact_univ
  unfold averagedPacket
  simpa only [Measure.restrict_univ] using hh

lemma averagedPacket_compact (p : Space) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (averagedPacket p r) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (‖p‖+r))
  intro x hx
  exact mem_closedBall_zero_iff.mpr (averagedPacket_support p hr hx)

lemma rotationalPacket_compact (p : Space) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ.prod (isCompact_closedBall 0 (‖p‖+r)))
  intro q hq
  refine ⟨mem_univ _, mem_closedBall_zero_iff.mpr ?_⟩
  have hd := packetDensity_support (rotate q.1 p) hr hq
  have hh := norm_add_le (q.2-rotate q.1 p) (rotate q.1 p)
  rw [sub_add_cancel,(rotate q.1).norm_map] at hh
  linarith

lemma rotationalPacket_integrable (p : Space) {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2)
      (rotationMeasure.prod volume) :=
  (rotationalPacket_continuous p r).integrable_of_hasCompactSupport (rotationalPacket_compact p hr)

lemma averagedPacket_mass (p : Space) {r : ℝ} (hr : 0 < r) :
    (∫ x, averagedPacket p r x) = 1 := by
  unfold averagedPacket
  rw [← integral_integral_swap (rotationalPacket_integrable p hr)]
  simp only [packetDensity_mass _ hr, integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma averagedPacket_integrable (p : Space) {r : ℝ} (hr : 0 < r) :
    Integrable (averagedPacket p r) :=
  (averagedPacket_continuous p r).integrable_of_hasCompactSupport (averagedPacket_compact p hr)

lemma averagedPacket_memLp (p : Space) {r : ℝ} (hr : 0 < r) :
    MemLp (averagedPacket p r) (5/3) :=
  (averagedPacket_continuous p r).memLp_of_hasCompactSupport (averagedPacket_compact p hr)

lemma packetDensity_nonneg (p : Space) (r : ℝ) (x : Space) : 0 ≤ packetDensity p r x := by
  simp only [packetDensity_formula]
  positivity

lemma averagedPacket_nonneg (p : Space) (r : ℝ) (x : Space) : 0 ≤ averagedPacket p r x :=
  integral_nonneg (fun g => packetDensity_nonneg (rotate g p) r x)

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
