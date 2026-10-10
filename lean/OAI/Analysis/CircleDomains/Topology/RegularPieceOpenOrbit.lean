import OAI.Analysis.CircleDomains.Selection.PieceFlowCoordinate

namespace OAI

/-! Each orbit is open in its actual regular level, as witnessed by the
nonzero derivative of its local level coordinate. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def CompactRegularPieceFlow.levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) (t : ℝ) : {z // z ∈ K} :=
  ⟨F.trajectory x t,F.member x t⟩

lemma CompactRegularPieceFlow.continuous_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (x : {z // z ∈ K}) : Continuous (F.levelTrajectory x) :=
  (F.trajectory_smooth x).continuous.subtype_mk _

lemma CompactRegularPieceFlow.isOpenMap_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) : IsOpenMap (F.levelTrajectory x) := by
  intro B hB
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨t,htB,rfl⟩
  obtain ⟨e,ht,he,hs,hi⟩ := exists_smooth_planar_level_chart hf (ha _ (F.scalar x t))
  let U : Set ℝ := (F.trajectory x) ⁻¹' e.source ∩ B
  have hU : U ∈ 𝓝 t := inter_mem
    ((F.trajectory_smooth x).continuous.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds ht))
    (hB.mem_nhds htB)
  let J := (fun s => (e (F.trajectory x s)).2) '' U
  have hJ : J ∈ 𝓝 ((e (F.trajectory x t)).2) :=
    piece_flow_coordinate_open_image F x t e ht he hs hi hU
  have hcont : Continuous (fun y : {z // z ∈ K} => (e y.val).2) :=
    (hs.continuous.comp continuous_subtype_val).snd
  have hsource : {y : {z // z ∈ K} | y.val ∈ e.source} ∈ 𝓝 (F.levelTrajectory x t) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds ht)
  filter_upwards [hsource,hcont.continuousAt.preimage_mem_nhds hJ] with y hyS hyJ
  obtain ⟨s,hsU,hsJ⟩ := hyJ
  have hsS : F.trajectory x s ∈ e.source := hsU.1
  have hp : e (F.trajectory x s) = e y.val := by
    apply Prod.ext
    · rw [he,he,F.scalar]
      exact F.in_level y.property |>.symm
    · exact hsJ
  have hy : F.levelTrajectory x s = y := Subtype.ext (e.injOn hsS hyS hp)
  exact ⟨s,hsU.2,hy⟩

lemma CompactRegularPieceFlow.isOpen_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ} {K : Set ℂ}
    (F : CompactRegularPieceFlow f a K) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // z ∈ K}) : IsOpen (range (F.levelTrajectory x)) := by
  simpa only [image_univ] using F.isOpenMap_levelTrajectory hf ha x univ isOpen_univ

end CircleDomainRigidity

end

end OAI
