import OAI.Analysis.CircleDomains.Selection.LevelFlowCoordinate

namespace OAI

/-! Each orbit is open in its actual regular level, as witnessed by the
nonzero derivative of its local level coordinate. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def CompactRegularLevelFlow.levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) (t : ℝ) : {z // f z = a} :=
  ⟨F.trajectory x t,F.scalar x t⟩

lemma CompactRegularLevelFlow.continuous_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (x : {z // f z = a}) : Continuous (F.levelTrajectory x) :=
  (F.trajectory_smooth x).continuous.subtype_mk _

lemma CompactRegularLevelFlow.isOpenMap_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // f z = a}) : IsOpenMap (F.levelTrajectory x) := by
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
    level_flow_coordinate_open_image F x t e ht he hs hi hU
  have hcont : Continuous (fun y : {z // f z = a} => (e y.val).2) :=
    (hs.continuous.comp continuous_subtype_val).snd
  have hsource : {y : {z // f z = a} | y.val ∈ e.source} ∈ 𝓝 (F.levelTrajectory x t) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds ht)
  filter_upwards [hsource,hcont.continuousAt.preimage_mem_nhds hJ] with y hyS hyJ
  obtain ⟨s,hsU,hsJ⟩ := hyJ
  have hsS : F.trajectory x s ∈ e.source := hsU.1
  have hp : e (F.trajectory x s) = e y.val := by
    apply Prod.ext
    · rw [he,he,F.scalar,y.property]
    · exact hsJ
  have hy : F.levelTrajectory x s = y := Subtype.ext (e.injOn hsS hyS hp)
  exact ⟨s,hsU.2,hy⟩

lemma CompactRegularLevelFlow.isOpen_range_levelTrajectory {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (x : {z // f z = a}) : IsOpen (range (F.levelTrajectory x)) := by
  simpa only [image_univ] using F.isOpenMap_levelTrajectory hf ha x univ isOpen_univ

end CircleDomainRigidity

end

end OAI
