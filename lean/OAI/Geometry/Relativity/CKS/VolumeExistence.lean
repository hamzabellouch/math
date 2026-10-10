import OAI.Geometry.Relativity.CKS.VolumeRegularity
import OAI.Geometry.Relativity.CKS.VolumeCompatibility
import OAI.Geometry.Relativity.CKS.MeasureGlue

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

theorem exists_volume [SecondCountableTopology M] (g : Metric (M := M)) :
    ∃ ν : Measure M, IsVolume g ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact ⟨0, fun x => isEmptyElim x⟩
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact exists_measure_of_compatible (fun x : M => (extChartAt I x).source)
      (fun x => (isOpen_extChartAt_source x).measurableSet) (localVolume g)
      (localVolume_compatible g) f (eq_univ_of_univ_subset hf)

lemma volume_on_subset [SecondCountableTopology M] (g : Metric (M := M))
    {ν : Measure M} (hν : IsVolume g ν)
    (x : M) {s : Set M} (hs : s ⊆ (extChartAt I x).source) :
    ν s = (localVolume g x) s := by
  rw [← hν x, Measure.restrict_apply' (isOpen_extChartAt_source x).measurableSet,
    inter_eq_left.mpr hs]

variable [SecondCountableTopology M]

lemma volume_locallyFinite (g : Metric (M := M)) {ν : Measure M} (hν : IsVolume g ν) :
    IsLocallyFiniteMeasure ν := by
  constructor
  intro x
  have hx : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  obtain ⟨δ,hδ,hbound⟩ := (Metric.continuousWithinAt_iff.mp
    (chartDensity_continuousOn g x _ hx)) 1 zero_lt_one
  let V := (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) δ
  have hVo : IsOpen V := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, by simpa using hδ⟩
  refine ⟨V, hVo.mem_nhds hxV, ?_⟩
  rw [volume_on_subset g hν x (inter_subset_left), localVolume_apply g x hVo.measurableSet]
  let C := chartDensity g x (extChartAt I x x) + 1
  have hpre : chartPreimage x V ⊆ Metric.ball (extChartAt I x x) δ := by
    intro y hy
    have he : extChartAt I x ((extChartAt I x).symm y) = y := (extChartAt I x).right_inv hy.2
    simpa only [mem_preimage,he] using hy.1.2
  have hden : ∀ y ∈ chartPreimage x V, chartDensity g x y ≤ C := by
    intro y hy
    have hb := hbound hy.2 (hpre hy)
    rw [Real.dist_eq] at hb
    exact le_of_lt (by linarith [(abs_lt.mp hb).2])
  calc
    ∫⁻ y in chartPreimage x V, ENNReal.ofReal (chartDensity g x y) ≤
        ∫⁻ _y in chartPreimage x V, ENNReal.ofReal C :=
      setLIntegral_mono measurable_const (fun y hy => ENNReal.ofReal_le_ofReal (hden y hy))
    _ = ENNReal.ofReal C * volume (chartPreimage x V) := by simp
    _ ≤ ENNReal.ofReal C * volume (Metric.ball (extChartAt I x x) δ) :=
      mul_le_mul_right (measure_mono hpre) _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Metric.isBounded_ball.measure_lt_top)

theorem exists_volume_locallyFinite (g : Metric (M := M)) :
    ∃ ν : Measure M, IsVolume g ν ∧ IsLocallyFiniteMeasure ν := by
  obtain ⟨ν,hν⟩ := exists_volume g
  exact ⟨ν,hν,volume_locallyFinite g hν⟩

end CKSIntrinsicVolume

end

end OAI
