import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Atlas Localization. -/

section

 

noncomputable section
open Set Filter Topology Manifold IsManifold
open scoped ContDiff

namespace Anticanonical.ComplexAtlas
variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

 
@[instance_reducible] def chartedSpace : ChartedSpace (Coordinates d) X where
  atlas := Set.range A.chart
  chartAt x := A.chart (A.covers x).choose
  mem_chart_source x := (A.covers x).choose_spec
  chart_mem_atlas point := ⟨(A.covers point).choose, rfl⟩

lemma real_smooth_transition (i j : Fin A.count) :
    ContDiffOn ℝ ∞ (A.transition i j) (coordinateOverlap (A.chart i) (A.chart j)) := by
  intro z hz
  exact ((ProjectiveKaehler.analyticOnNhd_pi_of_differentiableOn
    (A.isOpen_coordinateOverlap i j) (A.holomorphic i j) z hz).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

 
theorem isManifold : letI := A.chartedSpace; IsManifold 𝓘(ℝ, Coordinates d) ∞ X := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    transition, coordinateOverlap] using
      A.real_smooth_transition i j

 

theorem contMDiff_iff (f : X → ℝ) : letI := A.chartedSpace;
    ContMDiff 𝓘(ℝ, Coordinates d) 𝓘(ℝ) ∞ f ↔
      ∀ i, ContDiffOn ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i).target := by
  let := A.chartedSpace
  let := A.isManifold
  constructor
  · intro hf i
    have he : A.chart i ∈ maximalAtlas 𝓘(ℝ, Coordinates d) ∞ X :=
      (contDiffGroupoid ∞ 𝓘(ℝ, Coordinates d)).subset_maximalAtlas ⟨i, rfl⟩
    exact (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  · intro hf x
    rw [contMDiffAt_iff_source]
    have hchart : chartAt (Coordinates d) x = A.chart (A.covers x).choose := rfl
    have hx := (A.chart (A.covers x).choose).mapsTo (A.covers x).choose_spec
    have hh := ((hf (A.covers x).choose).contDiffAt
      ((A.chart (A.covers x).choose).open_target.mem_nhds hx)).contMDiffAt
    simpa only [extChartAt_coe_symm, extChartAt_coe, hchart, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      Set.range_id, contMDiffWithinAt_univ, chartAt, chartedSpace] using hh

 

theorem exists_smooth_partition [T2Space X] [CompactSpace X] :
    ∃ ρ : Fin A.count → SourceSmooth.SmoothRealFunction A,
      (∀ i x, 0 ≤ (ρ i).value x) ∧
      (∀ x, ∑ i, (ρ i).value x = 1) ∧
      (∀ i, tsupport (ρ i).value ⊆ (A.chart i).source) := by
  let := A.chartedSpace
  let := A.isManifold
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Coordinates d) (s := (Set.univ : Set X)) isClosed_univ
    (fun i => (A.chart i).source) (fun i => (A.chart i).open_source)
    (by intro x _; obtain ⟨i, hi⟩ := A.covers x; exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨fun i => ⟨ρ i, (A.contMDiff_iff (ρ i)).mp (ρ i).contMDiff⟩, ?_, ?_, ?_⟩
  · exact fun i x => ρ.nonneg i x
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
  · exact hρ

end Anticanonical.ComplexAtlas

end
end

end OAI
