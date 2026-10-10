import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.LocallyConstant.Basic

namespace OAI

/-! A local pairwise almost-everywhere constancy criterion on a compact
connected space with a measure of full support. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

section Abstract

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem ae_constant_on_of_ae_pairwise (f : X → ℝ) {U : Set X}
    (hU : μ U ≠ 0)
    (hpair : ∀ᵐ p ∂(μ.restrict U).prod (μ.restrict U), f p.1 = f p.2) :
    ∃ c : ℝ, f =ᵐ[μ.restrict U] fun _ => c := by
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hU
    (Measure.ae_ae_of_ae_prod hpair)
  refine ⟨f x, ?_⟩
  filter_upwards [hx] with y hy
  exact hy.symm

variable [μ.IsOpenPosMeasure]

omit [OpensMeasurableSpace X] [IsFiniteMeasure μ] in
theorem ae_constants_eq_of_open_overlap (f : X → ℝ) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hne : (U ∩ V).Nonempty)
    {c d : ℝ} (hc : f =ᵐ[μ.restrict U] fun _ => c)
    (hd : f =ᵐ[μ.restrict V] fun _ => d) : c = d := by
  have hc' : f =ᵐ[μ.restrict (U ∩ V)] fun _ => c :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hc
  have hd' : f =ᵐ[μ.restrict (U ∩ V)] fun _ => d :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hd
  obtain ⟨x, _, hxc, hxd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((hU.inter hV).measure_ne_zero μ hne) (hc'.and hd')
  exact hxc.symm.trans hxd

variable [CompactSpace X] [PreconnectedSpace X]

/-- Pairwise a.e. equality on a neighborhood of every point forces one
global a.e. constant on a connected compact full-support measure space. -/
theorem ae_constant_of_local_ae_pairwise (f : X → ℝ)
    (hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᵐ p ∂(μ.restrict U).prod (μ.restrict U), f p.1 = f p.2) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  choose U hU hx hpair using hlocal
  have hconst (x : X) : ∃ c : ℝ, f =ᵐ[μ.restrict (U x)] fun _ => c :=
    ae_constant_on_of_ae_pairwise f ((hU x).measure_ne_zero μ ⟨x, hx x⟩) (hpair x)
  choose c hc using hconst
  have hloc : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_exists_open c).mpr
    intro x
    refine ⟨U x, hU x, hx x, fun y hy => ?_⟩
    exact ae_constants_eq_of_open_overlap f (hU y) (hU x)
      ⟨y, hx y, hy⟩ (hc y) (hc x)
  obtain ⟨k, hk⟩ := hloc.exists_eq_const
  refine ⟨k, ?_⟩
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have heach (x : X) : ∀ᵐ y ∂μ, y ∈ U x → f y = k := by
    apply (ae_restrict_iff' (hU x).measurableSet).mp
    have hck : c x = k := congrFun hk x
    simpa only [hck, Filter.EventuallyEq] using hc x
  have hfin : ∀ᵐ y ∂μ, ∀ x : s, y ∈ U x → f y = k :=
    ae_all_iff.mpr (fun x => heach x)
  filter_upwards [hfin] with y hy
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact hy ⟨x, hxs⟩ hyx

end Abstract

section Actual

open EinsteinFour

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actual_scalar_ae_constant_of_local_ae_pairwise (g : SmoothMetric M)
    (f : M → ℝ)
    (hlocal : ∀ x, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ᵐ p ∂((normalizedVolume g).restrict U).prod ((normalizedVolume g).restrict U),
        f p.1 = f p.2) :
    ∃ c : ℝ, f =ᵐ[normalizedVolume g] fun _ => c := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let := normalizedVolume_isOpenPosMeasure g
  exact ae_constant_of_local_ae_pairwise f hlocal

end Actual

end
end PositiveEinsteinFour.Geometry

end OAI
