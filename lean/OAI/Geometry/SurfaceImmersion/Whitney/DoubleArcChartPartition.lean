import OAI.Geometry.SurfaceImmersion.Whitney.OrientedDoubleChartArc
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusSmoothStructure
import Mathlib.Topology.UnitInterval

namespace OAI

/-! A compact embedded arc in the actual transverse double locus has a
finite ordered subdivision into the smooth regular chart arcs constructed above. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem double_arc_chart_partition
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {γ : ℝ → surfaceDoublePairs f} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ), τ 0 = a ∧ Monotone τ ∧
      (∀ n, a ≤ τ n ∧ τ n ≤ b) ∧ (∀ n ≥ N, τ n = b) ∧
      ∀ n, ∃ c : SmoothDoubleChart f,
        MapsTo γ (Icc (τ n) (τ (n+1))) c.coord.source := by
  let C : surfaceDoublePairs f → Set (Icc a b) := fun p =>
    (fun t : Icc a b => γ t) ⁻¹' (transverseDoubleChart hf hreg p).coord.source
  have hC : ∀ p, IsOpen (C p) := fun p =>
    (transverseDoubleChart hf hreg p).coord.open_source.preimage hγ.domRestrict
  have hcover : univ ⊆ ⋃ p, C p := by
    intro t _
    refine mem_iUnion.mpr ⟨γ t,?_⟩
    exact transverseDoubleChart_mem hf hreg (γ t)
  obtain ⟨τ,hzero,hmono,⟨N,hend⟩,hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hC hcover
  refine ⟨fun n => (τ n).val,N,hzero,fun _ _ h => hmono h,
    fun n => (τ n).property,hend,?_⟩
  intro n
  obtain ⟨p,hp⟩ := hsub n
  refine ⟨transverseDoubleChart hf hreg p,?_⟩
  intro r hr
  have hrab : r ∈ Icc a b := ⟨(τ n).property.1.trans hr.1,hr.2.trans (τ (n+1)).property.2⟩
  exact hp (show (⟨r,hrab⟩ : Icc a b) ∈ Icc (τ n) (τ (n+1)) from hr)

theorem finite_smooth_double_arc_pieces
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {γ : ℝ → surfaceDoublePairs f} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ), τ 0 = a ∧ Monotone τ ∧
      (∀ n, a ≤ τ n ∧ τ n ≤ b) ∧ (∀ n ≥ N, τ n = b) ∧
      ∀ n, τ n < τ (n+1) →
        ∃ P : SmoothCompactArc (planeModel.prod planeModel) (M × M),
          P.curve '' Icc P.start P.finish =
            (fun t => (γ t).val) '' Icc (τ n) (τ (n+1)) ∧
          P.curve P.start = (γ (τ n)).val ∧
          P.curve P.finish = (γ (τ (n+1))).val := by
  obtain ⟨τ,N,hzero,hmono,hbounds,hend,hcharts⟩ :=
    double_arc_chart_partition hf hreg hab.le hγ
  refine ⟨τ,N,hzero,hmono,hbounds,hend,?_⟩
  intro n hn
  obtain ⟨c,hc⟩ := hcharts n
  have hsub : Icc (τ n) (τ (n+1)) ⊆ Icc a b := Icc_subset_Icc (hbounds n).1 (hbounds (n+1)).2
  obtain ⟨P,s,hs,hP,hstart,hfinish,himage,hleft,hright⟩ :=
    c.oriented_arc hn (hγ.mono hsub) (hinj.mono hsub) hc
  exact ⟨P,himage,hleft,hright⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
