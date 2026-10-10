import OAI.Geometry.SurfaceImmersion.Primitive.CircularPrimitiveFamily

namespace OAI

/-! Ordered finite primitive realization. The metric convexity is required
only at the actual prefix metrics, preserving the order of the cycles. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

def ConvexMetric (d : CircularPrimitiveFamily B ι) (g : SmoothMetric M) (a : ι) : Prop :=
  ∀ p ∈ tsupport (B.weight (d.curves a).index),
    ‖coordinateChart ((d.curves a).index : M) p-coordinateChart ((d.curves a).index : M) (d.curves a).index‖ ≤ d.chartRadius a →
    ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g ((d.curves a).index : M))
      (centeredConvexPhase (d.linearPart a) (d.convexPart a)
        (coordinateChart ((d.curves a).index : M) (d.curves a).index))
      (coordinateChart ((d.curves a).index : M) p) v v

 theorem realize_sequence (N : ℕ) :
    ∀ (d : CircularPrimitiveFamily B (Fin N)) (g : Fin (N+1) → SmoothMetric M),
    (∀ a : Fin N, (g a.succ).inner = (g a.castSucc).inner +
      (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) →
    (∀ a : Fin N, d.ConvexMetric (g a.castSucc) a) →
    ∀ (F : M → Space) (n : PreferredNormal F),
    IsSmoothIsometricImmersion M (g 0) F → MetricGoodPhaseData (g 0) F →
    FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
    ∃ W : M → Space, IsSmoothIsometricImmersion M (g (Fin.last N)) W ∧
      Nonempty (MetricGoodPhaseData (g (Fin.last N)) W) ∧ Nonempty (PreferredNormal W) := by
  classical
  induction N with
  | zero =>
    intro d g _ _ F n hF data _
    exact ⟨F,hF,⟨data⟩,⟨n⟩⟩
  | succ N ih =>
    intro d g hstep hconvex F n hF data hgeom
    obtain ⟨W,hW,⟨good⟩,normal,hnew⟩ := d.one_step 0 hF n hgeom (hconvex 0) data
      (g (Fin.succ 0)) (hstep 0)
    let d' := d.restrict (Fin.succ : Fin N → Fin (N+1)) (Fin.succ_injective N)
    let g' : Fin (N+1) → SmoothMetric M := fun a => g a.succ
    have hstep' (a : Fin N) : (g' a.succ).inner = (g' a.castSucc).inner +
        (fun p => (d'.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d'.phase a) p) := by
      simpa only [g',d',restrict,Function.comp_apply,ConvexMetric,Fin.succ_castSucc] using hstep a.succ
    have hconvex' (a : Fin N) : d'.ConvexMetric (g' a.castSucc) a := by
      simpa only [g',d',restrict,Function.comp_apply,ConvexMetric,Fin.succ_castSucc] using hconvex a.succ
    let f : Fin N → {j : Fin (N+1) // j ≠ 0} := fun a => ⟨a.succ,Fin.succ_ne_zero a⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Fin.succ_injective N (congrArg Subtype.val hab)
    have hsub : boundaryCrossingSet d'.curves univ ⊆
        boundaryCrossingSet (fun j : {j : Fin (N+1) // j ≠ 0} => d.curves j) univ := by
      rintro p ⟨a,_,b,_,hab,ha,hb⟩
      exact ⟨f a,mem_univ _,f b,mem_univ _,fun h => hab (hf h),ha,hb⟩
    have hgeom' : FiniteBoundaryGeometry d'.curves (boundaryCrossingSet d'.curves univ) W normal :=
      hnew.restrict f hf hsub
    obtain ⟨V,hV,hgood,hN⟩ := ih d' g' hstep' hconvex' W normal hW good hgeom'
    exact ⟨V,hV,hgood,hN⟩

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
