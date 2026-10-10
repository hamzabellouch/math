import OAI.Geometry.SurfaceImmersion.Atlas.VectorChartRead

namespace OAI

/-! Coordinate readings retain the support of the global input. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

lemma tsupport_comp_preimage {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero V]
    (f : X → V) (g : Y → X) (hg : Continuous g) : tsupport (f ∘ g) ⊆ g ⁻¹' tsupport f := by
  apply closure_minimal _ ((isClosed_tsupport f).preimage hg)
  intro y hy
  exact subset_tsupport f hy

variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorPlaneRead_support_on_weight (k : A.centers) (F : M → V)
    {x : SmallModes.Base} (hx : x ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base))
    (hF : x ∈ tsupport (A.vectorPlaneRead k F)) :
    (chart (k : M)).symm (planeCoordinateIsometry.symm x) ∈ tsupport F := by
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hx
  have hr := tsupport_comp_preimage (A.vectorChartRead k F) planeCoordinateIsometry.symm
    planeCoordinateIsometry.symm.continuous hF
  change planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (k : M) p)) ∈
    tsupport (localize (k : M) (A.outer k) F) at hr
  rw [LinearIsometryEquiv.symm_apply_apply] at hr
  obtain ⟨q,⟨hq,hqF⟩,he⟩ := localize_tsupport_inter (k : M) (A.outer_support k) F hr
  have hqp : q = p := (chart (k : M)).injOn (A.outer_support k hq) (A.weight_support k hp) he
  subst q
  simpa only [LinearIsometryEquiv.symm_apply_apply,(chart (k : M)).left_inv (A.weight_support k hp)]
    using hqF

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
