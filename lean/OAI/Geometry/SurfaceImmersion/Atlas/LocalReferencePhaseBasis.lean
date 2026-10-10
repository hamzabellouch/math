import OAI.Geometry.SurfaceImmersion.Primitive.CenteredAtlasPrimitives
import OAI.Geometry.Immersion.ClosedSurface.Main

namespace OAI

/-! A positive reference phase basis on a neighborhood of each center,
with its quadratic part fixed by the metric convexity estimate. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem local_reference_phase_basis (g : SmoothMetric M) (p : M)
    (P : PhaseBasis) (hP : ∀ j, 0 < P.Q j (coordinateMetric g p (coordinateCenter p))) (L : ℝ) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ (coordinateChart p).source ∧
      ∀ q ∈ U,
        admissiblePhaseCovectors P (fun j => phaseDerivative
          (centeredConvexPhase (P.ξ j) L (coordinateChart p p)) (coordinateChart p q)) ∧
        ∀ j, 0 < (centeredSpatialBasis P P.ξ L (coordinateChart p p)
          (coordinateChart p q)).Q j (coordinateMetric g p (coordinateChart p q)) := by
  let xi : Base → Fin 3 → Base := fun x j =>
    phaseDerivative (centeredConvexPhase (P.ξ j) L (coordinateCenter p)) x
  have hxi : Continuous xi := by
    apply continuous_pi
    intro j
    simp only [xi,centeredConvexPhase_phaseDerivative]
    fun_prop
  have hself : xi (coordinateCenter p) = P.ξ := by
    funext j
    simp only [xi,centeredConvexPhase_phaseDerivative,sub_self,smul_zero,add_zero]
  have hbase : (xi (coordinateCenter p),coordinateMetric g p (coordinateCenter p)) ∈
      positivePhaseParameters P := by
    rw [hself]
    refine ⟨?_,P.nonzero,?_⟩
    · rw [perturbedPhaseOperator_self]
      exact ⟨ContinuousLinearEquiv.refl ℝ PhaseMean.Tensor,rfl⟩
    · intro j
      simpa only [perturbedPhaseCoefficient_self] using hP j
  have hn := (hxi.continuousAt.prodMk (coordinateMetric_continuousAt_center g p)).eventually
    ((positivePhaseParameters_open P).mem_nhds hbase)
  obtain ⟨W,hWsub,hW,hcW⟩ := mem_nhds_iff.mp hn
  let U : Set M := (coordinateChart p).source ∩ (coordinateChart p) ⁻¹' W
  have hc : coordinateChart p p = coordinateCenter p := by
    simp [coordinateChart_apply,chartCoordinates,coordinateCenter,planeModel]
  refine ⟨U,(coordinateChart p).isOpen_inter_preimage hW,⟨?_,?_⟩,fun q hq => hq.1,?_⟩
  · rw [coordinateChart_source]; exact mem_chart_source Plane p
  · change coordinateChart p p ∈ W
    rwa [hc]
  · intro q hq
    have hm := hWsub hq.2
    change (xi (coordinateChart p q),coordinateMetric g p (coordinateChart p q)) ∈
      positivePhaseParameters P at hm
    have ha : admissiblePhaseCovectors P (xi (coordinateChart p q)) := ⟨hm.1,hm.2.1⟩
    rw [hc]
    refine ⟨ha,?_⟩
    intro j
    change 0 < (resolvedPhaseBasis P (xi (coordinateChart p q))).Q j _
    rw [resolvedPhaseBasis_coefficients P ha]
    exact hm.2.2 j

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
