import OAI.Geometry.SurfaceImmersion.Whitney.ArcTimeChartPartition
import OAI.Geometry.SurfaceImmersion.Atlas.TimeCoordinateTransition

namespace OAI

/-! Reversing only the transverse coordinate keeps the global arc time
and all axis points unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def transverseReflection : Base ≃L[ℝ] Base :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => ![-x 0,x 1]
    invFun := fun x => ![-x 0,x 1]
    left_inv := by intro x; ext i; fin_cases i <;> simp
    right_inv := by intro x; ext i; fin_cases i <;> simp
    map_add' := by intro x y; ext i; fin_cases i <;> simp [add_comm]
    map_smul' := by intro a x; ext i; fin_cases i <;> simp
  }

lemma transverseReflection_apply (x : Base) : transverseReflection x = ![-x 0,x 1] := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] {F : M → ℝ}
namespace SurfaceTimeChart

def reflect (c : SurfaceTimeChart F) : SurfaceTimeChart F where
  coord := c.coord.transHomeomorph transverseReflection.toHomeomorph
  smooth := transverseReflection.contDiff.contMDiff.comp_contMDiffOn c.smooth
  inverse_smooth := c.inverse_smooth.comp transverseReflection.symm.contDiff.contMDiff.contMDiffOn
    (fun _ hx => hx)
  time := by
    intro x hx
    change (transverseReflection (c.coord x)) 1 = F x
    exact c.time x hx

omit [IsManifold planeModel ∞ M] in
lemma reflect_axis (c : SurfaceTimeChart F) {x : M} {t : ℝ}
    (hx : c.coord x = ![0,t]) : c.reflect.coord x = ![0,t] := by
  change transverseReflection (c.coord x) = ![0,t]
  rw [hx,transverseReflection_apply]
  simp

omit [IsManifold planeModel ∞ M] in
lemma reflect_transition (c d : SurfaceTimeChart F) (x : M)
    (h : DifferentiableAt ℝ (d.coord ∘ c.coord.symm) (c.coord x)) :
    fderiv ℝ (d.reflect.coord ∘ c.coord.symm) (c.coord x) =
      transverseReflection.toContinuousLinearMap.comp
        (fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x)) := by
  change fderiv ℝ (transverseReflection ∘ (d.coord ∘ c.coord.symm)) (c.coord x) = _
  exact (transverseReflection.hasFDerivAt.comp (c.coord x) h.hasFDerivAt).fderiv

end SurfaceTimeChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
