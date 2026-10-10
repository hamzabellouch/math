import OAI.Geometry.SurfaceImmersion.Primitive.ReferenceCircularOperator
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOperatorStability

namespace OAI

/-! Compact positive inverse margins in the actual reference chart frames. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance referenceMarginFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance referenceMarginFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance referenceMarginFiberComplete : CompleteSpace TensorFiber := inferInstance
open PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

def chartCoefficient (i : d.B.centers) (j : Fin 3) (y : JetPolynomial.Base) : TensorFiber →L[ℝ] ℝ :=
  ((d.basis i y).Q j).comp fiberToThree

def chartReference (i : d.B.centers) (y : JetPolynomial.Base) : TensorFiber :=
  fiberFromThree (d.B.tensorChartRead i gref.inner y)

lemma chartCoefficient_smoothOn (i : d.B.centers) (j : Fin 3) :
    ContDiffOn ℝ ∞ (d.chartCoefficient i j) (d.B.chartWeightCompact i : Set JetPolynomial.Base) := by
  rintro y ⟨p,hp,rfl⟩
  exact ((d.basis_smooth i hp j).clm_comp contDiffAt_const).contDiffWithinAt

omit [T2Space M] in
lemma chartReference_smooth (i : d.B.centers) : ContDiff ℝ ∞ (d.chartReference i) :=
  fiberFromThree.contDiff.comp (d.B.tensorChartRead_smooth i gref.contMDiff)

lemma chartCoefficient_positive (i : d.B.centers) (j : Fin 3) {y : JetPolynomial.Base}
    (hy : y ∈ (d.B.chartWeightCompact i : Set JetPolynomial.Base)) :
    0 < d.chartCoefficient i j y (d.chartReference i y) := by
  obtain ⟨p,hp,rfl⟩ := hy
  change 0 < (d.basis i (chart (i : M) p)).Q j
    (fiberToThree (fiberFromThree (d.B.tensorChartRead i gref.inner (chart (i : M) p))))
  rw [fiberToThree_fromThree,d.B.tensorChartRead_on_weight i gref.inner hp]
  exact d.coefficient_positive i hp j

 theorem inverse_margin (i : d.B.centers) (j : Fin 3) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ y ∈ (d.B.chartWeightCompact i : Set JetPolynomial.Base),
      ∀ (T : TensorFiber →L[ℝ] TensorFiber) (H : TensorFiber),
        ‖T-ContinuousLinearMap.id ℝ TensorFiber‖ < eps →
        ‖H-d.chartReference i y‖ < eps →
        T.IsInvertible ∧ 0 < d.chartCoefficient i j y (T.inverse H) := by
  let f := fun y : JetPolynomial.Base =>
    ((ContinuousLinearMap.id ℝ TensorFiber,d.chartCoefficient i j y),d.chartReference i y)
  have hf : ContinuousOn f (d.B.chartWeightCompact i : Set JetPolynomial.Base) :=
    (continuousOn_const.prodMk (d.chartCoefficient_smoothOn i j).continuousOn).prodMk
      (d.chartReference_smooth i).continuous.continuousOn
  have hK := (d.B.chartWeightCompact i).isCompact.image_of_continuousOn hf
  obtain ⟨eps,heps,hmargin⟩ := compact_inverse_coefficient_stability hK
    (by rintro _ ⟨y,hy,rfl⟩; rfl)
    (by rintro _ ⟨y,hy,rfl⟩; exact d.chartCoefficient_positive i j hy)
  refine ⟨eps,heps,?_⟩
  intro y hy T H hT hH
  apply hmargin (f y) ⟨y,hy,rfl⟩ ((T,d.chartCoefficient i j y),H)
  change max (max ‖T-ContinuousLinearMap.id ℝ TensorFiber‖
    ‖d.chartCoefficient i j y-d.chartCoefficient i j y‖) ‖H-d.chartReference i y‖ < eps
  rw [sub_self,norm_zero,max_eq_left (norm_nonneg _)]
  exact max_lt hT hH

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
