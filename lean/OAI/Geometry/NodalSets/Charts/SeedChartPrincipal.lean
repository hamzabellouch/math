import OAI.Geometry.NodalSets.Elliptic.Divergence
import OAI.Geometry.NodalSets.Elliptic.IntrinsicSeedPatch

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma seedCoordEquiv_basis (i : Fin 4) :
    seedCoordEquiv (Pi.single i 1) = EuclideanSpace.basisFun (Fin 4) ℝ i := by
  ext j
  simp [seedCoordEquiv, EuclideanSpace.basisFun_apply]

lemma seedCoordEquiv_coordinate_matrix :
    (fun i j : Fin 4 ↦ (seedCoordEquiv (Pi.single j 1)) i) = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  simp [seedCoordEquiv_basis,EuclideanSpace.basisFun_apply,Matrix.one_apply]

lemma seedCoordEquiv_abs_det :
    |Matrix.det (fun i j : Fin 4 ↦ (seedCoordEquiv (Pi.single j 1)) i)| = 1 := by
  rw [seedCoordEquiv_coordinate_matrix,Matrix.det_one,abs_one]

lemma linearMetricPull_inverse_covector
    (g : BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (α : BaseModel →L[ℝ] ℝ) :
    ContinuousLinearMap.inverse (linearMetricPull seedCoordEquiv g)
      (linearCovectorPull seedCoordEquiv α) =
      seedCoordEquiv.symm (ContinuousLinearMap.inverse g α) := by
  let e := positiveMetricEquiv g hp
  have hpp : ∀ v : Coord, v ≠ 0 → 0 < linearMetricPull seedCoordEquiv g v v :=
    linearMetricField_positive seedCoordEquiv (fun _ ↦ g) 0 hp
  let E := positiveMetricEquiv (linearMetricPull seedCoordEquiv g) hpp
  rw [show ContinuousLinearMap.inverse (linearMetricPull seedCoordEquiv g) =
    E.symm.toContinuousLinearMap from ContinuousLinearMap.inverse_equiv E,
    show ContinuousLinearMap.inverse g = e.symm.toContinuousLinearMap from
      ContinuousLinearMap.inverse_equiv e]
  apply E.injective
  change E (E.symm (linearCovectorPull seedCoordEquiv α)) = E (seedCoordEquiv.symm (e.symm α))
  rw [E.apply_symm_apply]
  ext v
  change α (seedCoordEquiv v) = g (seedCoordEquiv (seedCoordEquiv.symm (e.symm α)))
    (seedCoordEquiv v)
  rw [seedCoordEquiv.apply_symm_apply]
  exact (congrArg (fun β : BaseModel →L[ℝ] ℝ ↦ β (seedCoordEquiv v)) (e.apply_symm_apply α)).symm

def seedCoordWeight (rho : Base → ℝ) (x : Coord) : ℝ :=
  rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) *
    roundChartDensity seedPoint (seedCoordEquiv x)

lemma intrinsicSeedCoordMetric_principal (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ∀ x, 0 < rho x) (i j : Fin 4) (x : Coord) :
    sourcePrincipal (intrinsicSeedCoordMetric A rho) i j x =
      (rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)))⁻¹ *
        intrinsicSphereChartTensor A seedPoint (seedCoordEquiv x) i j := by
  rw [← intrinsicSeedCoordMetric_eq A hs hp rho hr]
  let c := intrinsicChartCoefficient A rho seedPoint (seedCoordEquiv x)
  have hc : ∀ α : BaseModel →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α) :=
    intrinsicChartCoefficient_positive A hs hp rho seedPoint
      (by rw [centeredSphereChart_target]; trivial)
  let α : BaseModel →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp seedCoordEquiv.symm.toContinuousLinearMap
  have he : linearCovectorPull seedCoordEquiv α = (ContinuousLinearMap.proj j : Coord →L[ℝ] ℝ) := by
    ext v
    simp [linearCovectorPull_apply,α]
  unfold sourcePrincipal seedCoordMetric linearMetricField
  change (ContinuousLinearMap.inverse (linearMetricPull seedCoordEquiv (coefficientMetricValue c))
    (ContinuousLinearMap.proj j)) i = _
  rw [← he,linearMetricPull_inverse_covector _ (coefficientMetric_positive c hc (hr _)),
    coefficientMetric_inverse c hc (hr _)]
  have hα : baseCovectorCoordinates α = Pi.single j 1 := by
    ext k
    change (seedCoordEquiv.symm (EuclideanSpace.basisFun (Fin 4) ℝ k)) j = _
    rw [← seedCoordEquiv_basis,seedCoordEquiv.symm_apply_apply]
    simp [Pi.single_apply,eq_comm]
  change (seedCoordEquiv.symm (c.2⁻¹ • matrixContravariant
    (intrinsicSphereChartTensor A seedPoint (seedCoordEquiv x)) α)) i = _
  change (WithLp.ofLp (c.2⁻¹ • matrixContravariant
    (intrinsicSphereChartTensor A seedPoint (seedCoordEquiv x)) α)) i = _
  simp [matrixContravariant_coordinates,hα,c,intrinsicChartCoefficient]

end
end Yau.Target

end OAI
