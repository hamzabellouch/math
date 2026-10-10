import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialMetric
import OAI.Geometry.SurfaceImmersion.Correction.SurfaceMeanTensor

namespace OAI

/-! Embed the three mean-polynomial coefficients of one primitive in the
actual global atlas operator, with zero contribution from every other chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetPolynomial.Perturbation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma meanTensorPolynomial_global_extension {Q : Set LowJet} (hQ : IsCompact Q)
    (hQO : Q ⊆ O) (n : ℕ) :
    ∃ P : Fin 3 → Fin n → Expression,
      (∀ k r, (P k r).SmoothCoeffs univ) ∧
      (∀ k r, (P k r).order = (l.meanTensorPolynomial n k r).order) ∧
      (∀ k r, (P k r).loss = (l.meanTensorPolynomial n k r).loss) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space), ContDiff ℝ ∞ G →
        ∀ (z : ℝ) (p : JetPolynomial.Base), lowJet G p ∈ Q →
        coordinateMetricMap P z G (planeCoordinateIsometry p) =
          l.meanTensorOperator n z G (planeCoordinateIsometry p) := by
  classical
  choose P hs ho hl he using fun k r => Expression.exists_global_extension O.isOpen
    (l.meanTensorPolynomial_smooth n k r) hQ hQO
  refine ⟨P,hs,ho,hl,?_⟩
  intro G hG z p hp
  rw [← l.coordinateMetricMap_eq_meanTensorOperator hG]
  have hpoly : coordinatePolynomialValue P z G 0 (planeCoordinateIsometry p) =
      coordinatePolynomialValue (l.meanTensorPolynomial n) z G 0 (planeCoordinateIsometry p) := by
    funext k
    unfold coordinatePolynomialValue
    apply Finset.sum_congr rfl
    intro r _
    rw [he k r G (planeCoordinateIsometry.symm (planeCoordinateIsometry p),0)
      (by simpa only [planeCoordinateIsometry.symm_apply_apply] using hp)]
  change RealModes.realMetricTensor (G ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p)+
    coordinatePolynomialValue P z G 0 (planeCoordinateIsometry p) = _
  rw [hpoly]
  rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
local instance primitivePolyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitivePolyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance primitivePolyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitivePolyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitivePolySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitivePolySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- A single primitive's mean polynomial in the fixed atlas. -/
def primitiveAtlasPolynomial {n : ℕ} (i : A.centers) (P : Fin 3 → Fin n → Expression)
    (j : A.centers) : Fin 3 → Fin n → Expression := by
  classical
  exact if j = i then P else fun _ _ => Expression.coeff (fun _ => 0)

omit [CompactSpace M] in
lemma primitiveAtlasPolynomial_smooth {n : ℕ} (i : A.centers)
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ) :
    ∀ j k r, (A.primitiveAtlasPolynomial i P j k r).SmoothCoeffs univ := by
  classical
  intro j k r
  by_cases hji : j = i
  · simpa only [primitiveAtlasPolynomial,ite_eq_left hji] using hP k r
  · simp only [primitiveAtlasPolynomial,ite_eq_right hji,Expression.SmoothCoeffs]
    exact contDiffOn_const

omit [CompactSpace M] in
lemma atlasPolynomialValue_primitive {n : ℕ} (i : A.centers)
    (P : Fin 3 → Fin n → Expression) (z : ℝ) (G : M → Space) :
    A.atlasPolynomialValue (A.primitiveAtlasPolynomial i P) z G =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (coordinatePolynomialValue P z (A.jetChartMap i G) 0 (planeCoordinateIsometry y))) := by
  classical
  funext p
  unfold atlasPolynomialValue tensorPlaneRestore
  rw [Finset.sum_eq_single i]
  · simp [primitiveAtlasPolynomial]
  · intro j _ hji
    have hz : coordinatePolynomialValue (A.primitiveAtlasPolynomial i P j) z (A.jetChartMap j G) 0 = 0 := by
      funext x k
      simp only [primitiveAtlasPolynomial,ite_eq_right hji,coordinatePolynomialValue,Expression.eval,
        mul_zero,Finset.sum_const_zero,Pi.zero_apply]
    simp only [hz,Pi.zero_apply,map_zero,bundleRestore,smul_zero]
  · exact fun hi => False.elim (hi (Finset.mem_univ _))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
