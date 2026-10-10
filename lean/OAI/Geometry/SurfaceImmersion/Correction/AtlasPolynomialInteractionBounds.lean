import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorLocalBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialInteractionBounds

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance atlasInteractionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasInteractionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasInteractionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasInteractionDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasInteractionSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasInteractionSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)




lemma atlasPolynomialQuadratic_difference {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    (F X Y : M → Space) (hX : ContMDiff planeModel spaceModel ∞ X)
    (hY : ContMDiff planeModel spaceModel ∞ Y) :
    A.atlasPolynomialQuadratic P ε F (X+Y)-A.atlasPolynomialQuadratic P ε F X =
      A.tensorPlaneRestore (fun i => coordinatePolynomialInteraction (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm)) := by
  unfold atlasPolynomialQuadratic
  rw [← A.tensorPlaneRestore_sub]
  congr 1
  funext i
  have he : A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm =
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)+
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
    rw [A.jetChartMap_add]
    rfl
  simp only [Pi.sub_apply,he,coordinate_quadratic_add (P i) ε (A.jetChartMap i F)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff),add_sub_cancel_left]

/-- The mixed polynomial error is cubic in the correction amplitude after
using the fixed loss condition. -/
theorem atlas_polynomial_interaction_bound {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (m : ℕ) (B C D : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i)
    (hC : ∀ i, 0 < C i) (hD : ∀ i, 0 < D i) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (F X Y : M → Space),
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ X →
      ContMDiff planeModel spaceModel ∞ Y →
      ∀ τ ε δ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ i, MapsTo (lowJet (A.jetChartMap i F)) (U i) (Q i)) →
      (∀ i, WeightedEstimates.WeightedBound (U i) τ (m+tensorOrder (P i)) (B i)
        (lowJet (A.jetChartMap i F))) →
      (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i)+1)
        (C i*δ*τ) (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) →
      (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i)+1)
        (D i*δ^2) (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm)) →
      A.TensorWeightedBound τ m (E*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε F (X+Y)-A.atlasPolynomialQuadratic P ε F X) := by
  classical
  choose E hE he using fun i : A.centers => scaled_polynomial_interaction_bound (hU i) (hQ i)
    (P i) (hP i) m (B i) (hB i)
  obtain ⟨D₀,hD₀,hd⟩ := A.tensorPlaneRestore_bound_on_outer U hU houter m
  let S := ∑ i : A.centers, E i*(C i*D i+(D i)^2)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hE i)
    (add_nonneg (mul_nonneg (hC i).le (hD i).le) (sq_nonneg _)))
  refine ⟨D₀*S,mul_nonneg hD₀ hS,?_⟩
  intro F X Y hF hX hY τ ε δ hτ hτ1 hε hε1 hδ hδτ hsmall hGQ hGb hXb hYb
  have hlocal (i : A.centers) := he i (A.jetChartMap i F)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)
    (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) τ ε δ (C i) (D i)
    hτ hτ1 hε hε1 hδ hδτ (hC i) (hD i) (hsmall i) (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff)
    (hGQ i) (hGb i) (hXb i) (hYb i)
  have hb (i : A.centers) : WeightedEstimates.WeightedBound
      (planeCoordinateIsometry.symm ⁻¹' U i) τ m (S*(δ^3/τ))
      (coordinatePolynomialInteraction (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm)) :=
    (hlocal i).mono_const (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => mul_nonneg (hE j)
        (add_nonneg (mul_nonneg (hC j).le (hD j).le) (sq_nonneg _))) (Finset.mem_univ i))
      (div_nonneg (pow_nonneg hδ.le _) hτ.le))
  have hh := hd _ (fun i => coordinatePolynomialInteraction_smooth (hP i)
    (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff) ε)
    τ (S*(δ^3/τ)) hτ hτ1 (mul_nonneg hS (div_nonneg (pow_nonneg hδ.le _) hτ.le)) hb
  rw [A.atlasPolynomialQuadratic_difference P ε F X Y hX hY]
  simpa only [mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
