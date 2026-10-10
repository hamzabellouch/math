import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorLocalBounds
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledNonlinearBounds

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

local instance atlasRemainderFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasRemainderFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasRemainderDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasRemainderDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasRemainderSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasRemainderSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)



/-- The cubic Taylor remainder of the actual global polynomial metric. -/
theorem atlas_polynomial_remainder_bound {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (m : ℕ) (B C : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i) (hC : ∀ i, 0 < C i) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (F X : M → Space),
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ X →
      ∀ τ ε δ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → MapsTo
        (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x)) (U i) (Q i)) →
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → WeightedEstimates.WeightedBound (U i) τ
        (m+tensorOrder (P i)) (B i)
        (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x))) →
      (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i))
        (C i*δ*τ) (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) →
      A.TensorWeightedBound τ m (E*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F X) := by
  classical
  choose E hE he using fun i : A.centers => scaled_coordinate_taylor_bound (hU i) (hQ i)
    (P i) (hP i) m (B i) (hB i)
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound_on_outer U hU houter m
  let S := ∑ i : A.centers, E i*(C i)^3
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hE i) (pow_nonneg (hC i).le _))
  refine ⟨D*S,mul_nonneg hD hS,?_⟩
  intro F X hF hX τ ε δ hτ hτ1 hε hε1 hδ hsmall hseg hsegb hXb
  have hlocal (i : A.centers) := he i (A.jetChartMap i F)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) τ ε δ (C i)
    hτ hτ1 hε hε1 hδ (hC i) (hsmall i) (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
  have hbound (i : A.centers) : WeightedEstimates.WeightedBound
      (planeCoordinateIsometry.symm ⁻¹' U i) τ m (S*(δ^3/τ))
      (coordinateTaylorRemainder (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) := by
    have hb := hlocal i
      (by simpa only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using hseg i)
      (by simpa only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using hsegb i)
      (hXb i)
    exact hb.mono_const (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => mul_nonneg (hE j) (pow_nonneg (hC j).le _))
        (Finset.mem_univ i)) (div_nonneg (pow_nonneg hδ.le _) hτ.le))
  have hsmooth (i : A.centers) : ContDiff ℝ ∞
      (coordinateTaylorRemainder (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) := by
    exact (tensorTaylorRemainder_smooth (hP i) (A.jetChartMap_smooth i hF)
      (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).comp
        planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff
  have hh := hd _ hsmooth τ (S*(δ^3/τ)) hτ hτ1
    (mul_nonneg hS (div_nonneg (pow_nonneg hδ.le _) hτ.le)) hbound
  simpa only [atlasPolynomialRemainder,mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
