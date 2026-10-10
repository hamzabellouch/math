import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialValueBounds

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

local instance tensorLocalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorLocalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorLocalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance tensorLocalDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance tensorLocalSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorLocalSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


/-- Compact coordinate bounds on the outer supports suffice for global restoration. -/
theorem tensorPlaneRestore_bound_on_outer
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor),
      (∀ i, ContDiff ℝ ∞ (f i)) → ∀ (s C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
      (∀ i, WeightedEstimates.WeightedBound (planeCoordinateIsometry.symm ⁻¹' U i) s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  classical
  choose K χ hχU hχone using fun i => A.polynomial_outer_cutoff i (hU i) (houter i)
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let N : A.centers → ℝ := fun i => supportedWeightedSeminorm (K i) 1 m (χ i)
  have hN (i) : 0 ≤ N i := apply_nonneg _ _
  let E : A.centers → ℝ := fun i => 2^m * N i
  have hE (i) : 0 ≤ E i := mul_nonneg (by positivity) (hN i)
  let E₀ := ∑ i : A.centers, E i
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg (fun i _ => hE i)
  refine ⟨D*E₀,mul_nonneg hD hE₀,?_⟩
  intro f hf s C hs hs1 hC hb
  let ψ : A.centers → SmallModes.Base → ℝ := fun i => (χ i) ∘ planeCoordinateIsometry.symm
  let g : A.centers → SmallModes.Base → Tensor := fun i x => ψ i x • f i x
  have hψ (i) : ContDiff ℝ ∞ (ψ i) := (χ i).contDiff.comp planeCoordinateIsometry.symm.contDiff
  have hg (i) : ContDiff ℝ ∞ (g i) := (hψ i).smul (hf i)
  have hψsp (i) : tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' U i := by
    apply (show tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' tsupport (χ i) from ?_).trans
      (preimage_mono (hχU i))
    apply closure_minimal _ ((isClosed_tsupport (χ i)).preimage planeCoordinateIsometry.symm.continuous)
    intro x hx
    exact subset_tsupport (χ i) hx
  have hψb (i) : WeightedEstimates.WeightedBound univ s m (N i) (ψ i) :=
    weightedBound_comp_isometry planeCoordinateIsometry.symm (χ i).contDiff
      ((weightedBound_of_supportedSeminorm (1 : ℝ≥0) m (χ i)).shrink_scale hs.le hs1)
  have hgb (i) : WeightedEstimates.WeightedBound univ s m (E i*C) (g i) := by
    let V := planeCoordinateIsometry.symm ⁻¹' U i
    have hV : IsOpen V := (hU i).preimage planeCoordinateIsometry.symm.continuous
    have hprod := ((hψb i).restrict_open hV).smul_real hV.uniqueDiffOn hs.le (hN i) hC
      (hψ i).contDiffOn (hf i).contDiffOn (hb i)
    exact hprod.extend_support hV
      ((tsupport_smul_subset_left (ψ i) (f i)).trans (hψsp i)) (mul_nonneg (hE i) hC)
  have hglobal (i) : WeightedEstimates.WeightedBound univ s m (E₀*C) (g i) := by
    apply (hgb i).mono_const
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)) hC
  have hout := hd g s (E₀*C) hs hs1 (mul_nonneg hE₀ hC) hg hglobal
  have heq : A.tensorPlaneRestore g = A.tensorPlaneRestore f := by
    funext p
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p ∈ tsupport (A.outer i)
    · have hχp := hχone i p hp
      change A.outer i p • (A.tensorTriv i).symmL ℝ p
        (fiberFromThree ((χ i) (planeCoordinateIsometry.symm
          (planeCoordinateIsometry (chart (i : M) p))) • f i
            (planeCoordinateIsometry (chart (i : M) p)))) = _
      simp only [planeCoordinateIsometry.symm_apply_apply,hχp,one_smul]
      rfl
    · have hz : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp only [bundleRestore,hz,zero_smul]
  rw [heq] at hout
  simpa only [mul_assoc] using hout

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
