import OAI.Geometry.IsometricImmersion.Metrics.PatchTensorRestriction

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem patchAddress_inverse_mulVec_injective (a : PatchAddress) :
    Injective ((patchAddressMatrix a)⁻¹).mulVec := by
  intro v w hvw
  have h := congrArg (fun u : Coord => patchAddressMatrix a *ᵥ u) hvw
  have hR := Matrix.mul_nonsing_inv (patchAddressMatrix a)
    ((Matrix.isUnit_iff_isUnit_det _).mp (patchAddressMatrix_isUnit a))
  simpa only [Matrix.mulVec_mulVec,hR,Matrix.one_mulVec] using h

theorem patchAddress_local_inverse_congruence (g : MetricField)
    (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) (p : Coord) :
    (patchAddressMatrix a)⁻¹ᵀ *
      localPatchMetric g eta a (affineInverseCoordinates (patchAddressCenter a) (patchAddressMatrix a) p) *
        (patchAddressMatrix a)⁻¹ = (g + patchAddressTensor eta a) p := by
  have h := congrFun (affinePushforward_pullback g (patchAddressCenter a)
    (patchAddressMatrix a) (patchAddressMatrix_isUnit a)) p
  change (patchAddressMatrix a)⁻¹ᵀ *
      affinePullbackMetric g (patchAddressCenter a) (patchAddressMatrix a)
        (affineInverseCoordinates (patchAddressCenter a) (patchAddressMatrix a) p) *
          (patchAddressMatrix a)⁻¹ = g p at h
  simp only [localPatchMetric,Pi.add_apply,Matrix.mul_add,Matrix.add_mul,h]
  rfl

theorem patchAddress_add_posDef_of_local_metric
    {g : MetricField} {U : Set Coord} (hg : ∀ p ∈ U, (g p).PosDef)
    (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress)
    (hlocal : ∀ q ∈ modelSquare, (localPatchMetric g eta a q).PosDef)
    {p : Coord} (hp : p ∈ U) : ((g + patchAddressTensor eta a) p).PosDef := by
  let q := affineInverseCoordinates (patchAddressCenter a) (patchAddressMatrix a) p
  by_cases hq : q ∈ patchBox
  · have hpos := (hlocal q (patchBox_subset_modelSquare hq)).conjTranspose_mul_mul_same
      (patchAddress_inverse_mulVec_injective a)
    simpa only [q, Matrix.conjTranspose_eq_transpose_of_trivial,
      patchAddress_local_inverse_congruence] using hpos
  · have hz : perturbationTensor (eta a) q = 0 := perturbationTensor_zero_off_patch (eta a) hq
    have hpzero : patchAddressTensor eta a p = 0 := by
      change (patchAddressMatrix a)⁻¹ᵀ * perturbationTensor (eta a) q * (patchAddressMatrix a)⁻¹ = 0
      rw [hz,Matrix.mul_zero,Matrix.zero_mul]
    change (g p + patchAddressTensor eta a p).PosDef
    rw [hpzero,add_zero]
    exact hg p hp

theorem assembledPatchMetric_smoothPositive_of_local_metrics {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ q ∈ modelSquare, (localPatchMetric g eta a q).PosDef) :
    SmoothPositiveOn (assembledPatchMetric g eta) U :=
  assembledPatchMetric_smoothPositive he hg eta hsmall
    (fun a _ hp => patchAddress_add_posDef_of_local_metric hg.2 eta a (hlocal a) hp.1)

theorem assembledPatchMetric_curvature_on_disk_of_local_metrics {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ q ∈ modelSquare, (localPatchMetric g eta a q).PosDef)
    (n : ℕ) {p : Coord} (hp : p ∈ accumulatingDisk n) (hpU : p ∈ U) :
    gaussianCurvature (assembledPatchMetric g eta) p = gaussianCurvature g p :=
  assembledPatchMetric_curvature_on_disk he hg hU eta hsmall
    (fun a _ hp => patchAddress_add_posDef_of_local_metric hg.2 eta a (hlocal a) hp.1) n hp hpU

end SmoothLocal.Geometry

end

end OAI
