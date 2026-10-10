import OAI.Geometry.IsometricImmersion.Obstructions.PatchResidualTheorem
import OAI.Geometry.IsometricImmersion.Metrics.AffineTensorNeighborhood

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Model

theorem model_zero_mem_metricPatchSet
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hSV : modelSquare ⊆ V) (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    (0 : SymmetricPerturbation) ∈ metricPatchSet g0 kappa := by
  apply zero_mem_metricPatchSet
  · intro p hp
    exact hg0.2 p (hSV hp)
  · intro p hp
    rw [hbackground p (hSV (centralBox_subset_modelSquare hp))]
    exact modelCurvature_central_square hkappa (fun i => ⟨hp.1 i,hp.2 i⟩)

theorem exists_supported_patch_obstruction_in_open
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) (hzero : (0 : SymmetricPerturbation) ∈ O) :
    ∃ eta : SymmetricPerturbation, eta ∈ O ∧ eta ∈ metricPatchSet g0 kappa ∧
      SmoothPositiveOn (perturbedMetric g0 eta) V ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta) z := by
  let zeroPatch : metricPatchSet g0 kappa :=
    ⟨0,model_zero_mem_metricPatchSet hg0 hSV hkappa hbackground⟩
  let W : Set (metricPatchSet g0 kappa) := Subtype.val ⁻¹' O
  have hW : IsOpen W := hO.preimage continuous_subtype_val
  have hWzero : zeroPatch ∈ W := hzero
  obtain ⟨eta,hetaW,hg,_,hno⟩ :=
    exists_patch_obstruction_in_open hg0 hV hSV hkappa hbackground hW ⟨zeroPatch,hWzero⟩
  exact ⟨eta.val,hetaW,eta.property,hg,hno⟩

theorem exists_small_affine_patch_obstruction
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : SymmetricPerturbation,
      eta ∈ metricPatchSet g0 kappa ∧ SmoothPositiveOn (perturbedMetric g0 eta) V ∧
      (∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta) z) ∧
      (∀ k ≤ N, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (affinePushforwardMetric (perturbationTensor eta) b R) p‖ < epsilon) ∧
      ∀ i j : Fin 2, ∀ k ≤ N, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k
          (fun q => affinePushforwardMetric (perturbationTensor eta) b R q i j) p‖ < epsilon := by
  obtain ⟨eta,hetaO,hetaMetric,hg,hno⟩ := exists_supported_patch_obstruction_in_open
    hg0 hV hSV hkappa hbackground (affineTensorJetNeighborhood_isOpen R N epsilon)
      (zero_mem_affineTensorJetNeighborhood R N hepsilon)
  exact ⟨eta,hetaMetric,hg,hno,
    fun k hk p => affineTensorJetNeighborhood_physical_bounds b R N hetaO hk p,
    fun i j k hk p => affineTensorJetNeighborhood_coefficient_bounds b R N hetaO hk p i j⟩

end SmoothLocal.Perturbation

end

end OAI
