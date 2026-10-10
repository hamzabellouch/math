import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ ξ' : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center center' : CoefficientTorus (K := LayerSamplerVariables G I n B) U}

namespace AllocatedExternalCandidateSampler

theorem changeNarrow_zero_layers_typeZero
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ stride cells center) (hξ' : 0 < ξ') :
    AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ' stride cells center' := by
  apply allocatedExternalCandidateSampler_zero_layers B U b S hb o hR hσ poly hm
    center' N τ ξ' stride cells A.size_pos A.trim_pos hξ' A.stride_pos A.bases_nonempty
  simpa only [allocatedExternalCandidateWidths_zero_layers] using A.smooth_mass_pos

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem nativeDetection_zero_layers_typeZero_iff
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ stride cells center)
    (A' : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ' stride cells center')
    (degree : ℕ) (pSlice pTest pNative α : ℝ) :
    A.NativeDetection degree pSlice pTest pNative α ↔
      A'.NativeDetection degree pSlice pTest pNative α := by
  unfold NativeDetection
  simp only [law_zero_layers]
  unfold physical Path Site sides
  generalize_proofs hbox hbase hpos hmass hpos' hmass'
  revert hpos hmass hpos' hmass'
  rw [allocatedExternalCandidateWidths_zero_layers, allocatedExternalCandidateWidths_zero_layers]
  intros
  rfl

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
