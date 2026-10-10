import OAI.Geometry.IsometricImmersion.Calculus.AffineTensorJetBounds
import OAI.Geometry.IsometricImmersion.Assembly.SupportedNeighborhoods

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def affineTensorJetNeighborhood (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ)
    (epsilon : ℝ) : Set SymmetricPerturbation :=
  {η | ∀ k : Fin (N+1),
    perturbationSeminorm k.val η < epsilon / affineTensorOrderFactor R N}

theorem affineTensorJetNeighborhood_isOpen
    (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) (epsilon : ℝ) :
    IsOpen (affineTensorJetNeighborhood R N epsilon) := by
  unfold affineTensorJetNeighborhood
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_lt (perturbationSeminorm_continuous k.val) continuous_const

theorem zero_mem_affineTensorJetNeighborhood
    (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (0 : SymmetricPerturbation) ∈ affineTensorJetNeighborhood R N epsilon := by
  intro k
  have hzero : perturbationSeminorm k.val 0 = 0 := map_zero (perturbationSeminormFamily k.val)
  rw [hzero]
  exact div_pos hepsilon (affineTensorOrderFactor_pos R N)

theorem affineTensorJetNeighborhood_mem_nhds_zero
    (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    affineTensorJetNeighborhood R N epsilon ∈ 𝓝 (0 : SymmetricPerturbation) :=
  (affineTensorJetNeighborhood_isOpen R N epsilon).mem_nhds
    (zero_mem_affineTensorJetNeighborhood R N hepsilon)

theorem affineTensorJetNeighborhood_physical_bounds
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) {epsilon : ℝ}
    {η : SymmetricPerturbation} (hη : η ∈ affineTensorJetNeighborhood R N epsilon)
    {k : ℕ} (hk : k ≤ N) (p : Coord) :
    ‖iteratedFDeriv ℝ k (affinePushforwardMetric (perturbationTensor η) b R) p‖ < epsilon := by
  have hsmall := hη ⟨k, Nat.lt_succ_of_le hk⟩
  change perturbationSeminorm k η < epsilon / affineTensorOrderFactor R N at hsmall
  calc
    _ ≤ affineTensorOrderFactor R N * perturbationSeminorm k η :=
      supported_affine_tensor_finite_jet_le η b R hk p
    _ = perturbationSeminorm k η * affineTensorOrderFactor R N := mul_comm _ _
    _ < epsilon := (lt_div_iff₀ (affineTensorOrderFactor_pos R N)).mp hsmall

theorem affineTensorJetNeighborhood_coefficient_bounds
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) {epsilon : ℝ}
    {η : SymmetricPerturbation} (hη : η ∈ affineTensorJetNeighborhood R N epsilon)
    {k : ℕ} (hk : k ≤ N) (p : Coord) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ k
      (fun q => affinePushforwardMetric (perturbationTensor η) b R q i j) p‖ < epsilon :=
  (norm_iteratedFDeriv_affinePushforwardCoefficient_le
    (perturbationTensor_contDiff η).contDiffOn isOpen_univ b R (mem_univ _) k i j).trans_lt
      (affineTensorJetNeighborhood_physical_bounds b R N hη hk p)

theorem exists_open_affine_tensor_budget_neighborhood
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) (S : Set Coord)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ O : Set SymmetricPerturbation, IsOpen O ∧ 0 ∈ O ∧
      ∀ η ∈ O, ∀ k ≤ N, ∀ p ∈ S,
        ‖iteratedFDeriv ℝ k (affinePushforwardMetric (perturbationTensor η) b R) p‖ < epsilon := by
  refine ⟨affineTensorJetNeighborhood R N epsilon,
    affineTensorJetNeighborhood_isOpen R N epsilon,
    zero_mem_affineTensorJetNeighborhood R N hepsilon,?_⟩
  intro η hη k hk p _
  exact affineTensorJetNeighborhood_physical_bounds b R N hη hk p

theorem exists_affine_diagonal_budget_neighborhoods
    (b : ℕ → Coord) (R : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (budget : ℕ → ℝ) (hbudget : ∀ j, 0 < budget j) :
    ∃ O : ℕ → Set SymmetricPerturbation,
      (∀ j, IsOpen (O j) ∧ (0 : SymmetricPerturbation) ∈ O j) ∧
      ∀ j, ∀ η ∈ O j, ∀ k ≤ j, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k
          (affinePushforwardMetric (perturbationTensor η) (b j) (R j)) p‖ < budget j := by
  refine ⟨fun j => affineTensorJetNeighborhood (R j) j (budget j),?_,?_⟩
  · intro j
    exact ⟨affineTensorJetNeighborhood_isOpen (R j) j (budget j),
      zero_mem_affineTensorJetNeighborhood (R j) j (hbudget j)⟩
  · intro j η hη k hk p
    exact affineTensorJetNeighborhood_physical_bounds (b j) (R j) j hη hk p

end SmoothLocal.Perturbation

end

end OAI
