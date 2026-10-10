import OAI.Analysis.BoundedHochschild.RepresentedAveragingAlgebra
import OAI.Analysis.BoundedHochschild.FactorCandidateCompactness

namespace OAI

/-! The compact orbit of the original factorization operator under normalized
right averages. Membership in the original algebra is preserved on its closure. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def representedAveragingOrbit (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) : Set (H →WOT[ℂ] K) :=
  {V | ∃ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) ∧
    V = weakRepresentedRightAverage π σ m W}

def closedRepresentedAveragingOrbit (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) : Set (H →WOT[ℂ] K) :=
  closure (representedAveragingOrbit π σ W)

lemma weakRepresentedRightAverage_mem_orbit (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {I : Type*} [Fintype I] (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →WOT[ℂ] K) :
    weakRepresentedRightAverage π σ m W ∈ representedAveragingOrbit π σ W := by
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, m ∘ e.symm, ?_, ?_⟩
  · exact (e.symm.sum_comp (fun i => m i * star (m i))).trans hm
  · exact congrArg ContinuousLinearMapWOT.ofCLM
      (representedRightAverage_reindex π σ e.symm m W.toCLM).symm

lemma representedAveragingOrbit_self (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    W ∈ representedAveragingOrbit π σ W := by
  have h := weakRepresentedRightAverage_mem_orbit π σ
    (fun _ : Fin 1 => (1 : M)) (by simp) W
  change ContinuousLinearMapWOT.ofCLM
    (representedRightAverage π σ (fun _ : Fin 1 => (1 : M)) W.toCLM) ∈ _ at h
  simpa only [representedRightAverage_one, ContinuousLinearMapWOT.ofCLM_toCLM] using h

lemma representedAveragingOrbit_invariant (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {I : Type*} [Fintype I] (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →WOT[ℂ] K) :
    Set.MapsTo (weakRepresentedRightAverage π σ m)
      (representedAveragingOrbit π σ W) (representedAveragingOrbit π σ W) := by
  rintro V ⟨n, v, hv, rfl⟩
  have he := congrArg ContinuousLinearMapWOT.ofCLM
    (representedRightAverage_comp π σ m v W.toCLM)
  change weakRepresentedRightAverage π σ m (weakRepresentedRightAverage π σ v W) =
    weakRepresentedRightAverage π σ (fun p : I × Fin n => m p.1 * v p.2) W at he
  rw [he]
  exact weakRepresentedRightAverage_mem_orbit π σ _
    (rightAverage_product_normalized m v hm hv) W

theorem closedRepresentedAveragingOrbit_invariant (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {I : Type*} [Fintype I] (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →WOT[ℂ] K) :
    Set.MapsTo (weakRepresentedRightAverage π σ m)
      (closedRepresentedAveragingOrbit π σ W) (closedRepresentedAveragingOrbit π σ W) :=
  (representedAveragingOrbit_invariant π σ m hm W).closure
    (weakRepresentedRightAverage_continuous π σ m)

theorem closedRepresentedAveragingOrbit_isCompact (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    IsCompact (closedRepresentedAveragingOrbit π σ W) := by
  apply (rectangularWeakBall_isCompact ‖W.toCLM‖).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (rectangularWeakBall_isClosed ‖W.toCLM‖)
  rintro V ⟨n, m, hm, rfl⟩
  exact representedRightAverage_norm_le π σ m hm W.toCLM

theorem closedRepresentedAveragingOrbit_subset_candidates
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (hσ : Function.Injective σ)
    (hclosed : ∀ C, IsClosed (representationWeakBall σ C))
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) {D : ℝ} (hD : 0 ≤ D)
    {W : H →WOT[ℂ] K} (hW : W ∈ factorCandidates σ π L D) :
    closedRepresentedAveragingOrbit π σ W ⊆ factorCandidates σ π L D := by
  apply closure_minimal _ (factorCandidates_isClosed σ hclosed π L D)
  rintro V ⟨n, m, hm, rfl⟩
  exact factorCandidates_invariant σ hσ π L hD m hm hW

end BoundedHochschild.KadisonRingrose

end

end OAI
