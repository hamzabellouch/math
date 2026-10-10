import Mathlib
import OAI.Analysis.FreeWords.PatchingExtension
import OAI.Analysis.FreeWords.PatchingFill

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem unitary_admissible_bound
    (hF : IsFactor M) (hD : IsDiffuse M)
    {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hXfin : X.Finite) (hKfin : K.Finite)
    (hXnorm : ∀ x∈X, ‖x‖≤1) (hXcenter : ∀ x∈X, τ.map x=0)
    (hKzero : ∀ k∈K, k≠0) (hK1 : 1∈K) (hKm1 : -1∈K)
    {δ C η : ℝ} (hδ : 0<δ) (hC : 0≤C) (hη : 0<η) (hη1 : η≤1)
    (hdom : (2:ℝ)^N*(2/η+1)≤C) :
    ∃ u : unitary (ConcreteAlgebra M), ∀ A, PatchingWord.Admissible X K N A →
      ‖τ.map (A.value (fun k => (u^k).val))‖≤patchingBudget δ C (1-η)+2^N*η := by
  obtain ⟨v,hv⟩ := maximal_patching_bounds τ {a | PatchingWord.Admissible X K N a}
    (patchingBudget δ C) (1-η) (continuous_patchingBudget δ C)
    (by rw [patchingBudget_zero]) (sub_nonneg.mpr hη1)
  have ht : (τ.map v.support).re=1-η := by
    apply le_antisymm hv.1.1
    by_contra h
    have hstrict : (τ.map v.support).re<1-η := lt_of_not_ge h
    obtain ⟨v',hvv',hv'⟩ := patching_extension τ hF hD hXfin hKfin hXnorm hXcenter
      hKzero hK1 hKm1 hδ hC hη hdom v hstrict hv.1.2
    exact (not_le_of_gt hvv') (hv.2 hv' hvv'.le)
  exact fill_partial_bound τ v hXnorm ht (fun A hA => ht ▸ hv.1.2 A hA)

end

end KKLocalPatching
end

end OAI
