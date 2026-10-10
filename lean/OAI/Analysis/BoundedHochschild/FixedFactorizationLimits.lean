import OAI.Analysis.BoundedHochschild.WeakRepresentationAverages

namespace OAI

/-! Pointwise weak operator limits retain a fixed representation and left
factor, while the bounded right factor is allowed to vary. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakFactorFamily (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (W : H →WOT[ℂ] K) : M → (H →WOT[ℂ] H) :=
  fun a => weakFactorValue π L a W

lemma weakFactorFamily_continuous (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) :
    Continuous (weakFactorFamily π L) := by
  apply continuous_pi
  intro a
  exact weakFactorValue_continuous π L a

theorem fixedFactorization_isClosed (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (D : ℝ) :
    IsClosed {F : M → (H →WOT[ℂ] H) | ∃ W : H →L[ℂ] K, ‖W‖ ≤ D ∧
      ∀ a, F a = ContinuousLinearMapWOT.ofCLM (L.adjoint.comp ((π a).comp W))} := by
  have hcompact := (rectangularWeakBall_isCompact (H := H) (K := K) D).image
    (weakFactorFamily_continuous π L)
  have he : weakFactorFamily π L '' rectangularWeakBall D =
      {F : M → (H →WOT[ℂ] H) | ∃ W : H →L[ℂ] K, ‖W‖ ≤ D ∧
        ∀ a, F a = ContinuousLinearMapWOT.ofCLM (L.adjoint.comp ((π a).comp W))} := by
    ext F
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact ⟨W.toCLM, hW, fun _ => rfl⟩
    · rintro ⟨W, hW, hF⟩
      refine ⟨ContinuousLinearMapWOT.ofCLM W, hW, ?_⟩
      funext a
      exact (hF a).symm
  rw [he] at hcompact
  exact hcompact.isClosed

theorem factorization_of_pointwise_weak_limit
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (L : H →L[ℂ] K) {D : ℝ} {I : Type*} {l : Filter I} [l.NeBot]
    (T : I → M →L[ℂ] M) (W : I → H →L[ℂ] K) (hW : ∀ i, ‖W i‖ ≤ D)
    (hT : ∀ i a, σ (T i a) = L.adjoint.comp ((π a).comp (W i)))
    (S : M →L[ℂ] M)
    (hlim : ∀ a ξ η, Tendsto (fun i => inner ℂ η (σ (T i a) ξ)) l
      (𝓝 (inner ℂ η (σ (S a) ξ)))) :
    ∃ V : H →L[ℂ] K, ‖V‖ ≤ D ∧
      ∀ a, σ (S a) = L.adjoint.comp ((π a).comp V) := by
  have ht : Tendsto (fun i a => ContinuousLinearMapWOT.ofCLM (σ (T i a))) l
      (𝓝 (fun a => ContinuousLinearMapWOT.ofCLM (σ (S a)))) := by
    apply tendsto_pi_nhds.mpr
    intro a
    exact ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr (hlim a)
  have hf (i : I) : (fun a => ContinuousLinearMapWOT.ofCLM (σ (T i a))) ∈
      {F : M → (H →WOT[ℂ] H) | ∃ W : H →L[ℂ] K, ‖W‖ ≤ D ∧
        ∀ a, F a = ContinuousLinearMapWOT.ofCLM (L.adjoint.comp ((π a).comp W))} :=
    ⟨W i, hW i, fun a => congrArg ContinuousLinearMapWOT.ofCLM (hT i a)⟩
  obtain ⟨V, hV, he⟩ := (fixedFactorization_isClosed π L D).mem_of_tendsto ht
    (Eventually.of_forall hf)
  exact ⟨V, hV, fun a => congrArg ContinuousLinearMapWOT.toCLM (he a)⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
