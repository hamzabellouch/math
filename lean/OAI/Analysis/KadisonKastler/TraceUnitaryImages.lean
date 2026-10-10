import OAI.Analysis.KadisonKastler.TraceUnitaryClosure
import OAI.Analysis.KadisonKastler.UnitaryImageLinearMap

namespace OAI

/-! # Extending the boundary unitary images to the whole algebra -/

namespace KadisonKastler

noncomputable section

variable {H E I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {M N : VonNeumannAlgebra H}

/-- Closedness of the unitary trace vectors extends the boundary image
formula from a trace-dense family to every unitary. -/
theorem exists_unitary_vector_image_of_traceDense
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a) (hτN : FiniteVectorTrace τN)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E))
    (himages : ∀ i, ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J (ρ i)))
    (u : unitary (Algebra M)) :
    ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J u) := by
  have hclosed := hτN.isClosed_traceUnitary_image K hK
  have hmem : (S : E →L[ℂ] E) (J u) ∈
      K '' (unitary (Algebra N) : Set (Algebra N)) := by
    apply hclosed.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨i, hi⟩ := hρ u ε hε
    obtain ⟨v, hv⟩ := himages i
    refine ⟨K v, ⟨v, v.property, rfl⟩, ?_⟩
    rw [hv, dist_eq_norm, ← map_sub, Unitary.norm_map, ← map_sub, hJ]
    exact hi
  obtain ⟨v, hv, he⟩ := hmem
  exact ⟨⟨v, hv⟩, he⟩

/-- The normalized boundary unitary defines a unital linear map into
the neighboring algebra and sends every unitary to a unitary. -/
theorem exists_unital_linear_transfer_of_traceDense
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a) (hτN : FiniteVectorTrace τN)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E)) (hS1 : (S : E →L[ℂ] E) (J 1) = K 1)
    (himages : ∀ i, ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J (ρ i))) :
    ∃ θ : Algebra M →ₗ[ℂ] Algebra N,
      θ 1 = 1 ∧ (∀ a, K (θ a) = (S : E →L[ℂ] E) (J a)) ∧
      (∀ u : unitary (Algebra M), θ u ∈ unitary (Algebra N)) := by
  obtain ⟨θ, hθ, hθU⟩ := exists_linear_map_of_unitary_vectors J K
    (traceHilbert_injective K hK) (S : E →L[ℂ] E).toLinearMap
    (exists_unitary_vector_image_of_traceDense τM τN J K hJ hK hτN ρ hρ S himages)
  refine ⟨θ, ?_, hθ, hθU⟩
  apply traceHilbert_injective K hK
  exact (hθ 1).trans hS1

/-- The algebra transfer constructed from the boundary images is also
continuous in the operator norm, as needed for spectral approximation. -/
theorem exists_continuous_unital_transfer_of_traceDense
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a) (hτN : FiniteVectorTrace τN)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E)) (hS1 : (S : E →L[ℂ] E) (J 1) = K 1)
    (himages : ∀ i, ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J (ρ i))) :
    ∃ θ : Algebra M →L[ℂ] Algebra N,
      θ 1 = 1 ∧ (∀ a, K (θ a) = (S : E →L[ℂ] E) (J a)) ∧
      (∀ u : unitary (Algebra M), θ u ∈ unitary (Algebra N)) := by
  obtain ⟨θ, hθ1, hθ, hθU⟩ := exists_unital_linear_transfer_of_traceDense
    τM τN J K hJ hK hτN ρ hρ S hS1 himages
  exact ⟨continuousLinearMapOfUnitaryImages θ hθU, hθ1, hθ, hθU⟩

end

end KadisonKastler

end OAI
