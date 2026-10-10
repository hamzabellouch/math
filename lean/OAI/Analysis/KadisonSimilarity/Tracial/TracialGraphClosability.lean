import OAI.Analysis.KadisonSimilarity.Derivation.CyclicGraphEmbedding
import OAI.Analysis.KadisonSimilarity.Derivation.TracialCornerCyclicity
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

/-! A separating tracial vector makes the cyclic graph closable. Testing
against its dense commutant orbit proves this directly on the closed graph. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {A H K E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A tracial cyclic source and a target subrepresentation inside a common
normal representation have a closable orbit map if the source identity
vector separates that normal algebra. -/
theorem tracial_cyclic_graph_closable
    (G : TracialCornerGeometry A H)
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (π : A →⋆ₐ[ℂ] (E →L[ℂ] E))
    (M : VonNeumannAlgebra E) (hπ : ∀ a, π a ∈ M)
    (I : H →ₗᵢ[ℂ] E) (J : K →ₗᵢ[ℂ] E)
    (hI : ∀ a, I.toContinuousLinearMap.comp (G.left a) =
      (π a).comp I.toContinuousLinearMap)
    (hJ : ∀ a, J.toContinuousLinearMap.comp (ρ a) =
      (π a).comp J.toContinuousLinearMap)
    (hsep : ∀ a : M.toStarSubalgebra, (a : E →L[ℂ] E) (I (G.vector 1)) = 0 → a = 0)
    (ξ : K) :
    ∀ x : cyclicGraph G.left ρ (G.vector 1) ξ,
      (x : RectangularSum H K).fst = 0 → (x : RectangularSum H K).snd = 0 := by
  let Ω := I (G.vector 1)
  have htest (T : M.commutant.toStarSubalgebra)
      (x : cyclicGraph G.left ρ (G.vector 1) ξ) :
      inner ℂ (J (x : RectangularSum H K).snd) ((T : E →L[ℂ] E) Ω) =
        inner ℂ (J ξ) ((T : E →L[ℂ] E) (I (G.conjugation (x : RectangularSum H K).fst))) := by
    have hc : IsClosed {z : RectangularSum H K |
        inner ℂ (J z.snd) ((T : E →L[ℂ] E) Ω) =
          inner ℂ (J ξ) ((T : E →L[ℂ] E) (I (G.conjugation z.fst)))} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply closure_minimal (s := Set.range
      (orbitLinearMap (pairRepresentation G.left ρ).range
        (WithLp.toLp 2 (G.vector 1, ξ)))) ?_ hc x.property
    rintro z ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := b.property
    change pairRepresentation G.left ρ a = _ at ha
    change inner ℂ (J (((b : (pairRepresentation G.left ρ).range) :
        RectangularSum H K →L[ℂ] RectangularSum H K)
        (WithLp.toLp 2 (G.vector 1, ξ))).snd) ((T : E →L[ℂ] E) Ω) =
      inner ℂ (J ξ) ((T : E →L[ℂ] E) (I (G.conjugation
        (((b : (pairRepresentation G.left ρ).range) :
          RectangularSum H K →L[ℂ] RectangularSum H K)
          (WithLp.toLp 2 (G.vector 1, ξ))).fst)))
    rw [← ha]
    change inner ℂ (J ((pairRepresentation G.left ρ a
        (WithLp.toLp 2 (G.vector 1, ξ))).snd)) ((T : E →L[ℂ] E) Ω) =
      inner ℂ (J ξ) ((T : E →L[ℂ] E) (I (G.conjugation
        (pairRepresentation G.left ρ a (WithLp.toLp 2 (G.vector 1, ξ))).fst)))
    rw [pairRepresentation_fst, pairRepresentation_snd]
    change inner ℂ (J (ρ a ξ)) ((T : E →L[ℂ] E) Ω) =
      inner ℂ (J ξ) ((T : E →L[ℂ] E) (I (G.conjugation (G.left a (G.vector 1)))))
    rw [G.left_vector, mul_one, G.conjugation_vector]
    have hIa := congrArg (fun S : H →L[ℂ] E => S (G.vector 1)) (hI (star a))
    have hJa := congrArg (fun S : K →L[ℂ] E => S ξ) (hJ a)
    change I (G.left (star a) (G.vector 1)) = π (star a) Ω at hIa
    rw [G.left_vector, mul_one] at hIa
    change J (ρ a ξ) = π a (J ξ) at hJa
    rw [hJa, hIa, map_star, ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.adjoint_inner_right]
    have hcomm : (π a).adjoint.comp (T : E →L[ℂ] E) =
        (T : E →L[ℂ] E).comp (π a).adjoint := by
      have h := VonNeumannAlgebra.mem_commutant_iff.mp T.property (π (star a)) (hπ (star a))
      rw [map_star, ContinuousLinearMap.star_eq_adjoint] at h
      ext z
      exact congrArg (fun S : E →L[ℂ] E => S z) h
    exact congrArg (fun S : E →L[ℂ] E => inner ℂ (J ξ) (S Ω)) hcomm
  intro x hx
  apply J.injective
  rw [map_zero]
  apply ext_inner_right ℂ
  intro y
  have hd : DenseRange (fun T : M.commutant.toStarSubalgebra => (T : E →L[ℂ] E) Ω) :=
    Generator.commutant_orbit_dense M Ω hsep
  refine hd.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro T
  have h := htest T x
  rw [hx, map_zero, map_zero, map_zero, inner_zero_right] at h
  simpa only [inner_zero_left] using h

/-- Assemble the cyclic embeddings when the source trace vector is
separating in the target's normal algebra. -/
theorem countable_embedding_of_separating_trace_vector
    [TopologicalSpace.SeparableSpace E]
    (G : TracialCornerGeometry A H) (π : A →⋆ₐ[ℂ] (E →L[ℂ] E))
    (M : VonNeumannAlgebra E) (hπ : ∀ a, π a ∈ M)
    (I : H →ₗᵢ[ℂ] E)
    (hI : ∀ a, I.toContinuousLinearMap.comp (G.left a) =
      (π a).comp I.toContinuousLinearMap)
    (hsep : ∀ a : M.toStarSubalgebra, (a : E →L[ℂ] E) (I (G.vector 1)) = 0 → a = 0) :
    ∃ U : E →ₗᵢ[ℂ] CountableCopies H, ∀ a,
      U.toContinuousLinearMap.comp (π a) =
        (countableAmplify (G.left a)).comp U.toContinuousLinearMap := by
  let D := cyclicDecompositionData π.range
  have hlocal (i : D.generators) : ∃ J : D.Space i →ₗᵢ[ℂ] H, ∀ a,
      J.toContinuousLinearMap.comp (D.representation π i a) =
        (G.left a).comp J.toContinuousLinearMap := by
    apply cyclic_embedding_of_closable_graph G.left (D.representation π i)
      (G.vector 1) (D.generator π i) (D.generator_dense π i)
    apply tracial_cyclic_graph_closable G (D.representation π i) π M hπ I
      (D.summands.inclusion i) hI
      (fun a => (D.representation_intertwines π i a).symm) hsep
  choose J hJ using hlocal
  exact countable_embedding_of_cyclic_embeddings π G.left D J hJ

end KadisonSimilarity

end

end OAI
