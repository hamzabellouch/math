import OAI.Analysis.KadisonSimilarity.Representation.StandardEmbeddingAssembly
import OAI.Analysis.KadisonSimilarity.Representation.NormalRepresentationReduction

namespace OAI

/-! Equality of vector functionals constructs a cyclic intertwining
isometry. Countable cyclic assembly then gives the standard
embedding required by the finite-factor application. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The isometry on a dense cyclic orbit extends to the complete Hilbert
space and retains its intertwining identity. -/
theorem cyclic_isometry_of_orbit_norms
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (ξ : H) (η : K) (hξ : DenseRange (fun a : A => σ a ξ))
    (hn : ∀ a, ‖σ a ξ‖ = ‖ρ a η‖) :
    ∃ J : H →ₗᵢ[ℂ] K, ∀ a,
      J.toContinuousLinearMap.comp (σ a) = (ρ a).comp J.toContinuousLinearMap := by
  let e : A →ₗ[ℂ] H :=
    { toFun := fun a => σ a ξ
      map_add' a b := by simp
      map_smul' c a := by simp }
  let f : A →ₗ[ℂ] K :=
    { toFun := fun a => ρ a η
      map_add' a b := by simp
      map_smul' c a := by simp }
  have hd : DenseRange e := hξ
  have hnorm (a : A) : ‖f a‖ = ‖e a‖ := (hn a).symm
  let J : H →ₗᵢ[ℂ] K := f.extendOfIsometry (e := e) hd hnorm
  have he (a : A) : J (e a) = f a :=
    LinearMap.extendOfIsometry_eq f hd hnorm a
  refine ⟨J, fun a => ?_⟩
  ext x
  refine hξ.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  change J (σ a (e b)) = ρ a (J (e b))
  have hab : σ a (e b) = e (a * b) := by
    change σ a (σ b ξ) = σ (a * b) ξ
    rw [map_mul]
    rfl
  rw [hab, he, he]
  change ρ (a * b) η = ρ a (ρ b η)
  rw [map_mul]
  rfl

/-- Equality of vector functionals supplies the norm identity on each
cyclic orbit by testing the positive square `a* a`. -/
theorem orbit_norms_of_vector_functionals
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (ξ : H) (η : K)
    (h : ∀ a, inner ℂ ξ (σ a ξ) = inner ℂ η (ρ a η)) (a : A) :
    ‖σ a ξ‖ = ‖ρ a η‖ := by
  have hp := h (star a * a)
  rw [map_mul, map_star, map_mul, map_star] at hp
  change inner ℂ ξ ((σ a).adjoint (σ a ξ)) =
    inner ℂ η ((ρ a).adjoint (ρ a η)) at hp
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right] at hp
  have hsq := congrArg Complex.re hp
  change RCLike.re (inner ℂ (σ a ξ) (σ a ξ)) =
    RCLike.re (inner ℂ (ρ a η) (ρ a η)) at hsq
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), inner_self_eq_norm_sq (𝕜 := ℂ)] at hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

variable [PartialOrder A] [StarOrderedRing A]

/-- Once the normal vector-functional realization is constructed, the
standard embedding follows without a separate decomposition assumption. -/
theorem normal_standard_embedding_of_vector_realization
    [TopologicalSpace.SeparableSpace H]
    (τ : A →ₚ[ℂ] ℂ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hvector : ∀ ξ : H, ∃ η : τ.GNS, ∀ a,
      inner ℂ ξ (σ a ξ) = inner ℂ η (τ.gnsStarAlgHom a η)) :
    HiaiNormalStandardEmbeddingInput τ σ := by
  let D := cyclicDecompositionData σ.range
  have hlocal (i : D.generators) : ∃ J : D.Space i →ₗᵢ[ℂ] τ.GNS,
      ∀ a, J.toContinuousLinearMap.comp (D.representation σ i a) =
        (τ.gnsStarAlgHom a).comp J.toContinuousLinearMap := by
    obtain ⟨η, hη⟩ := hvector (i : H)
    apply cyclic_isometry_of_orbit_norms (D.representation σ i) τ.gnsStarAlgHom
      (D.generator σ i) η (D.generator_dense σ i)
    intro a
    change ‖σ a (i : H)‖ = ‖τ.gnsStarAlgHom a η‖
    exact orbit_norms_of_vector_functionals σ τ.gnsStarAlgHom i η hη a
  choose J hJ using hlocal
  exact countable_embedding_of_cyclic_embeddings σ τ.gnsStarAlgHom D J hJ

end KadisonSimilarity

end

end OAI
