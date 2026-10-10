import OAI.Analysis.KadisonSimilarity.Derivation.FactorizationGeometry
import OAI.Analysis.KadisonSimilarity.Similarity.SimilarityCompleteBound

namespace OAI

/-! Similarity descends to a bounded algebraic retract. This is used for
the first-coordinate corner after finite matrix amplification. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem similarity_of_retract (π : BoundedUnitalHom A H) (ρ : BoundedUnitalHom A K)
    (U : H →L[ℂ] K) (V : K →L[ℂ] H)
    (h : ∀ a, V.comp ((ρ.1 a).comp U) = π.1 a)
    (hρ : SimilarToStar A K ρ) : SimilarToStar A H π := by
  obtain ⟨S, hS⟩ := hρ
  let σ := similarityStarRepresentation ρ S hS
  let W : H →L[ℂ] K := (S : K →L[ℂ] K).comp U
  let L : K →L[ℂ] H := V.comp (↑S⁻¹ : K →L[ℂ] K)
  have hf (a : A) : L.comp ((σ a).comp W) = π.1 a := by
    ext x
    have hc (z : K) : (↑S⁻¹ : K →L[ℂ] K) ((S : K →L[ℂ] K) z) = z := by
      have hz := congrArg (fun T : K →L[ℂ] K => T z) (Units.inv_mul S)
      simpa only [mul_apply_eq_comp, one_def, id_apply] using hz
    change V ((↑S⁻¹ : K →L[ℂ] K) ((S : K →L[ℂ] K)
      (ρ.1 a ((↑S⁻¹ : K →L[ℂ] K) ((S : K →L[ℂ] K) (U x)))))) = π.1 a x
    rw [hc, hc]
    exact congrArg (fun T : H →L[ℂ] H => T x) (h a)
  obtain ⟨R, _, hR⟩ := quantitative_similarity_of_factorization π σ W L hf
  exact ⟨R, hR⟩

end KadisonSimilarity

end

end OAI
