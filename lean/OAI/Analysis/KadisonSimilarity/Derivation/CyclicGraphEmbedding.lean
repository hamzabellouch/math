import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerPolar
import OAI.Analysis.KadisonSimilarity.Derivation.RectangularDerivations

namespace OAI

/-! A closable cyclic orbit map gives an isometric subrepresentation. The
closed graph is itself a cyclic reducing representation, and its two
coordinate maps yield the embedding by polar decomposition. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Direct sum of two star representations, with the Hilbert product norm. -/
def pairRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    A →⋆ₐ[ℂ] (RectangularSum H K →L[ℂ] RectangularSum H K) where
  toAlgHom := (rectangularRepresentation σ ρ 0 (by simp)).1
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ y (rectangularTriangular (σ (star a)) 0 (ρ (star a)) x) =
      inner ℂ y ((rectangularTriangular (σ a) 0 (ρ a)).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ y.fst (rectangularTriangular (σ (star a)) 0 (ρ (star a)) x).fst +
        inner ℂ y.snd (rectangularTriangular (σ (star a)) 0 (ρ (star a)) x).snd =
      inner ℂ (rectangularTriangular (σ a) 0 (ρ a) y).fst x.fst +
        inner ℂ (rectangularTriangular (σ a) 0 (ρ a) y).snd x.snd
    simp only [rectangularTriangular_fst,
      rectangularTriangular_snd, zero_apply, add_zero, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

@[simp] theorem pairRepresentation_fst (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) (x : RectangularSum H K) :
    (pairRepresentation σ ρ a x).fst = σ a x.fst := by
  change (rectangularTriangular (σ a) 0 (ρ a) x).fst = _
  simp only [rectangularTriangular_fst, zero_apply, add_zero]

@[simp] theorem pairRepresentation_snd (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) (x : RectangularSum H K) :
    (pairRepresentation σ ρ a x).snd = ρ a x.snd :=
  rectangularTriangular_snd _ _ _ _

/-- The closed cyclic graph of the orbit map `σ(a)Ω ↦ ρ(a)ξ`. -/
def cyclicGraph (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : H) (ξ : K) :=
  orbitClosure (pairRepresentation σ ρ).range (WithLp.toLp 2 (Ω, ξ))

/-- Trivial vertical part of the closed cyclic graph is exactly the
closability condition needed by the polar construction. -/
theorem cyclic_embedding_of_closable_graph
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (ξ : K) (hξ : DenseRange (fun a : A => ρ a ξ))
    (hclose : ∀ x : cyclicGraph σ ρ Ω ξ,
      (x : RectangularSum H K).fst = 0 → (x : RectangularSum H K).snd = 0) :
    ∃ J : K →ₗᵢ[ℂ] H, ∀ a,
      J.toContinuousLinearMap.comp (ρ a) = (σ a).comp J.toContinuousLinearMap := by
  let π := pairRepresentation σ ρ
  let ζ : RectangularSum H K := WithLp.toLp 2 (Ω, ξ)
  let Q := cyclicGraph σ ρ Ω ξ
  let ν := orbitRepresentation π ζ
  let X : Q →L[ℂ] H := (WithLp.fstL 2 ℂ H K).comp Q.toSubmodule.subtypeL
  let Y : Q →L[ℂ] K := (WithLp.sndL 2 ℂ H K).comp Q.toSubmodule.subtypeL
  have hXi : Function.Injective X := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply (WithLp.equiv 2 (H × K)).injective
    apply Prod.ext
    · change (x : RectangularSum H K).fst - (y : RectangularSum H K).fst = 0
      exact sub_eq_zero.mpr hxy
    · exact hclose (x - y) (by
        change (x : RectangularSum H K).fst - (y : RectangularSum H K).fst = 0
        exact sub_eq_zero.mpr hxy)
  have hYd : DenseRange Y := by
    have hsub : Set.range (fun a : A => ρ a ξ) ⊆ Set.range Y := by
      rintro _ ⟨a, rfl⟩
      let q : Q := ⟨π a ζ, orbitClosure_invariant π.range ζ (π.rangeRestrict a) ζ
        (self_mem_orbitClosure π.range ζ)⟩
      refine ⟨q, ?_⟩
      change (pairRepresentation σ ρ a ζ).snd = ρ a ξ
      rw [pairRepresentation_snd]
      rfl
    intro y
    exact closure_mono hsub (hξ y)
  apply isometry_of_injective_dense_correspondence ν σ ρ X Y hXi hYd
  · intro a
    ext x
    exact pairRepresentation_fst σ ρ a x
  · intro a
    ext x
    exact pairRepresentation_snd σ ρ a x

end KadisonSimilarity

end

end OAI
