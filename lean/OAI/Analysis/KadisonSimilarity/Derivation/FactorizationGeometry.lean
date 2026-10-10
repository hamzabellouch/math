import OAI.Analysis.KadisonSimilarity.Derivation.FactorizationSpace

namespace OAI

/-! # Removing the kernel of a star intertwiner

A surjective intertwiner with a bounded right inverse restricts to an
isomorphism on the orthogonal complement of its kernel. Orthogonal
projection does not increase the right-inverse norm, which retains the
sharp bound needed for quantitative similarity.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Restriction of a star representation to a closed invariant subspace. -/
def restrictStarRepresentation (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (M : ClosedSubmodule ℂ K)
    (hM : ∀ a x, x ∈ M → σ a x ∈ M) : A →⋆ₐ[ℂ] (M →L[ℂ] M) where
  toFun a := (σ a).restrict (hM a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    let : CompleteSpace M.toSubmodule := M.isClosed.completeSpace_coe
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : K) (σ (star a) (x : K)) =
      inner ℂ y (((σ a).restrict (hM a)).adjoint x)
    rw [map_star, star_eq_adjoint, adjoint_inner_right, adjoint_inner_right]
    rfl

/-- A bounded right inverse of a surjective star intertwiner gives
similarity with no increase in the product of its two norms. -/
theorem quantitative_similarity_of_surjective_intertwiner
    (π : BoundedUnitalHom A H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (L : K →L[ℂ] H) (hLW : L.comp W = 1)
    (hL : ∀ a, L.comp (σ a) = (π.1 a).comp L) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  let N : ClosedSubmodule ℂ K := ⟨L.ker, L.isClosed_ker⟩
  let : CompleteSpace N.toSubmodule := N.isClosed.completeSpace_coe
  let E : ClosedSubmodule ℂ K := ⟨N.toSubmoduleᗮ, N.toSubmodule.isClosed_orthogonal⟩
  let : CompleteSpace E.toSubmodule := E.isClosed.completeSpace_coe
  have hN (a : A) (x : K) (hx : x ∈ N) : σ a x ∈ N := by
    change L (σ a x) = 0
    have h := congrArg (fun T : K →L[ℂ] H => T x) (hL a)
    change L x = 0 at hx
    simpa only [comp_apply, hx, map_zero] using h
  have hE (a : A) (x : K) (hx : x ∈ E) : σ a x ∈ E := by
    apply (N.toSubmodule.mem_orthogonal _).mpr
    intro y hy
    rw [← adjoint_inner_left, ← star_eq_adjoint, ← map_star]
    exact (N.toSubmodule.mem_orthogonal x).mp hx _ (hN (star a) y hy)
  let σ₀ := restrictStarRepresentation σ E hE
  let L₀ : E →L[ℂ] H := L.domRestrict E.toSubmodule
  let W₀ : H →L[ℂ] E := E.toSubmodule.orthogonalProjectionOnto.comp W
  have hL₀W₀ : L₀.comp W₀ = 1 := by
    ext x
    change L ((N.toSubmoduleᗮ).orthogonalProjectionOnto (W x) : K) = x
    rw [N.toSubmodule.orthogonalProjectionOnto_orthogonal]
    change L (W x - N.toSubmodule.starProjection (W x)) = x
    have hz : L (N.toSubmodule.starProjection (W x)) = 0 :=
      Submodule.starProjection_apply_mem N.toSubmodule (W x)
    have hw := congrArg (fun T : H →L[ℂ] H => T x) hLW
    simpa only [map_sub, hz, sub_zero, comp_apply, one_def, id_apply] using hw
  have hL₀inj : Function.Injective L₀ := by
    intro x y hxy
    apply Subtype.ext
    have hk : (x : K) - (y : K) ∈ N := by
      change L ((x : K) - (y : K)) = 0
      change L (x : K) = L (y : K) at hxy
      rw [map_sub, hxy, sub_self]
    have he : (x : K) - (y : K) ∈ N.toSubmoduleᗮ := E.sub_mem x.property y.property
    have hz := (N.toSubmodule.mem_orthogonal _).mp he _ hk
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)
  have hW₀L₀ : W₀.comp L₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply hL₀inj
    exact congrArg (fun T : H →L[ℂ] H => T (L₀ x)) hL₀W₀
  have hL₀ (a : A) : L₀.comp (σ₀ a) = (π.1 a).comp L₀ := by
    ext x
    exact congrArg (fun T : K →L[ℂ] H => T x) (hL a)
  have hW₀ (a : A) : W₀.comp (π.1 a) = (σ₀ a).comp W₀ := by
    apply ContinuousLinearMap.ext
    intro x
    apply hL₀inj
    have hlx := congrArg (fun T : H →L[ℂ] H => T x) hL₀W₀
    have hla := congrArg (fun T : H →L[ℂ] H => T (π.1 a x)) hL₀W₀
    have hi := congrArg (fun T : E →L[ℂ] H => T (W₀ x)) (hL₀ a)
    change L₀ (W₀ (π.1 a x)) = L₀ (σ₀ a (W₀ x))
    simpa only [comp_apply, one_def, id_apply] using hla.trans (hi.trans
      (congrArg (π.1 a) hlx)).symm
  have hnW : ‖W₀‖ ≤ ‖W‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact (E.toSubmodule.norm_orthogonalProjectionOnto_apply_le (W x)).trans
      (W.le_opNorm x)
  have hnL : ‖L₀‖ ≤ ‖L‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact L.le_opNorm (x : K)
  obtain ⟨S, hS, hstar⟩ := quantitative_similarity_of_intertwiner
    π σ₀ W₀ L₀ hL₀W₀ hW₀L₀ hW₀
  exact ⟨S, hS.trans (mul_le_mul hnW hnL (norm_nonneg _) (norm_nonneg _)), hstar⟩

/-- Multiplicativity upgrades a bounded star-representation factorization
to a similarity, with the original product bound. -/
theorem quantitative_similarity_of_factorization
    (π : BoundedUnitalHom A H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hf : ∀ a, L.comp ((σ a).comp W) = π.1 a) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  let M := factorizationSpace σ W
  let : CompleteSpace M.toSubmodule := M.isClosed.completeSpace_coe
  let σ₀ := restrictStarRepresentation σ M (factorizationSpace_invariant σ W)
  let W₀ : H →L[ℂ] M := W.codRestrict M.toSubmodule (right_mem_factorizationSpace σ W)
  let L₀ : M →L[ℂ] H := L.domRestrict M.toSubmodule
  have hLW : L₀.comp W₀ = 1 := by
    ext x
    change L (W x) = x
    have h := congrArg (fun T : H →L[ℂ] H => T x) (hf 1)
    simpa only [comp_apply, map_one, one_def, id_apply] using h
  have hL (a : A) : L₀.comp (σ₀ a) = (π.1 a).comp L₀ := by
    ext x
    exact left_intertwines_factorizationSpace π σ W L hf a x x.property
  have hnW : ‖W₀‖ ≤ ‖W‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact W.le_opNorm x
  have hnL : ‖L₀‖ ≤ ‖L‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact L.le_opNorm (x : K)
  obtain ⟨S, hS, hs⟩ := quantitative_similarity_of_surjective_intertwiner
    π σ₀ W₀ L₀ hLW hL
  exact ⟨S, hS.trans (mul_le_mul hnW hnL (norm_nonneg _) (norm_nonneg _)), hs⟩

end KadisonSimilarity

end

end OAI
