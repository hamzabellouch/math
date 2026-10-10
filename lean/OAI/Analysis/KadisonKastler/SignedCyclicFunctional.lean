import OAI.Analysis.KadisonKastler.HermitianPositiveDecomposition
import OAI.Analysis.KadisonKastler.CyclicCoefficientNorm

namespace OAI

/-! # A cyclic signed-vector model for a Hermitian functional

The norm-additive positive parts give a two-summand GNS representation.
Equality in the coefficient norm bound makes its sign preserve the cyclic
subspace. Restricting there gives the precise model used in the separation
argument, with no polar-decomposition hypothesis.
-/

namespace KadisonKastler

noncomputable section

open NaimarkZFC HochschildNormalPart KadisonSimilarity
open scoped InnerProductSpace

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

theorem exists_signed_cyclic_functional (f : A →L[ℂ] ℂ)
    (hf : ∀ a, f (star a) = star (f a)) (hfn : ‖f‖ = 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (S : H →L[ℂ] H),
      ‖ξ‖ = 1 ∧ DenseRange (fun a : A => π a ξ) ∧
      IsSelfAdjoint S ∧ S * S = 1 ∧
      (∀ a, Commute S (π a)) ∧ ∀ a, f a = inner ℂ (S ξ) (π a ξ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨p, q, hpq, hn⟩ := exists_norm_additive_positive_decomposition f hf
  let H₀ := WithLp 2 (p.GNS × q.GNS)
  let π : A →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀) := sumRepresentation p.gnsStarAlgHom q.gnsStarAlgHom
  let ξ : H₀ := WithLp.toLp 2 (gnsVector p, gnsVector q)
  let S : H₀ →L[ℂ] H₀ := sumOperator 1 (-1)
  have hSnorm (x : H₀) : ‖S x‖ = ‖x‖ := by
    have hs := WithLp.prod_norm_sq_eq_of_L2 (S x)
    have hx := WithLp.prod_norm_sq_eq_of_L2 x
    change ‖S x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖-x.snd‖ ^ 2 at hs
    rw [norm_neg] at hs
    nlinarith [norm_nonneg (S x), norm_nonneg x]
  have hSsq : S * S = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change WithLp.toLp 2 (x.fst, - - x.snd) = x
    rw [neg_neg]
    rfl
  have hSstar : IsSelfAdjoint S := by
    have he : S = S.adjoint := by
      apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      intro x y
      change inner ℂ x.fst y.fst + inner ℂ (-x.snd) y.snd =
        inner ℂ x.fst y.fst + inner ℂ x.snd (-y.snd)
      simp only [inner_neg_left, inner_neg_right]
    exact he.symm
  have hScomm (a : A) : Commute S (π a) := by
    apply ContinuousLinearMap.ext
    intro x
    change WithLp.toLp 2 (p.gnsStarAlgHom a x.fst, -(q.gnsStarAlgHom a x.snd)) =
      WithLp.toLp 2 (p.gnsStarAlgHom a x.fst, q.gnsStarAlgHom a (-x.snd))
    simp only [map_neg]
  have hξsq : ‖ξ‖ ^ 2 = ‖f‖ := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact (congrArg₂ (· + ·) (gnsVector_norm_sq p) (gnsVector_norm_sq q)).trans hn
  have hξn : ‖ξ‖ = 1 := by
    rw [hfn] at hξsq
    nlinarith [norm_nonneg ξ]
  have hcoeff : coefficient π (S ξ) ξ = f := by
    ext a
    change inner ℂ (gnsVector p) (p.gnsStarAlgHom a (gnsVector p)) +
      inner ℂ (-gnsVector q) (q.gnsStarAlgHom a (gnsVector q)) = f a
    rw [inner_neg_left, gnsVector_coefficient, gnsVector_coefficient]
    exact (hpq a).symm
  have hSξ : S ξ ∈ orbitClosure π.range ξ :=
    coefficient_norm_eq_mem_orbitClosure π ξ (S ξ) (hSnorm ξ)
      (by rw [hcoeff, hξsq])
  have hinv := commuting_operator_preserves_orbitClosure π ξ S hScomm hSξ
  let K := orbitClosure π.range ξ
  let T : K →L[ℂ] K := S.restrict hinv
  let ρ := orbitRepresentation π ξ
  let ζ := orbitGenerator π ξ
  refine ⟨K, inferInstance, inferInstance, inferInstance, ρ, ζ, T,
    hξn, orbitGenerator_dense π ξ, ?_, ?_, ?_, ?_⟩
  · have he : T = T.adjoint := by
      apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      intro x y
      change inner ℂ (S x.val) y.val = inner ℂ x.val (S y.val)
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hSstar.star_eq]
    exact he.symm
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun R : H₀ →L[ℂ] H₀ => R x.val) hSsq
  · intro a
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun R : H₀ →L[ℂ] H₀ => R x.val) (hScomm a).eq
  · intro a
    exact (congrArg (fun F : A →L[ℂ] ℂ => F a) hcoeff).symm

end

end KadisonKastler

end OAI
