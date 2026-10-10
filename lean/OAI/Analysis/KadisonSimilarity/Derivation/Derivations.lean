import OAI.Analysis.KadisonSimilarity.OperatorAlgebra
import OAI.Analysis.Unitarizability.Triangular
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

/-!
# The triangular representation of a bounded derivation

Similarity of the upper triangular representation gives an inner implementer
for a bounded derivation.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The orthogonal projection onto a closed subspace invariant under a family
and its adjoints commutes with that family. -/
theorem orthogonal_projection_commutes (U : A → (H →L[ℂ] H))
    (hstar : ∀ a, U (star a) = star (U a)) (M : ClosedSubmodule ℂ H)
    (hM : ∀ a x, x ∈ M → U a x ∈ M) (a : A) :
    Commute M.toSubmodule.starProjection (U a) := by
  change M.toSubmodule.starProjection * U a = U a * M.toSubmodule.starProjection
  ext x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM a _ (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    simp only [mul_apply_eq_comp]
    have hadj : (U a).adjoint = U (star a) := (hstar a).symm
    have hzero : inner ℂ ((U a) (x - M.toSubmodule.starProjection x)) w = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hadj]
      exact M.toSubmodule.starProjection_inner_eq_zero x _ (hM (star a) w hw)
    simpa only [map_sub, ContinuousLinearMap.coe_coe] using hzero

/-- Similarity to a star representation supplies a bounded commuting
projection onto every closed invariant subspace. -/
theorem exists_commuting_projection (π : BoundedUnitalHom A H)
    (hπ : SimilarToStar A H π) (M : ClosedSubmodule ℂ H)
    (hM : ∀ a x, x ∈ M → π.1 a x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ ∀ a, Commute P (π.1 a) := by
  rcases hπ with ⟨S, hS⟩
  let e := ContinuousLinearEquiv.ofUnit S
  let U (a : A) : H →L[ℂ] H :=
    e.toContinuousLinearMap * π.1 a * e.symm.toContinuousLinearMap
  let N : ClosedSubmodule ℂ H := M.mapEquiv e
  have hU : ∀ a, U (star a) = star (U a) := hS
  have hN : ∀ a x, x ∈ N → U a x ∈ N := by
    intro a x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨π.1 a y, hM a y hy, by simp [U, mul_apply_eq_comp]⟩
  let Q := N.toSubmodule.starProjection
  let P : H →L[ℂ] H := e.symm.toContinuousLinearMap.comp (Q.comp e.toContinuousLinearMap)
  have hmem (x : H) : P x ∈ M := by
    have h := Submodule.starProjection_apply_mem N.toSubmodule (e x)
    rcases h with ⟨y, hy, he⟩
    change e.symm (Q (e x)) ∈ M
    rw [← he]
    simpa using hy
  have hfix (x : H) (hx : x ∈ M) : P x = x := by
    have hn : e x ∈ N := ⟨x, hx, rfl⟩
    change e.symm (Q (e x)) = x
    rw [Submodule.starProjection_eq_self_iff.mpr hn]
    simp
  refine ⟨P, hmem, hfix, ?_⟩
  intro a
  have hq := orthogonal_projection_commutes U hU N hN a
  change P * π.1 a = π.1 a * P
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => e.symm (T (e x))) hq.eq
  simpa [P, Q, U, mul_apply_eq_comp] using h

namespace Derivation

open Dixmier.Triangular

/-- The bounded upper triangular operator with equal diagonal blocks. -/
def triangularOperator (σ d : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  diagonal σ + inl.comp (d.comp (WithLp.sndL 2 ℂ H H))

omit [CompleteSpace H] in
@[simp] theorem triangularOperator_fst (σ d : H →L[ℂ] H) (x : Double H) :
    (triangularOperator σ d x).fst = σ x.fst + d x.snd := by
  simp [triangularOperator, inl]

omit [CompleteSpace H] in
@[simp] theorem triangularOperator_snd (σ d : H →L[ℂ] H) (x : Double H) :
    (triangularOperator σ d x).snd = σ x.snd := by
  simp [triangularOperator, inl]

omit [CompleteSpace H] in
/-- A bounded derivation vanishes at the identity. -/
theorem map_one_eq_zero (σ : BoundedUnitalHom A H) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = σ.1 a * δ b + δ a * σ.1 b) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [one_mul, map_one, mul_one] at h
  have h' : δ 1 + 0 = δ 1 + δ 1 := by simpa using h
  exact (add_left_cancel h').symm

/-- The triangular algebra representation associated to a bounded derivation. -/
def representation (σ : BoundedUnitalHom A H) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = σ.1 a * δ b + δ a * σ.1 b) :
    BoundedUnitalHom A (Double H) := by
  let f : A →ₗ[ℂ] (Double H →L[ℂ] Double H) :=
    { toFun := fun a => triangularOperator (σ.1 a) (δ a)
      map_add' := by
        intro a b
        ext x
        apply (WithLp.equiv 2 (H × H)).injective
        apply Prod.ext
        · simp; abel
        · simp
      map_smul' := by
        intro c a
        ext x
        apply (WithLp.equiv 2 (H × H)).injective
        apply Prod.ext <;> simp [smul_add] }
  have hone : f 1 = 1 := by
    ext x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp [f, map_one_eq_zero σ δ hδ]
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · simp [f, hδ, mul_apply_eq_comp, map_add]; abel
    · simp [f, mul_apply_eq_comp]
  refine ⟨AlgHom.ofLinearMap f hone hmul, ?_⟩
  change Continuous (fun a => triangularOperator (σ.1 a) (δ a))
  unfold triangularOperator diagonal
  exact (((σ.2.clm_comp_const _).const_clm_comp _).add
    ((σ.2.clm_comp_const _).const_clm_comp _)).add
    ((δ.continuous.clm_comp_const _).const_clm_comp _)

/-- A similarity of the triangular representation provides an inner
implementer for the derivation. -/
theorem inner_of_similar (σ : BoundedUnitalHom A H) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = σ.1 a * δ b + δ a * σ.1 b)
    (hsim : SimilarToStar A (Double H) (representation σ δ hδ)) :
    ∃ V : H →L[ℂ] H, ∀ a, δ a = V * σ.1 a - σ.1 a * V := by
  let π := representation σ δ hδ
  let M : ClosedSubmodule ℂ (Double H) :=
    ⟨(WithLp.sndL 2 ℂ H H).ker, (WithLp.sndL 2 ℂ H H).isClosed_ker⟩
  have hM : ∀ a x, x ∈ M → π.1 a x ∈ M := by
    intro a x hx
    change x.snd = 0 at hx
    change (triangularOperator (σ.1 a) (δ a) x).snd = 0
    simp [hx]
  rcases exists_commuting_projection π hsim M hM with ⟨P, hm, hf, hp⟩
  let q : H →L[ℂ] H := (WithLp.fstL 2 ℂ H H).comp (P.comp inr)
  have hzero (x : Double H) : (P x).snd = 0 := hm x
  have hfix (x : H) : P (inl x) = inl x := hf _ (by change (inl x).snd = 0; simp)
  have hdecomp (x : Double H) : x = inl x.fst + inr x.snd := by
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp
  have hfst (x : Double H) : (P x).fst = x.fst + q x.snd := by
    nth_rw 1 [hdecomp x]
    rw [map_add, hfix]
    simp [q]
  refine ⟨-q, ?_⟩
  intro a
  ext x
  have h := congrArg (fun T : Double H →L[ℂ] Double H => (T (inr x)).fst) (hp a).eq
  change (P (triangularOperator (σ.1 a) (δ a) (inr x))).fst =
    (triangularOperator (σ.1 a) (δ a) (P (inr x))).fst at h
  rw [hfst, triangularOperator_fst, triangularOperator_snd,
    triangularOperator_fst, hzero] at h
  have hq (x : H) : (P (inr x)).fst = q x := rfl
  rw [hq] at h
  simp only [inr_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_zero,
    zero_add, add_zero] at h
  change δ a x = (-q) (σ.1 a x) - σ.1 a ((-q) x)
  simp only [neg_apply, map_neg, sub_neg_eq_add]
  apply eq_neg_add_iff_add_eq.mpr
  simpa only [add_comm] using h

end Derivation

universe u v

/-- The similarity property of one algebra, with an independent universe for Hilbert spaces. This is property (SP) in Ozawa's formulation. -/
def AlgebraSimilarityProperty (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : BoundedUnitalHom A K), SimilarToStar A K π

/-- The bounded form of property (DP): innerness is tested in every faithful
unital star representation, independently of a bounded homomorphism under test. -/
def FaithfulStarDerivationsInner (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (σ : BoundedUnitalHom A K), (∀ a, σ.1 (star a) = star (σ.1 a)) →
    Function.Injective σ.1 → ∀ δ : A →L[ℂ] (K →L[ℂ] K),
      (∀ a b, δ (a * b) = σ.1 a * δ b + δ a * σ.1 b) →
      ∃ V : K →L[ℂ] K, ∀ a, δ a = V * σ.1 a - σ.1 a * V

/-- Kirchberg's derivation criterion (1996), as stated in Ozawa,
*An invitation to the similarity problems*,
Theorem 1.1, with boundedness supplied by Ringrose (1972), Theorem 2, p. 434.
-/
def KirchbergDerivationCriterion (A : Type u) [CStarAlgebra A] : Prop :=
  FaithfulStarDerivationsInner.{u,v} A → AlgebraSimilarityProperty.{u,v} A

/-- The elementary converse to the published Kirchberg implication, proved by
the triangular representation and its invariant first summand. -/
theorem faithfulStarDerivationsInner_of_similarity {A : Type u} [CStarAlgebra A]
    (similarity : AlgebraSimilarityProperty.{u,v} A) : FaithfulStarDerivationsInner.{u,v} A := by
  intro K _ _ _ σ _hstar _hfaithful δ hδ
  exact Derivation.inner_of_similar σ δ hδ
    (similarity (Dixmier.Triangular.Double K) (Derivation.representation σ δ hδ))

end KadisonSimilarity

end

end OAI
