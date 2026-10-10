import OAI.Analysis.KadisonKastler.CornerUnitary

namespace OAI

/-! # Restriction to a reducing subspace and finite coefficients

The restriction of a star algebra to a closed invariant subspace is an
actual star homomorphism. Extending a corner unitary by the identity
preserves the coefficients of its conjugation on that subspace.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (K : Submodule ℂ H) [CompleteSpace K]

omit [CompleteSpace H] in
theorem cornerCompression_coe_of_invariant (T : H →L[ℂ] H)
    (hT : ∀ x ∈ K, T x ∈ K) (x : K) :
    (cornerCompression K T x : H) = T x := by
  change K.starProjection (T x) = T x
  exact Submodule.starProjection_eq_self_iff.mpr (hT x x.property)

omit [CompleteSpace H] in
theorem cornerCompression_mul_of_invariant (T S : H →L[ℂ] H)
    (hS : ∀ x ∈ K, S x ∈ K) :
    cornerCompression K (T * S) = cornerCompression K T * cornerCompression K S := by
  apply ContinuousLinearMap.ext
  intro x
  change K.orthogonalProjectionOnto (T (S x)) =
    K.orthogonalProjectionOnto (T (cornerCompression K S x : H))
  rw [cornerCompression_coe_of_invariant K S hS x]

theorem cornerCompression_star (T : H →L[ℂ] H) :
    cornerCompression K (star T) = star (cornerCompression K T) := by
  simp only [cornerCompression, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc]

/-- Restriction to a closed subspace invariant under the given star algebra. -/
def reducingRestriction (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) :
    A →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun a := cornerCompression K a.val
  map_zero' := map_zero (cornerCompression K)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    change K.orthogonalProjectionOnto (x : H) = x
    exact K.orthogonalProjectionOnto_mem_subspace_eq_self x
  map_add' a b := map_add (cornerCompression K) a.val b.val
  map_mul' a b := cornerCompression_mul_of_invariant K a.val b.val (hA b)
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    change K.orthogonalProjectionOnto (c • (x : H)) = c • x
    rw [map_smul, K.orthogonalProjectionOnto_mem_subspace_eq_self]
  map_star' a := cornerCompression_star K a.val

@[simp] theorem reducingRestriction_coe_apply (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
    (a : A) (x : K) :
    (reducingRestriction K A hA a x : H) = (a : H →L[ℂ] H) x :=
  cornerCompression_coe_of_invariant K a.val (hA a) x

theorem star_cornerUnitary_coe (v : unitary (K →L[ℂ] K)) :
    star (cornerUnitary K v : H →L[ℂ] H) =
      (cornerUnitary K (star v) : H →L[ℂ] H) := by
  have hp : star K.starProjection = K.starProjection := by
    rw [← cornerExtension_one K, ← cornerExtension_star K]
    exact congrArg (cornerExtension K) (star_one (R := K →L[ℂ] K))
  simp only [coe_cornerUnitary, star_add, star_sub, star_one,
    ← cornerExtension_star, Unitary.coe_star, hp]

/-- On the reducing subspace, the extended unitary gives exactly the
conjugation of the restricted operator. -/
theorem unitaryConj_cornerUnitary_apply (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
    (v : unitary (K →L[ℂ] K)) (a : A) (x : K) :
    unitaryConj (cornerUnitary K v) a.val (x : H) =
      (unitaryConj v (reducingRestriction K A hA a) x : H) := by
  simp only [unitaryConj, mul_apply_eq_comp, star_cornerUnitary_coe, Unitary.coe_star,
    cornerUnitary_apply]
  rw [← reducingRestriction_coe_apply K A hA a
    ((star (v : K →L[ℂ] K)) x), cornerUnitary_apply]

/-- Coefficients on the reducing space are unchanged when its unitary is
extended by the identity on the orthogonal complement. -/
theorem inner_unitaryConj_cornerUnitary (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
    (v : unitary (K →L[ℂ] K)) (a : A) (x y : K) :
    inner ℂ (y : H) (unitaryConj (cornerUnitary K v) a.val (x : H)) =
      inner ℂ y (unitaryConj v (reducingRestriction K A hA a) x) := by
  rw [unitaryConj_cornerUnitary_apply]
  rfl

end

end KadisonKastler

end OAI
