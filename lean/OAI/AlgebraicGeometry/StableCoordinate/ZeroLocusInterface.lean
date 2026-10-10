import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

/-!
# Complex zero loci and ideal transport

This module supplies the geometric interface needed when an ambient polynomial
isomorphism is described on complex points.  Polynomial substitutions induce
mutually inverse polynomial maps, not arbitrary set-theoretic bijections.
Hilbert's Nullstellensatz then recovers radical defining ideals from their
complex zero loci.  No conclusion about the manuscript's polynomial is assumed.
-/

noncomputable section

namespace StableCoordinate.ZeroLocusInterface

open MvPolynomial

variable {k σ : Type*} [Field k]

/-- The map on affine points contravariantly induced by a polynomial substitution. -/
def pointMap (φ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (x : σ → k) : σ → k :=
  fun i => aeval x (φ (X i))

/-- Substitution and evaluation commute, for every polynomial. -/
theorem aeval_pointMap (φ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (x : σ → k) (p : MvPolynomial σ k) :
    aeval (pointMap φ x) p = aeval x (φ p) := by
  have h : aeval (pointMap φ x) = (aeval x).comp φ := by
    ext i
    simp [pointMap]
  exact AlgHom.congr_fun h p

@[simp]
theorem pointMap_id (x : σ → k) :
    pointMap (AlgHom.id k (MvPolynomial σ k)) x = x := by
  funext i
  simp [pointMap]

/-- Composition reverses because coordinate-ring homomorphisms are pullbacks. -/
theorem pointMap_comp (φ ψ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (x : σ → k) :
    pointMap (φ.comp ψ) x = pointMap ψ (pointMap φ x) := by
  funext i
  simp [pointMap, aeval_pointMap]

/-- A polynomial algebra automorphism induces an affine-space automorphism on
points; both directions are explicitly given by polynomial evaluation. -/
def pointEquiv (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k) :
    (σ → k) ≃ (σ → k) where
  toFun := pointMap e.toAlgHom
  invFun := pointMap e.symm.toAlgHom
  left_inv x := by
    funext i
    change aeval (pointMap e.toAlgHom x) (e.symm (X i)) = x i
    rw [aeval_pointMap]
    simp
  right_inv x := by
    funext i
    change aeval (pointMap e.symm.toAlgHom x) (e (X i)) = x i
    rw [aeval_pointMap]
    simp

@[simp]
theorem pointEquiv_apply (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (x : σ → k) : pointEquiv e x = pointMap e.toAlgHom x := rfl

/-- Pullback of a zero locus agrees with extension of its defining ideal. -/
theorem preimage_zeroLocus (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (I : Ideal (MvPolynomial σ k)) :
    (pointEquiv e) ⁻¹' zeroLocus k I = zeroLocus k (I.map e.toRingHom) := by
  ext x
  constructor
  · intro hx p hp
    obtain ⟨q, hq, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hp
    change aeval x (e.toAlgHom q) = 0
    rw [← aeval_pointMap]
    exact hx q hq
  · intro hx p hp
    change aeval (pointMap e.toAlgHom x) p = 0
    rw [aeval_pointMap]
    exact hx (e p) (Ideal.mem_map_of_mem e.toRingHom hp)

/-- The inverse point map carries a closed algebraic set to the zero locus of
its transported ideal.  This fixes the usual contravariance convention. -/
theorem image_zeroLocus (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (I : Ideal (MvPolynomial σ k)) :
    (pointEquiv e).symm '' zeroLocus k I = zeroLocus k (I.map e.toRingHom) := by
  rw [← preimage_zeroLocus]
  exact (pointEquiv e).image_symm_eq_preimage _

variable [IsAlgClosed k] [Finite σ]

/-- Over an algebraically closed field, radical ideals are determined by their
sets of rational points.  The finite-variable hypothesis is essential. -/
theorem radical_ideal_eq_of_zeroLocus_eq
    {I J : Ideal (MvPolynomial σ k)} (hI : I.IsRadical) (hJ : J.IsRadical)
    (h : zeroLocus k I = zeroLocus k J) : I = J := by
  calc
    I = vanishingIdeal k (zeroLocus k I) := by
      rw [vanishingIdeal_zeroLocus_eq_radical, hI.radical]
    _ = vanishingIdeal k (zeroLocus k J) := congrArg (vanishingIdeal k) h
    _ = J := by rw [vanishingIdeal_zeroLocus_eq_radical, hJ.radical]

/-- Equality of geometric images under a polynomial ambient automorphism
recovers equality of the transported radical defining ideals. -/
theorem map_ideal_eq_of_image_zeroLocus_eq
    (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    {I J : Ideal (MvPolynomial σ k)} (hI : I.IsRadical) (hJ : J.IsRadical)
    (h : (pointEquiv e).symm '' zeroLocus k I = zeroLocus k J) :
    I.map e.toRingHom = J := by
  refine radical_ideal_eq_of_zeroLocus_eq ?_ hJ ?_
  · have hm : I.map e.toRingHom = I.comap e.symm.toRingHom := by
      ext p
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
      constructor
      · rintro ⟨q, hq, rfl⟩
        simpa using hq
      · intro hp
        exact ⟨e.symm p, hp, e.apply_symm_apply p⟩
    rw [hm]
    exact hI.comap _
  · rw [← image_zeroLocus]
    exact h

/-- For prime defining ideals, image equality and ideal transport are
exactly equivalent; no extra geometric assumption is introduced. -/
theorem image_zeroLocus_eq_iff_map_eq
    (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (I J : Ideal (MvPolynomial σ k)) [I.IsPrime] [J.IsPrime] :
    (pointEquiv e).symm '' zeroLocus k I = zeroLocus k J ↔
      I.map e.toRingHom = J := by
  constructor
  · exact map_ideal_eq_of_image_zeroLocus_eq e
      (Ideal.IsPrime.isRadical inferInstance) (Ideal.IsPrime.isRadical inferInstance)
  · intro h
    rw [image_zeroLocus, h]

omit [IsAlgClosed k] [Finite σ] in
/-- The zero locus of the principal fiber ideal is exactly the named fiber,
including the parameter value zero. -/
theorem zeroLocus_fiber_ideal (p : MvPolynomial σ k) (t : k) :
    zeroLocus k (Ideal.span ({p - C t} : Set (MvPolynomial σ k))) =
      {x : σ → k | aeval x p = t} := by
  rw [zeroLocus_span]
  ext x
  simp [sub_eq_zero]

end StableCoordinate.ZeroLocusInterface

end

end OAI
