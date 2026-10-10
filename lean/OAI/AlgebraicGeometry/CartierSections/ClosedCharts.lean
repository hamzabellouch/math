/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import OAI.AlgebraicGeometry.CartierSections.ChartCompletion
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Unramified.LocalRing

namespace OAI

/-!
# Closed étale coordinate charts

Over an algebraically closed coefficient field, a closed unramified chart has no
residue extension, and its coordinate functions generate its maximal ideal.
-/

namespace CartierSections
/-- A local essentially finite type unramified chart over an algebraically closed
residue field induces an isomorphism on residue rings. -/
theorem local_unramified_base_bijective
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A]
    [IsAlgClosed (IsLocalRing.ResidueField R)] :
    Function.Bijective (quotientBaseMap (A := A) (IsLocalRing.maximalIdeal R)) := by
  let e := Ideal.quotientEquivAlgOfEq R (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := A))
  have hb : Function.Bijective (e.toAlgHom.comp
      (quotientBaseMap (A := A) (IsLocalRing.maximalIdeal R))) := by
    have he : (e.toAlgHom.comp (quotientBaseMap (A := A) (IsLocalRing.maximalIdeal R))).toRingHom =
        algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) := by
      ext a
      rfl
    change Function.Bijective (e.toAlgHom.comp
      (quotientBaseMap (A := A) (IsLocalRing.maximalIdeal R))).toRingHom
    rw [he]
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := IsLocalRing.ResidueField R) (K := IsLocalRing.ResidueField A)
  refine ⟨fun _ _ h => hb.injective (congrArg e h), ?_⟩
  intro a
  obtain ⟨r, hr⟩ := hb.surjective (e a)
  exact ⟨r, e.injective hr⟩

/-- The coordinate-origin ideal is the literal kernel of the constant
coefficient map. -/
theorem idealOfVars_eq_ker_constantCoeff {σ k : Type*} [CommRing k] :
    MvPolynomial.idealOfVars σ k = RingHom.ker (MvPolynomial.constantCoeff (σ := σ) (R := k)) := by
  ext p
  rw [← pow_one (MvPolynomial.idealOfVars σ k), MvPolynomial.mem_pow_idealOfVars_iff']
  change (∀ d : σ →₀ ℕ, Finsupp.degree d < 1 → p.coeff d = 0) ↔ p.coeff 0 = 0
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have he : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
    simpa [he] using h

noncomputable def polynomialOriginResidueEquiv {σ k : Type*} [CommRing k] :
    MvPolynomial σ k ⧸ MvPolynomial.idealOfVars σ k ≃+* k :=
  (Ideal.quotEquivOfEq (idealOfVars_eq_ker_constantCoeff (σ := σ) (k := k))).trans
    (RingHom.quotientKerEquivOfSurjective (f := MvPolynomial.constantCoeff (σ := σ) (R := k))
      (fun c => ⟨MvPolynomial.C c, MvPolynomial.constantCoeff_C σ c⟩))

@[simp] theorem polynomialOriginResidueEquiv_mk {σ k : Type*} [CommRing k]
    (p : MvPolynomial σ k) :
    polynomialOriginResidueEquiv (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ k) p) =
      MvPolynomial.constantCoeff p := rfl

theorem polynomialOrigin_isMaximal {σ k : Type*} [Field k] :
    (MvPolynomial.idealOfVars σ k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.constantCoeff_C σ c⟩)

attribute [local instance] polynomialOrigin_isMaximal

section ClosedChart
universe u
variable {σ k R A : Type u} [Field k] [CommRing R] [CommRing A]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) A]
  [Algebra R A] [IsScalarTower (MvPolynomial σ k) R A]
  [IsLocalRing R] [IsLocalRing A]
  [IsLocalization.AtPrime R (MvPolynomial.idealOfVars σ k)]
  [IsLocalHom (algebraMap R A)]
  [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A]

include R

/-- Closed étale coordinate functions generate the maximal ideal. -/
theorem closed_chart_maximalIdeal :
    (MvPolynomial.idealOfVars σ k).map (algebraMap (MvPolynomial σ k) A) =
      IsLocalRing.maximalIdeal A := by
  have := polynomialOrigin_isMaximal (σ := σ) (k := k)
  rw [IsScalarTower.algebraMap_eq (MvPolynomial σ k) R A, ← Ideal.map_map,
    IsLocalization.AtPrime.map_eq_maximalIdeal (MvPolynomial.idealOfVars σ k) R,
    Algebra.FormallyUnramified.map_maximalIdeal]

variable [IsAlgClosed k]

/-- The residue premise for the completion equivalence follows from a
closed unramified chart over the algebraically closed coefficient field. -/
theorem closed_chart_base_bijective :
    Function.Bijective (quotientBaseMap (A := A) (MvPolynomial.idealOfVars σ k)) := by
  have := polynomialOrigin_isMaximal (σ := σ) (k := k)
  let eR := IsLocalization.AtPrime.equivQuotMaximalIdeal (MvPolynomial.idealOfVars σ k) R
  let eK := (polynomialOriginResidueEquiv (σ := σ) (k := k)).symm.trans eR
  have : IsAlgClosed (IsLocalRing.ResidueField R) :=
    IsAlgClosed.of_ringEquiv k _ eK
  let eA := Ideal.quotEquivOfEq (closed_chart_maximalIdeal (R := R) (A := A) (σ := σ) (k := k))
  let eA' := Ideal.quotEquivOfEq (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := A))
  have hlocal := local_unramified_base_bijective (R := R) (A := A)
  have heq : eA.toRingHom.comp (quotientBaseMap (A := A) (MvPolynomial.idealOfVars σ k)).toRingHom =
      (eA'.toRingHom.comp (quotientBaseMap (A := A) (IsLocalRing.maximalIdeal R)).toRingHom).comp
        eR.toRingHom := by
    apply RingHom.ext
    intro v
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective v
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap (MvPolynomial σ k) A p) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (algebraMap R A (algebraMap (MvPolynomial σ k) R p))
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k) R A]
  have hb : Function.Bijective (eA.toRingHom.comp
      (quotientBaseMap (A := A) (MvPolynomial.idealOfVars σ k)).toRingHom) := by
    rw [heq]
    exact (eA'.bijective.comp hlocal).comp eR.bijective
  refine ⟨fun _ _ h => hb.injective (congrArg eA h), ?_⟩
  intro a
  obtain ⟨p, hp⟩ := hb.surjective (eA a)
  exact ⟨p, eA.injective hp⟩
end ClosedChart
end CartierSections

end OAI
