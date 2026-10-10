import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.MvPowerSeries.Derivative

namespace OAI

/-!
# Derivations on étale coordinate charts

Formally étale coordinate derivations satisfy the coordinate chain rule and commute
with expansion in multivariate power series. These are the regular differential
operators used in the logarithmic jet estimate for uniform Cartier sections.
-/

namespace CartierSections
open TensorProduct
section Etale
variable {k A T M : Type*} [CommRing k] [CommRing A] [CommRing T]
  [Algebra k A] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [Algebra.FormallyEtale A T]
  [AddCommGroup M] [Module k M] [Module A M] [Module T M]
  [IsScalarTower k A M] [IsScalarTower A T M] [IsScalarTower k T M]

noncomputable def extendEtaleDerivation (D : Derivation k A M) : Derivation k T M :=
  ((LinearMap.liftBaseChange T D.liftKaehlerDifferential).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A T).symm.toLinearMap).compDer
      (KaehlerDifferential.D k T)

@[simp] theorem extendEtaleDerivation_algebraMap (D : Derivation k A M) (a : A) :
    extendEtaleDerivation D (algebraMap A T a) = D a := by
  change (LinearMap.liftBaseChange T D.liftKaehlerDifferential)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A T).symm
      (KaehlerDifferential.D k T (algebraMap A T a))) = D a
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

/-- Formally étale coordinates determine a derivation, not only its values
on coordinate polynomials. -/
theorem etale_derivation_ext (D E : Derivation k T M)
    (h : ∀ a : A, D (algebraMap A T a) = E (algebraMap A T a)) : D = E := by
  have hh :
      D.liftKaehlerDifferential.comp
        (KaehlerDifferential.mapBaseChange k A T) =
      E.liftKaehlerDifferential.comp
        (KaehlerDifferential.mapBaseChange k A T) := by
    ext a
    change D.liftKaehlerDifferential
        (KaehlerDifferential.mapBaseChange k A T (1 ⊗ₜ KaehlerDifferential.D k A a)) =
      E.liftKaehlerDifferential
        (KaehlerDifferential.mapBaseChange k A T (1 ⊗ₜ KaehlerDifferential.D k A a))
    simpa using h a
  have hlin : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ :=
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A T).surjective z
    exact LinearMap.congr_fun hh z
  ext t
  rw [← Derivation.liftKaehlerDifferential_comp_D D t, hlin]
  simp

end Etale

@[simp] theorem derivation_sum_apply {k T M ι : Type*} [CommRing k] [CommRing T]
    [Algebra k T] [AddCommGroup M] [Module k M] [Module T M]
    [IsScalarTower k T M] (s : Finset ι) (D : ι → Derivation k T M) (a : T) :
    (∑ i ∈ s, D i) a = ∑ i ∈ s, D i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert, hi, ih]

section Coordinates
variable {k T ι : Type*} [CommRing k] [CommRing T]
  [Algebra k T] [Algebra (MvPolynomial ι k) T]
  [IsScalarTower k (MvPolynomial ι k) T]
  [Algebra.FormallyEtale (MvPolynomial ι k) T]

/-- The partial derivatives on a formally étale coordinate chart, obtained
from the cotangent-space base-change isomorphism. -/
noncomputable def etalePartial (i : ι) : Derivation k T T :=
  extendEtaleDerivation
    ((Algebra.linearMap (MvPolynomial ι k) T).compDer (MvPolynomial.pderiv i))

@[simp] theorem etalePartial_coordinate [DecidableEq ι] (i j : ι) :
    etalePartial (k := k) (T := T) i
      (algebraMap (MvPolynomial ι k) T (MvPolynomial.X j)) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j; simp [etalePartial, MvPolynomial.pderiv_X]
  · simp [etalePartial, MvPolynomial.pderiv_X, h]

/-- The ordinary chain rule holds for all functions on the étale chart,
not just for coordinate polynomials. -/
theorem etale_coordinate_chain_rule [Fintype ι] (D : Derivation k T T) (f : T) :
    D f = ∑ i : ι, D (algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)) *
        etalePartial (k := k) (T := T) i f := by
  classical
  let E : Derivation k T T := ∑ i : ι,
    D (algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)) • etalePartial i
  have hpoly : D.compAlgebraMap (MvPolynomial ι k) = E.compAlgebraMap (MvPolynomial ι k) := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [E, Derivation.compAlgebraMap_apply,
      Derivation.smul_apply, etalePartial_coordinate]
  have heq : D = E := etale_derivation_ext D E (fun a => Derivation.congr_fun hpoly a)
  simpa [E, derivation_sum_apply, Derivation.smul_apply] using Derivation.congr_fun heq f

/-- Coordinate chain rule with values in an algebra over the coordinate chart.
This is the form needed after pullback to the DVR of a divisor on a model. -/
theorem etale_coordinate_chain_rule_to [Fintype ι] {R : Type*} [CommRing R]
    [Algebra k R] [Algebra T R] [IsScalarTower k T R]
    (D : Derivation k T R) (f : T) :
    D f = ∑ i : ι, D (algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)) *
        algebraMap T R (etalePartial (k := k) (T := T) i f) := by
  classical
  let : Algebra (MvPolynomial ι k) R :=
    ((algebraMap T R).comp (algebraMap (MvPolynomial ι k) T)).toAlgebra
  let : IsScalarTower (MvPolynomial ι k) T R := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k (MvPolynomial ι k) R :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq k T R, IsScalarTower.algebraMap_eq k (MvPolynomial ι k) T]
      rfl)
  let E : Derivation k T R := ∑ i : ι,
    D (algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)) •
      (Algebra.linearMap T R).compDer (etalePartial i)
  have hpoly : D.compAlgebraMap (MvPolynomial ι k) = E.compAlgebraMap (MvPolynomial ι k) := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [E, Derivation.compAlgebraMap_apply,
      Derivation.smul_apply, etalePartial_coordinate]
  have heq : D = E := etale_derivation_ext D E (fun a => Derivation.congr_fun hpoly a)
  simpa [E, derivation_sum_apply, Derivation.smul_apply] using Derivation.congr_fun heq f

end Coordinates
end CartierSections


namespace CartierSections
/-- The coordinate derivatives commute with formal expansion by formal unramifiedness. -/
theorem etalePartial_series_natural
    {k T ι : Type*} [Field k] [CommRing T]
    [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T]
    [Algebra.FormallyEtale (MvPolynomial ι k) T]
    (θ : T →ₐ[k] MvPowerSeries ι k)
    (hz : ∀ i, θ (algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)) = MvPowerSeries.X i)
    (i : ι) (f : T) :
    θ (etalePartial (k := k) (T := T) i f) = MvPowerSeries.pderiv (R := k) i (θ f) := by
  classical
  let : Algebra T (MvPowerSeries ι k) := θ.toRingHom.toAlgebra
  have : IsScalarTower k T (MvPowerSeries ι k) := IsScalarTower.of_algHom θ
  have hpoly : θ.comp (IsScalarTower.toAlgHom k (MvPolynomial ι k) T) =
      MvPolynomial.coeToMvPowerSeries.algHom k := by
    apply MvPolynomial.algHom_ext
    simpa using hz
  have : IsScalarTower (MvPolynomial ι k) T (MvPowerSeries ι k) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro p
      exact (AlgHom.congr_fun hpoly p).symm)
  let D : Derivation k T (MvPowerSeries ι k) :=
    (Algebra.linearMap T (MvPowerSeries ι k)).compDer (etalePartial (k := k) (T := T) i)
  let E : Derivation k T (MvPowerSeries ι k) :=
    (MvPowerSeries.pderiv (R := k) i).compAlgebraMap T
  have heq : D = E := by
    apply etale_derivation_ext (A := MvPolynomial ι k) D E
    have hD : D.compAlgebraMap (MvPolynomial ι k) = E.compAlgebraMap (MvPolynomial ι k) := by
      apply MvPolynomial.derivation_ext
      intro j
      change θ (etalePartial (k := k) (T := T) i (algebraMap (MvPolynomial ι k) T (MvPolynomial.X j))) =
        MvPowerSeries.pderiv (R := k) i (θ (algebraMap (MvPolynomial ι k) T (MvPolynomial.X j)))
      rw [etalePartial_coordinate, hz j]
      by_cases h : i = j
      · subst j; simp
      · simp [h, Ne.symm h]
    intro p
    exact Derivation.congr_fun hD p
  exact Derivation.congr_fun heq f
end CartierSections

end OAI
