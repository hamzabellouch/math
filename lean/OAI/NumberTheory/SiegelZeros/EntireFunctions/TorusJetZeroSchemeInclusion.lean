import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.EntireFunctions.AffineZeroScheme

namespace OAI

namespace SiegelZeros

section
section
open CategoryTheory _root_.AlgebraicGeometry
namespace WeightedTorusJets.Geometry

section TorusJetZeroSchemeNested
variable {K : Type*} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K
local notation "Torus" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : Poly))

noncomputable def torusJetZeroSchemeInclusion (c : Fin 3 → Fin 4 → K) (F : Poly)
    (t : Fin 3 → ℕ) {b d : ℕ} (hbd : b ≤ d) :
    torusJetZeroScheme c F t d ⟶ torusJetZeroScheme c F t b :=
  affineZeroSchemeInclusion _ _
    (rectangleJetIdeal_mono (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t hbd)

theorem torusJetZeroSchemeInclusion_isClosedImmersion (c : Fin 3 → Fin 4 → K) (F : Poly)
    (t : Fin 3 → ℕ) {b d : ℕ} (hbd : b ≤ d) :
    IsClosedImmersion (torusJetZeroSchemeInclusion c F t hbd) :=
  affineZeroSchemeInclusion_isClosedImmersion _ _ _

theorem torusJetZeroScheme_component_genericPoint (c : Fin 3 → Fin 4 → K) (F : Poly)
    (t : Fin 3 → ℕ) (b : ℕ) (q : PrimeSpectrum Torus)
    (hq : (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b).IsMinimalPrime
      q.asIdeal) :
    ∃ V : Set (torusJetZeroScheme c F t b),
      IsGenericPoint (affineZeroSchemePoint
        (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b) q hq.le) V ∧
      Maximal IsIrreducible V :=
  affineZeroSchemePoint_isGenericPoint_component _ q hq

end TorusJetZeroSchemeNested
end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem quotient_maximal_ideal_isNilpotent {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (J : Ideal R)
    (hJ : J.radical = IsLocalRing.maximalIdeal R) :
    IsNilpotent ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J)) := by
  apply (Ideal.fg_of_isNoetherianRing _).isNilpotent_iff_le_nilradical.mpr
  simpa only [← hJ, Ideal.map_quotient_self, nilradical, Ideal.zero_eq_bot] using
    (Ideal.map_radical_le (I := J) (Ideal.Quotient.mk J))

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

attribute [local instance] spec_stalk_isLocalRing

theorem spec_stalk_component_filtration_nilpotent {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (q : PrimeSpectrum R)
    (hq : I.IsMinimalPrime q.asIdeal) :
    IsNilpotent ((IsLocalRing.maximalIdeal
      ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q)).map
      (Ideal.Quotient.mk (I.map (algebraMap R
        ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q))))) := by
  have : IsNoetherianRing ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  exact quotient_maximal_ideal_isNilpotent _ (spec_stalk_component_radical I q hq)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

noncomputable def localizationQuotientEquivStalkQuotient {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) :
    (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))) ≃ₐ[R]
      (((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p) ⧸
        I.map (algebraMap R ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p))) := by
  refine Ideal.quotientEquivAlg _ _ (AlgebraicGeometry.StructureSheaf.stalkIso R p) ?_
  rw [Ideal.map_map]
  exact congrArg I.map (AlgebraicGeometry.StructureSheaf.stalkIso R p).toAlgHom.comp_algebraMap.symm

noncomputable def affineZeroSchemeStalkEquivAmbientQuotient {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    (affineZeroScheme I).presheaf.stalk (affineZeroSchemePoint I p hp) ≃+*
      (((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p) ⧸
        I.map (algebraMap R ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p))) :=
  (affineZeroSchemeStalkEquivAt I p hp).trans
    (localizationQuotientEquivStalkQuotient I p).toRingEquiv

theorem affineZeroSchemeStalk_length_ambientStalk {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    Module.length ((affineZeroScheme I).presheaf.stalk (affineZeroSchemePoint I p hp))
        ((affineZeroScheme I).presheaf.stalk (affineZeroSchemePoint I p hp)) =
      Module.length ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p)
        (((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p) ⧸
          I.map (algebraMap R ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p))) :=
  (ringEquiv_self_length (affineZeroSchemeStalkEquivAmbientQuotient I p hp)).trans
    (Module.length_eq_of_surjective (M :=
      ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p) ⧸
        I.map (algebraMap R ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p)))
      Ideal.Quotient.mk_surjective).symm

theorem ambient_stalk_quotient_length_eq_localization {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    Module.length ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p)
        (((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p) ⧸
          I.map (algebraMap R ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p))) =
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))) :=
  (affineZeroSchemeStalk_length_ambientStalk I p hp).symm.trans
    (affineZeroSchemeStalk_length I p hp)

end WeightedTorusJets.Geometry
end

section
namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

noncomputable def torusToPolynomialFractionRing (n : ℕ) :
    Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) →ₐ[
      MvPolynomial (Fin n) K] FractionRing (MvPolynomial (Fin n) K) :=
  Localization.mapToFractionRing (FractionRing (MvPolynomial (Fin n) K))
    (Submonoid.powers (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
    (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero i))

theorem torusToPolynomialFractionRing_algebraMap (n : ℕ) (F : MvPolynomial (Fin n) K) :
    torusToPolynomialFractionRing n (algebraMap (MvPolynomial (Fin n) K)
      (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))) F) =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) F :=
  (torusToPolynomialFractionRing n).commutes F

@[instance_reducible]
noncomputable def torusPolynomialFractionAlgebra (n : ℕ) :
    Algebra (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) :=
  (torusToPolynomialFractionRing n).toRingHom.toAlgebra

theorem torusPolynomialFractionAlgebra_data (n : ℕ) :
    let : Algebra (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := torusPolynomialFractionAlgebra n
    IsScalarTower (MvPolynomial (Fin n) K)
      (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) ∧
    IsFractionRing (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := by
  let : Algebra (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := torusPolynomialFractionAlgebra n
  have h : IsScalarTower (MvPolynomial (Fin n) K)
      (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) :=
    IsScalarTower.of_algebraMap_eq fun x => (torusToPolynomialFractionRing n).commutes x |>.symm
  exact ⟨h, IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))) _ _⟩

noncomputable def torusFractionRingEquiv (n : ℕ) :
    let : Algebra (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := torusPolynomialFractionAlgebra n
    FractionRing (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))) ≃ₐ[
      Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))]
        FractionRing (MvPolynomial (Fin n) K) := by
  let : Algebra (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := torusPolynomialFractionAlgebra n
  have := (torusPolynomialFractionAlgebra_data (K := K) n).2
  exact IsLocalization.algEquiv
    (nonZeroDivisors (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))))
    (FractionRing (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))))
    (FractionRing (MvPolynomial (Fin n) K))

noncomputable def torusFractionRingEquivOverK (n : ℕ) :
    FractionRing (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin n) K) := by
  let : Algebra (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := torusPolynomialFractionAlgebra n
  have := (torusPolynomialFractionAlgebra_data (K := K) n).1
  have : IsScalarTower K
      (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := IsScalarTower.to₁₃₄ K (MvPolynomial (Fin n) K)
        (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
        (FractionRing (MvPolynomial (Fin n) K))
  exact (torusFractionRingEquiv (K := K) n).restrictScalars K

theorem torusFractionRingEquivOverK_algebraMap (n : ℕ) (f : MvPolynomial (Fin n) K) :
    torusFractionRingEquivOverK n
      (algebraMap (MvPolynomial (Fin n) K)
        (FractionRing (Localization.Away
          (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))) f) =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) f := by
  let : Algebra (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
      (FractionRing (MvPolynomial (Fin n) K)) := torusPolynomialFractionAlgebra n
  change torusFractionRingEquiv n _ = _
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) K)
    (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))
    (FractionRing (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))),
    (torusFractionRingEquiv (K := K) n).commutes]
  exact torusToPolynomialFractionRing_algebraMap n f

end WeightedTorusJets.Geometry
end

end

end SiegelZeros

end OAI
