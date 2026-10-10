import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.DerivationJet

namespace OAI

namespace SiegelZeros

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
noncomputable section
namespace WeightedTorusJets.Geometry

theorem rectangularTaylorThree_augmentation {R B σ : Type*}
    [CommRing R] [Algebra ℚ R] [CommRing B] [Algebra ℚ B]
    (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) (D₁ D₂ D₃ : Derivation ℚ R R)
    (i₁ i₂ i₃ : σ) (f : R →+* B) (a : R) :
    rectangularAugmentation k hk (rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a) = f a :=
  rectangularTaylorThree_residue σ k hk D₁ D₂ D₃ i₁ i₂ i₃ f
    (rectangularAugmentation k hk).toRingHom (fun p => quotientAugmentation_mk _ _ p) a

variable {R : Type*} [CommRing R] [Algebra ℚ R]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry


variable {K : Type*} [Field K] [CharZero K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

noncomputable def torusDerivationOverRat (c : Fin 3 → Fin 4 → K) (j : Fin 3) :
    Derivation ℚ TorusCoordRing TorusCoordRing :=
  (localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
    (invariantDerivation (c j))).restrictScalars ℚ

noncomputable def localTorusDerivationOverRat (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (j : Fin 3) :
    Derivation ℚ (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) :=
  localizeDerivation q.asIdeal.primeCompl (torusDerivationOverRat c j)

theorem torusDerivationOverRat_commute (c : Fin 3 → Fin 4 → K) (i j : Fin 3) :
    Function.Commute (torusDerivationOverRat c i) (torusDerivationOverRat c j) := by
  simpa only [torusDerivationOverRat, Derivation.coe_restrictScalars] using
    localizeDerivation_commute (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
      (invariantDerivation (c i)) (invariantDerivation (c j))
      (invariantDerivation_commute (c i) (c j))

theorem localTorusDerivationOverRat_commute (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (i j : Fin 3) :
    Function.Commute (localTorusDerivationOverRat c q i) (localTorusDerivationOverRat c q j) :=
  localizeDerivation_commute q.asIdeal.primeCompl
    (torusDerivationOverRat c i) (torusDerivationOverRat c j)
    (torusDerivationOverRat_commute c i j)

theorem torus_derivationJet_eq (c : Fin 3 → Fin 4 → K) (a : Fin 3 → ℕ) (F : PolyRing) :
    derivationJet (torusDerivationOverRat c) a (algebraMap PolyRing TorusCoordRing F) =
      algebraMap PolyRing TorusCoordRing (invariantJet c a F) := by
  simpa only [derivationJet, torusDerivationOverRat, Module.End.pow_apply,
    Derivation.coeFn_coe, Derivation.coe_restrictScalars] using
      torus_mixed_derivatives_algebraMap c a F

theorem torus_derivativeStageIdeal_eq (c : Fin 3 → Fin 4 → K)
    (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing) :
    derivativeStageIdeal (torusDerivationOverRat c) t b (algebraMap PolyRing TorusCoordRing F) =
      rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b := by
  simp only [derivativeStageIdeal, rectangleJetIdeal, torus_derivationJet_eq]

theorem local_torus_derivativeStageIdeal_eq (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing) :
    Ideal.map (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal))
      (rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b) =
    derivativeStageIdeal (localTorusDerivationOverRat c q) t b
      (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
        (algebraMap PolyRing TorusCoordRing F)) := by
  rw [← torus_derivativeStageIdeal_eq]
  apply derivativeStageIdeal_map
  intro j f
  exact (localizeDerivation_algebraMap q.asIdeal.primeCompl (torusDerivationOverRat c j) f).symm

theorem local_torus_stage_le_maximal (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing)
    (hq : rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b ≤ q.asIdeal) :
    derivativeStageIdeal (localTorusDerivationOverRat c q) t b
      (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
        (algebraMap PolyRing TorusCoordRing F)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
  rw [← local_torus_derivativeStageIdeal_eq]
  exact (Ideal.map_mono hq).trans_eq
    (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (Localization.AtPrime q.asIdeal))

theorem local_torus_stage_primary_data (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing)
    (hq : (rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b).IsMinimalPrime q.asIdeal) :
    let J := derivativeStageIdeal (localTorusDerivationOverRat c q) t b
      (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
        (algebraMap PolyRing TorusCoordRing F))
    J.radical = IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ∧ J.IsPrimary ∧
      ∃ n : ℕ, IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n ≤ J := by
  dsimp only
  rw [← local_torus_derivativeStageIdeal_eq]
  exact ⟨component_local_radical _ q.asIdeal hq, component_local_primary _ q.asIdeal hq,
    component_local_contains_maximal_pow _ q.asIdeal hq⟩


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

section ScalarCompatibility

variable {K S L : Type*} [CommRing K] [Algebra ℚ K]
  [CommRing S] [Algebra K S] [Algebra ℚ S] [IsScalarTower ℚ K S]
  [CommRing L] [Algebra K L] [Algebra ℚ L] [IsScalarTower ℚ K L]
  [Algebra S L] [IsScalarTower K S L] [IsScalarTower ℚ S L]

theorem derivationCotangentResidue_restrictScalars (D : Derivation K S S) (I : Ideal S) :
    derivationCotangentResidue (D.restrictScalars ℚ) I = derivationCotangentResidue D I := by
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rfl

end ScalarCompatibility


attribute [local instance] Ideal.Quotient.field

variable {K : Type*} [Field K] [CharZero K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

theorem localTorusDerivationOverRat_eq_direct (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (M : Submonoid PolyRing)
    [IsLocalization M (Localization.AtPrime q.asIdeal)] (j : Fin 3) :
    localTorusDerivationOverRat c q j =
      (localizeDerivation (T := Localization.AtPrime q.asIdeal) M
        (invariantDerivation (c j))).restrictScalars ℚ := by
  apply localization_derivation_ext M
  intro F
  rw [IsScalarTower.algebraMap_apply PolyRing TorusCoordRing (Localization.AtPrime q.asIdeal)]
  simp only [localTorusDerivationOverRat, localizeDerivation_algebraMap,
    torusDerivationOverRat, Derivation.coe_restrictScalars]
  rw [← IsScalarTower.algebraMap_apply PolyRing TorusCoordRing (Localization.AtPrime q.asIdeal),
    ← IsScalarTower.algebraMap_apply PolyRing TorusCoordRing (Localization.AtPrime q.asIdeal),
    localizeDerivation_algebraMap]

theorem localTorusDerivationOverRat_cotangent_eq_direct (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (M : Submonoid PolyRing)
    [IsLocalization M (Localization.AtPrime q.asIdeal)] (j : Fin 3) :
    derivationCotangentResidue (localTorusDerivationOverRat c q j)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) =
    derivationCotangentResidue
      (localizeDerivation (T := Localization.AtPrime q.asIdeal) M (invariantDerivation (c j)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) := by
  rw [localTorusDerivationOverRat_eq_direct c q M j, derivationCotangentResidue_restrictScalars]


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem derivationJet_selected_one (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i : I) (hi : ∀ j : I, j = i) (α : I → ℕ) (F : R) :
    ((D i).toLinearMap ^ α i) F =
      derivationJet D (Function.extend (Subtype.val : I → Fin 3) α 0) F := by
  classical
  have hα : α = Pi.single i (α i) := by
    funext j
    rw [hi j]
    simp
  rw [hα, extend_selectedIndex_single]
  simpa using derivationJet_shift D h01 h02 h12 i (α i) (0 : Fin 3 → ℕ) F

theorem derivationJet_selected_two (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j : I) (hij : i ≠ j)
    (hcover : ∀ u : I, u = i ∨ u = j) (α : I → ℕ) (F : R) :
    ((D i).toLinearMap ^ α i) (((D j).toLinearMap ^ α j) F) =
      derivationJet D (Function.extend (Subtype.val : I → Fin 3) α 0) F := by
  classical
  have hα : α = Pi.single j (α j) + Pi.single i (α i) := by
    funext u
    rcases hcover u with rfl | rfl <;> simp [hij, hij.symm]
  conv_lhs => rw [← derivationJet_zero D F]
  rw [derivationJet_shift D h01 h02 h12, derivationJet_shift D h01 h02 h12]
  have he : Function.extend (Subtype.val : I → Fin 3) α 0 =
      Pi.single (j : Fin 3) (α j) + Pi.single (i : Fin 3) (α i) := by
    conv_lhs => rw [hα]
    calc
      _ = Function.extend (Subtype.val : I → Fin 3) (Pi.single j (α j)) 0 +
          Function.extend (Subtype.val : I → Fin 3) (Pi.single i (α i)) 0 :=
        Function.extend_add (Subtype.val : I → Fin 3) _ _ 0 0
      _ = _ := by rw [extend_selectedIndex_single, extend_selectedIndex_single]
  rw [he, zero_add]

theorem derivationJet_selected_three (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcover : ∀ u : I, u = i ∨ u = j ∨ u = k) (α : I → ℕ) (F : R) :
    ((D i).toLinearMap ^ α i) (((D j).toLinearMap ^ α j) (((D k).toLinearMap ^ α k) F)) =
      derivationJet D (Function.extend (Subtype.val : I → Fin 3) α 0) F := by
  classical
  have hα : α = (Pi.single k (α k) + Pi.single j (α j)) + Pi.single i (α i) := by
    funext u
    rcases hcover u with rfl | rfl | rfl <;> simp [hij, hij.symm, hik, hik.symm, hjk, hjk.symm]
  conv_lhs => rw [← derivationJet_zero D F]
  rw [derivationJet_shift D h01 h02 h12, derivationJet_shift D h01 h02 h12,
    derivationJet_shift D h01 h02 h12]
  have he : Function.extend (Subtype.val : I → Fin 3) α 0 =
      (Pi.single (k : Fin 3) (α k) + Pi.single (j : Fin 3) (α j)) +
        Pi.single (i : Fin 3) (α i) := by
    conv_lhs => rw [hα]
    calc
      _ = Function.extend (Subtype.val : I → Fin 3) (Pi.single k (α k) + Pi.single j (α j)) 0 +
          Function.extend (Subtype.val : I → Fin 3) (Pi.single i (α i)) 0 :=
        Function.extend_add (Subtype.val : I → Fin 3) _ _ 0 0
      _ = (Function.extend (Subtype.val : I → Fin 3) (Pi.single k (α k)) 0 +
          Function.extend (Subtype.val : I → Fin 3) (Pi.single j (α j)) 0) +
          Function.extend (Subtype.val : I → Fin 3) (Pi.single i (α i)) 0 := by
        congr 1
        exact Function.extend_add (Subtype.val : I → Fin 3) _ _ 0 0
      _ = _ := by rw [extend_selectedIndex_single, extend_selectedIndex_single,
        extend_selectedIndex_single]
  rw [he, zero_add]

end WeightedTorusJets.Geometry

open scoped TensorProduct


open scoped TensorProduct







open Module




open scoped BigOperators







namespace WeightedTorusJets.Geometry


variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct





variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "TorusCoordRing" => Localization.Away
  (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))


end WeightedTorusJets.Geometry

end
end




open scoped BigOperators


open Module


open MvPolynomial


end SiegelZeros

end OAI
