import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional
import OAI.NumberTheory.PiExponent.Jets.CompactJetIdealCoherent
import OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace PiExponent.CompactLogJetIdeal
open CompactJetPolynomial

variable {m : ℕ}

abbrev coordinateRing (m : ℕ) := MvPolynomial (Fin (m+1)) ℂ
abbrev affineSpace (m : ℕ) : Scheme := Spec (CommRingCat.of (coordinateRing m))
abbrev base : Scheme := Spec (CommRingCat.of ℂ)

def structureMap (m : ℕ) : affineSpace m ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)))

def point (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (center c)).toRingHom)

theorem point_section (c : Fin m → ℂ) : point c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (center c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (c : Fin m → ℂ) : Set.range (point c) = {centerPoint c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (center c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (center c))

theorem support_specIdeal {R : Type} [CommRing R] (I : Ideal R) :
    ((PiExponentSeshadri.IdealPullback.specIdeal I).support : Set (Spec (CommRingCat.of R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [PiExponentSeshadri.IdealPullback.specIdeal,
    Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap]
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)]

def polynomialIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal (coordinateRing m) :=
  ∏ a, powerIdeal (c a) (logPolynomials T) e

def affineIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : (affineSpace m).IdealSheafData :=
  PiExponentSeshadri.IdealPullback.specIdeal (polynomialIdeal c T e)

theorem support_affineIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal c T e).support : Set (affineSpace m)) =
      ⋃ a, Set.range (point (c a)) := by
  rw [affineIdeal, support_specIdeal]
  unfold polynomialIdeal
  rw [zeroLocus_prod_powerIdeal c (logPolynomials T) (logPolynomials_eval_zero T) e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
    exact ⟨a, (Set.mem_singleton_iff.mp ha).symm⟩

def compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) : X.IdealSheafData :=
  CompactJetIdeal.extend (affineIdeal c T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal c T e j).comap j = affineIdeal c T e :=
  CompactJetIdeal.restrict_extend _ j

theorem support_compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdeal c T e j).support : Set X) =
      ⋃ a, Set.range (point (c a) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal c T e) j π
    (fun a => point (c a)) (fun a => by
      rw [Category.assoc, hπ, point_section]) (support_affineIdeal c T e he),
    support_affineIdeal c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem compactIdeal_isFinitePresentation {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} [IsLocallyNoetherian X] (j : affineSpace m ⟶ X) :
    (PiExponentSeshadri.IdealModule.closedModule (compactIdeal c T e j)).IsFinitePresentation :=
  CompactJetIdeal.extend_isFinitePresentation _ j

theorem polynomialIdeal_pow_le {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (n : ℕ) (a : J) :
    polynomialIdeal c T e ^ n ≤ powerIdeal (c a) (logPolynomials T) e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ a))

theorem formalJet_packet_zero_of_mem_polynomialIdeal_pow {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : coordinateRing m) (hP : P ∈ polynomialIdeal c T e ^ n) (a : J) :
    JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet (c a) P) =
      (fun _ => (0 : ℂ)) :=
  formalJet_packet_zero_of_mem_pow (c a) T e v hv hT R he n P
    (polynomialIdeal_pow_le c T e n a hP)

end PiExponent.CompactLogJetIdeal
end

end OAI
