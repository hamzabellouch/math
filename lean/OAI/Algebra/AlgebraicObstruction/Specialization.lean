import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.CoefficientData

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Specialization
open PrimeSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [Algebra.FiniteType ℤ R]

theorem spectrum_contains_basic_open :
    ∃ N : ℤ, N ≠ 0 ∧ (basicOpen N : Set (PrimeSpectrum ℤ)) ⊆
      Set.range (comap (algebraMap ℤ R)) := by
  have : Algebra.FinitePresentation ℤ R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Flat ℤ R := inferInstance
  have hopen : IsOpen (Set.range (comap (algebraMap ℤ R))) := by
    simpa only [Set.image_univ] using
      (isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := ℤ) (S := R))
        Set.univ isOpen_univ
  let z : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩
  have hz : z ∈ Set.range (comap (algebraMap ℤ R)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    ext a
    simp only [comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot]
    exact Int.cast_eq_zero
  obtain ⟨U, hU, hzU, hUsub⟩ := isBasis_basic_opens.exists_subset_of_mem_open hz hopen
  obtain ⟨U', ⟨N, rfl⟩, rfl⟩ := hU
  refine ⟨N, ?_, hUsub⟩
  change N ≠ 0 at hzU
  exact hzU

theorem finite_residue_fields_away :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ N →
      ∃ I : Ideal R, I.IsMaximal ∧ (p : R) ∈ I ∧ Finite (R ⧸ I) := by
  obtain ⟨N,hN,hopen⟩ := spectrum_contains_basic_open R
  refine ⟨N,hN,?_⟩
  intro p hp hpN
  let : Fact p.Prime := ⟨hp⟩
  let z : PrimeSpectrum ℤ := comap (Int.castRingHom (ZMod p)) ⟨⊥, Ideal.isPrime_bot⟩
  have hz : z ∈ (basicOpen N : Set (PrimeSpectrum ℤ)) := by
    change ¬ (N : ZMod p) ∈ (⊥ : Ideal (ZMod p))
    simpa only [Ideal.mem_bot, ZMod.intCast_zmod_eq_zero_iff_dvd] using hpN
  obtain ⟨P,hP⟩ := hopen hz
  have hpP : (p : R) ∈ P.asIdeal := by
    have h := congrArg PrimeSpectrum.asIdeal hP
    have hzmem : (p : ℤ) ∈ z.asIdeal := by
      change ((p : ℤ) : ZMod p) ∈ (⊥ : Ideal (ZMod p))
      simp only [Ideal.mem_bot, Int.cast_natCast, CharP.cast_eq_zero]
    rw [← h] at hzmem
    change algebraMap ℤ R (p : ℤ) ∈ P.asIdeal at hzmem
    simpa only [map_natCast, Int.cast_natCast] using hzmem
  obtain ⟨I,hI,hPI⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  have : I.IsMaximal := hI
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  have hpI : (p : R) ∈ I := hPI hpP
  have : CharP (R ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hpI)
  let : Algebra (ZMod p) (R ⧸ I) := ZMod.algebra (R ⧸ I) p
  have : Algebra.FiniteType (ZMod p) (R ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) (R ⧸ I)
  have : Module.Finite (ZMod p) (R ⧸ I) :=
    finite_of_finite_type_of_isJacobsonRing (ZMod p) (R ⧸ I)
  exact ⟨I,hI,hpI, Module.finite_of_finite (ZMod p)⟩

universe u

structure Reduction (R : Type u) [CommRing R] (p : ℕ) where
  K : Type u
  [field : Field K]
  [finite : Finite K]
  [characteristic : CharP K p]
  hom : R →+* K

theorem finite_field_reduction :
    ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p → Nonempty (Reduction R p) := by
  obtain ⟨N,hN,h⟩ := finite_residue_fields_away R
  refine ⟨N.natAbs,?_⟩
  intro p hp hpB
  have hpN : ¬ (p : ℤ) ∣ N := by
    intro hd
    have hh := Int.natAbs_le_of_dvd_ne_zero hd hN
    simp only [Int.natAbs_natCast] at hh
    omega
  obtain ⟨I,hI,hpI,hfin⟩ := h p hp hpN
  let : I.IsMaximal := hI
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let : Finite (R ⧸ I) := hfin
  let : CharP (R ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hpI)
  exact ⟨{ K := R ⧸ I, hom := Ideal.Quotient.mk I }⟩

end BoundaryOnly.FormalObstruction.Specialization

namespace BoundaryOnly.FormalObstruction.CoefficientRing

theorem no_integral_formal_data (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] (d : ℕ) (hd : 5 ≤ d) (n : Fin d → ℕ) :
    ¬ Nonempty (FormalData (k := R) n) := by
  rintro ⟨D⟩
  obtain ⟨B,hB⟩ := Specialization.finite_field_reduction R
  obtain ⟨p,hpB,hp⟩ := Nat.exists_infinite_primes (max B 2 + 1)
  obtain ⟨r⟩ := hB p hp (by omega)
  let : Field r.K := r.field
  let : CharP r.K p := r.characteristic
  exact BoundaryOnly.FormalObstruction.no_formal_data r.K p hp (by omega) d hd n
    ⟨(D.map r.hom).toField⟩
end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
