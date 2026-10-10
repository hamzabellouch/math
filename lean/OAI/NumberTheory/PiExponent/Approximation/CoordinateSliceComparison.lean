import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis
import OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv

namespace OAI

noncomputable section
namespace PiExponent.CoordinateSliceComparison

open PiExponentJets.PolynomialLocalResidueResolution
open CoordinateFiniteSlice

variable {K ι : Type*} [Field K] [Fintype ι]

abbrev primeLength {R : Type*} [CommRing R] (Q : Ideal R) [Q.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))

omit [Fintype ι] in
theorem splitBasis (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val)) :
    IsTranscendenceBasis K
      (splitResidueBeta K (Fin A.card) {i // i ∉ A} (splitPrime Q A)) :=
  complementary_transcendenceBasis Q A hB

omit [Fintype ι] in
theorem map_residueSlice_eq_enumeratedSliceMap
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (MvPolynomial.map (residueEquiv Q A).symm.toRingHom).comp
      ((CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)).comp
        (coordinateRenaming (K := K) A).toRingHom) =
      (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [CoordinateSliceLength.residueSlice, coordinateRenaming,
      WeightedSliceDegree.enumeratedSliceMap, WeightedSliceDegree.sliceMap,
      MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
  · intro i
    obtain ⟨j, rfl⟩ := (coordinateEquiv A).surjective i
    cases j with
    | inl j =>
      simp [RingHom.comp_apply, CoordinateSliceLength.residueSlice]
    | inr j =>
      change MvPolynomial.map (residueEquiv Q A).symm.toRingHom
        (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)
          (coordinateRenaming (K := K) A (MvPolynomial.X j.val))) =
        WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (MvPolynomial.X j.val)
      rw [coordinateRenaming_X_inr]
      rw [show CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)
          (MvPolynomial.X (Sum.inr j)) =
          MvPolynomial.C (splitResidueBeta K (Fin A.card) {i // i ∉ A} (splitPrime Q A) j) by
        simp [CoordinateSliceLength.residueSlice]]
      rw [MvPolynomial.map_C, enumeratedSliceMap_X_inr]
      exact congrArg MvPolynomial.C (residueEquiv_symm_coordinate_inr Q A j)

omit [Fintype ι] in
theorem map_splitPoint_eq (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (fun i => (residueEquiv Q A).symm.toRingEquiv
      (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A) i)) =
      slicePoint Q A := by
  funext i
  exact residueEquiv_symm_coordinate_inl Q A i

omit [Fintype ι] in
theorem map_slice_ideal (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A))).map
      (MvPolynomial.map (residueEquiv Q A).symm.toRingHom) =
    I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  exact map_residueSlice_eq_enumeratedSliceMap Q A

theorem length_eq_enumeratedSlice [CharZero K]
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val)) :
    primeLength Q I = primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom) := by
  have h₁ := PiExponentJets.W22.localized_quotient_length_eq_of_ringEquiv
    (coordinateRenaming (K := K) A).toRingEquiv Q (splitPrime Q A)
    (PiExponentSiegel.W23.atPrimeImage_comap (coordinateRenaming (K := K) A).toRingEquiv Q) I
  have h₂ := CoordinateSliceLength.length_eq_residueSlice K (Fin A.card) {i // i ∉ A}
    (splitPrime Q A) (splitBasis Q A hB) (I.map (coordinateRenaming (K := K) A).toRingHom)
  have h₃ := PointLengthEquiv.pointLocal_quotient_length (residueEquiv Q A).symm.toRingEquiv
    (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A))
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)))
  rw [map_slice_ideal, map_splitPoint_eq] at h₃
  exact h₁.trans (h₂.trans h₃)

theorem slicePoint_mem_minimalPrimes
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val))
    (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom).minimalPrimes := by
  have h₁ := splitPrime_mem_minimalPrimes Q I A hQ
  have h₂ := CoordinateSliceLength.slicePoint_mem_minimalPrimes K (Fin A.card) {i // i ∉ A}
    (splitPrime Q A) (splitBasis Q A hB) (I.map (coordinateRenaming (K := K) A).toRingHom) h₁
  have h₃ := PointLengthEquiv.point_mem_minimalPrimes_map (residueEquiv Q A).symm.toRingEquiv
    (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A))
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A))) h₂
  rw [map_slice_ideal, map_splitPoint_eq] at h₃
  exact h₃

theorem length_eq_enumeratedSlice_of_normalBasis [CharZero K]
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A) :
    primeLength Q I = primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom) :=
  length_eq_enumeratedSlice Q I A
    (idealResidueNormalBasis_complement_isTranscendenceBasis Q A hA)

theorem slicePoint_mem_minimalPrimes_of_normalBasis [CharZero K]
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom).minimalPrimes :=
  slicePoint_mem_minimalPrimes Q I A
    (idealResidueNormalBasis_complement_isTranscendenceBasis Q A hA) hQ

omit [Fintype ι] in
theorem map_span_sliceFamily
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    {J : Type*} (f : J → MvPolynomial ι K) :
    (Ideal.span (Set.range f)).map
      (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom =
    Ideal.span (Set.range (fun j =>
      WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem length_eq_sliceFamily_of_normalBasis [CharZero K]
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    {J : Type*} (f : J → MvPolynomial ι K) :
    primeLength Q (Ideal.span (Set.range f)) =
      primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
        (Ideal.span (Set.range (fun j =>
          WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j)))) := by
  have h := length_eq_enumeratedSlice_of_normalBasis Q (Ideal.span (Set.range f)) A hA
  rw [map_span_sliceFamily] at h
  exact h

theorem sliceFamily_mem_minimalPrimes_of_normalBasis [CharZero K]
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    {J : Type*} (f : J → MvPolynomial ι K)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (Ideal.span (Set.range (fun j =>
        WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j)))).minimalPrimes := by
  have h := slicePoint_mem_minimalPrimes_of_normalBasis Q (Ideal.span (Set.range f)) A hA hQ
  rw [map_span_sliceFamily] at h
  exact h

end PiExponent.CoordinateSliceComparison

end

end OAI
