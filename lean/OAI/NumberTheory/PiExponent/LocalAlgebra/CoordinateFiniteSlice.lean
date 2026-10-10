import Mathlib
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv

namespace OAI

noncomputable section
namespace PiExponent.CoordinateFiniteSlice

open PiExponentJets.PolynomialLocalResidueResolution

variable {K ι : Type*} [Field K]

def coordinateEquiv (A : Finset ι) :
    Fin A.card ⊕ {i // i ∉ A} ≃ ι := by
  classical
  exact (Equiv.sumCongr A.equivFin.symm (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ A))

@[simp] theorem coordinateEquiv_inl (A : Finset ι) (i : Fin A.card) :
    coordinateEquiv A (Sum.inl i) = (A.equivFin.symm i).val := rfl

@[simp] theorem coordinateEquiv_inr (A : Finset ι) (i : {i // i ∉ A}) :
    coordinateEquiv A (Sum.inr i) = i.val := rfl

def coordinateRenaming (A : Finset ι) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K :=
  MvPolynomial.renameEquiv K (coordinateEquiv A).symm

@[simp] theorem coordinateRenaming_X_inl (A : Finset ι) (i : Fin A.card) :
    coordinateRenaming (K := K) A (MvPolynomial.X (A.equivFin.symm i).val) =
      MvPolynomial.X (Sum.inl i) := by
  change MvPolynomial.rename (coordinateEquiv A).symm
    (MvPolynomial.X (coordinateEquiv A (Sum.inl i))) = _
  rw [MvPolynomial.rename_X, Equiv.symm_apply_apply]

@[simp] theorem coordinateRenaming_X_inr (A : Finset ι) (i : {i // i ∉ A}) :
    coordinateRenaming (K := K) A (MvPolynomial.X i.val) =
      MvPolynomial.X (Sum.inr i) := by
  change MvPolynomial.rename (coordinateEquiv A).symm
    (MvPolynomial.X (coordinateEquiv A (Sum.inr i))) = _
  rw [MvPolynomial.rename_X, Equiv.symm_apply_apply]

abbrev splitPrime (Q : Ideal (MvPolynomial ι K)) (A : Finset ι) :
    Ideal (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) :=
  Q.map (coordinateRenaming (K := K) A).toRingHom

instance splitPrime_isPrime (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (splitPrime Q A).IsPrime := Ideal.map_isPrime_of_equiv (coordinateRenaming A)

def residueEquiv (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    Q.ResidueField ≃ₐ[K] (splitPrime Q A).ResidueField :=
  primeResidueAlgEquiv (coordinateRenaming A) Q

@[simp] theorem residueEquiv_coordinate_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    residueEquiv Q A
      (algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X (A.equivFin.symm i).val)) =
    algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inl i)) := by
  simpa only [residueEquiv, splitPrime, coordinateRenaming_X_inl] using
    primeResidueAlgEquiv_algebraMap (coordinateRenaming (K := K) A) Q
      (MvPolynomial.X (A.equivFin.symm i).val)

@[simp] theorem residueEquiv_coordinate_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    residueEquiv Q A
      (algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i.val)) =
    algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i)) := by
  simpa only [residueEquiv, splitPrime, coordinateRenaming_X_inr] using
    primeResidueAlgEquiv_algebraMap (coordinateRenaming (K := K) A) Q (MvPolynomial.X i.val)

theorem complementary_transcendenceBasis
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} =>
      algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i.val))) :
    IsTranscendenceBasis K (fun i : {i // i ∉ A} =>
      algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i))) := by
  simpa only [Function.comp_def, residueEquiv_coordinate_inr] using (residueEquiv Q A).isTranscendenceBasis hB

theorem splitPrime_mem_minimalPrimes
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hQ : Q ∈ I.minimalPrimes) :
    splitPrime Q A ∈ (I.map (coordinateRenaming (K := K) A).toRingHom).minimalPrimes := by
  rw [Ideal.minimalPrimes_map_of_surjective (f := (coordinateRenaming (K := K) A).toRingHom)
    (coordinateRenaming (K := K) A).surjective]
  have hk : RingHom.ker (coordinateRenaming (K := K) A).toRingHom = ⊥ := by
    ext p
    change coordinateRenaming (K := K) A p = 0 ↔ p = 0
    exact (coordinateRenaming (K := K) A).map_eq_zero_iff
  rw [hk, sup_bot_eq]
  exact ⟨Q, hQ, rfl⟩

def residueCoordinates (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (i : ι) : Q.ResidueField :=
  algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i)

def slicePoint (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (i : Fin A.card) : Q.ResidueField := residueCoordinates Q (A.equivFin.symm i)

@[simp] theorem enumeratedSliceMap_X_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)
      (MvPolynomial.X (A.equivFin.symm i).val) = MvPolynomial.X i := by
  simp [WeightedSliceDegree.enumeratedSliceMap,
    WeightedSliceDegree.sliceMap_X_mem (C := K) A (residueCoordinates Q)
      (A.equivFin.symm i).val (A.equivFin.symm i).property]

@[simp] theorem enumeratedSliceMap_X_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)
      (MvPolynomial.X i.val) = MvPolynomial.C (residueCoordinates Q i.val) := by
  simp [WeightedSliceDegree.enumeratedSliceMap,
    WeightedSliceDegree.sliceMap_X_notMem (C := K) A (residueCoordinates Q) i.val i.property]

theorem residueEquiv_symm_coordinate_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    (residueEquiv Q A).symm
      (algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inl i))) =
      slicePoint Q A i := by
  apply (residueEquiv Q A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (residueEquiv_coordinate_inl Q A i).symm

theorem residueEquiv_symm_coordinate_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    (residueEquiv Q A).symm
      (algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i))) =
      residueCoordinates Q i.val := by
  apply (residueEquiv Q A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (residueEquiv_coordinate_inr Q A i).symm

end PiExponent.CoordinateFiniteSlice

end

end OAI
