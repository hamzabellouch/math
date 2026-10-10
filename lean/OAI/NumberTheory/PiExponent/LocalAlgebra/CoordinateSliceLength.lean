import Mathlib
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence
import OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv

namespace OAI

noncomputable section

namespace PiExponent.CoordinateSliceLength

open PiExponentJets.PolynomialLocalResidueResolution

abbrev localizedLength {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))

theorem localizedLength_congr {R : Type*} [CommRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (h : P = Q) (I : Ideal R) :
    localizedLength P I = localizedLength Q I := by
  subst Q
  rfl

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

def rationalizePolynomial :
    MvPolynomial (α ⊕ β) K →+* MvPolynomial α (SplitCoefficientField K β) :=
  (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom.comp
    (algebraMap (MvPolynomial (α ⊕ β) K)
      (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β))

@[simp] theorem rationalizePolynomial_X_inl (i : α) :
    rationalizePolynomial K α β (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i :=
  PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inl K α β i

@[simp] theorem rationalizePolynomial_X_inr (i : β) :
    rationalizePolynomial K α β (MvPolynomial.X (Sum.inr i)) =
      MvPolynomial.C (algebraMap (MvPolynomial β K) (SplitCoefficientField K β)
        (MvPolynomial.X i)) :=
  PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inr K α β i

theorem closedPolynomialIdeal_eq_ker :
    closedPolynomialIdeal K α β Q hB =
      RingHom.ker (closedPointEvaluationRingHom K α β Q hB) := by
  unfold closedPolynomialIdeal coefficientClosedPoint
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).map
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom = _
  exact Ideal.map_comap_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective _

theorem map_prime_eq_closedPolynomialIdeal :
    Q.map (rationalizePolynomial K α β) = closedPolynomialIdeal K α β Q hB := by
  have h := extended_kernel_eq
    (PiExponentSiegelAux.W09.coefficientDenominators K α β)
    (algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q))
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)
    (closedPointEvaluation_original K α β Q hB)
  rw [Ideal.ker_algebraMap_residueField] at h
  unfold closedPolynomialIdeal coefficientClosedPoint
  rw [← h, Ideal.map_map]
  rfl

theorem closedPolynomialIdeal_comap :
    (closedPolynomialIdeal K α β Q hB).comap (rationalizePolynomial K α β) = Q := by
  rw [closedPolynomialIdeal_eq_ker]
  change RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
    (rationalizePolynomial K α β)) = Q
  rw [show (closedPointEvaluationRingHom K α β Q hB).comp
      (rationalizePolynomial K α β) =
      algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) from
    closedPointEvaluation_original K α β Q hB]
  exact Ideal.ker_algebraMap_residueField Q

theorem closedPolynomialIdeal_mem_minimalPrimes
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (hQ : Q ∈ I.minimalPrimes) :
    closedPolynomialIdeal K α β Q hB ∈
      (I.map (rationalizePolynomial K α β)).minimalPrimes := by
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rw [← map_prime_eq_closedPolynomialIdeal]
    exact Ideal.map_mono hQ.1.2
  · intro J hJ hJP
    let : J.IsPrime := hJ.1
    have hcont : Q ≤ J.comap (rationalizePolynomial K α β) := by
      apply hQ.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hJ.2⟩
      rw [← closedPolynomialIdeal_comap K α β Q hB]
      exact Ideal.comap_mono hJP
    rw [← map_prime_eq_closedPolynomialIdeal]
    exact Ideal.map_le_iff_le_comap.mpr hcont

theorem polynomialPrimeClosedPointEquiv_algebraMap
    (p : MvPolynomial (α ⊕ β) K) :
    polynomialPrimeClosedPointEquiv K α β Q hB
      (algebraMap _ (Localization.AtPrime Q) p) =
    algebraMap (MvPolynomial α (SplitCoefficientField K β)) (Localization.AtPrime (closedPolynomialIdeal K α β Q hB))
      (rationalizePolynomial K α β p) := by
  let := closedLocal_isLocalizationAtOriginal K α β Q hB
  change PiExponentSiegel.W23.atPrimeEquivOfRingEquiv _ _
    ((IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
      (CoefficientClosedLocal K α β Q hB))
      (algebraMap _ (Localization.AtPrime Q) p)) = _
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (α ⊕ β) K)
    (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
    (CoefficientClosedLocal K α β Q hB)]
  exact PiExponentSiegel.W23.atPrimeEquivOfRingEquiv_algebraMap _ _ _

theorem polynomialPrimeClosedPointEquiv_map_ideal (I : Ideal (MvPolynomial (α ⊕ β) K)) :
    (I.map (algebraMap _ (Localization.AtPrime Q))).map
      (polynomialPrimeClosedPointEquiv K α β Q hB).toRingHom =
    (I.map (rationalizePolynomial K α β)).map
      (algebraMap (MvPolynomial α (SplitCoefficientField K β)) (Localization.AtPrime (closedPolynomialIdeal K α β Q hB))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact polynomialPrimeClosedPointEquiv_algebraMap K α β Q hB p

include hB in

theorem length_eq_rationalized (I : Ideal (MvPolynomial (α ⊕ β) K)) :
    localizedLength Q I =
      localizedLength (closedPolynomialIdeal K α β Q hB)
        (I.map (rationalizePolynomial K α β)) :=
  LocalLengthTransport.localLength_eq_of_localizedIdeal_map Q
    (closedPolynomialIdeal K α β Q hB) (polynomialPrimeClosedPointEquiv K α β Q hB)
    I (I.map (rationalizePolynomial K α β))
    (polynomialPrimeClosedPointEquiv_map_ideal K α β Q hB I)

theorem splitCoefficientResidue_isScalarTower :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    IsScalarTower K (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap K (SplitResidue K α β Q) a =
    ((rationalResidueEquiv (splitLocalBeta K α β Q) hB.1
      (algebraMap K (SplitCoefficientField K β) a)) : SplitResidue K α β Q)
  rw [AlgEquiv.commutes]
  rfl

theorem splitResidue_finite [Finite α] [Finite β] :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    Module.Finite (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitCoefficientResidue_isScalarTower K α β Q hB
  let : Algebra.EssFiniteType K (SplitResidue K α β Q) :=
    Algebra.EssFiniteType.comp K (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q)
  let := Algebra.EssFiniteType.of_comp K (SplitCoefficientField K β)
    (SplitResidue K α β Q)
  let := splitResidue_algebraic K α β Q hB
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

def slicePoint (i : α) : SplitResidue K α β Q :=
  algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q)
    (MvPolynomial.X (Sum.inl i))

def residueSlice :
    MvPolynomial (α ⊕ β) K →+* MvPolynomial α (SplitResidue K α β Q) :=
  (MvPolynomial.aeval (fun i : α ⊕ β => match i with
    | Sum.inl i => MvPolynomial.X i
    | Sum.inr j => MvPolynomial.C (splitResidueBeta K α β Q j))).toRingHom

theorem map_rationalize_eq_residueSlice :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    (MvPolynomial.map (algebraMap (SplitCoefficientField K β) (SplitResidue K α β Q))).comp
      (rationalizePolynomial K α β) = residueSlice K α β Q := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitCoefficientResidue_isScalarTower K α β Q hB
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.map _ (rationalizePolynomial K α β (MvPolynomial.C a)) = _
    have hr : rationalizePolynomial K α β (MvPolynomial.C a) =
        MvPolynomial.C (algebraMap K (SplitCoefficientField K β) a) := by
      change PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
        (algebraMap K (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) a) = _
      exact (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).commutes a
    rw [hr, MvPolynomial.map_C]
    change MvPolynomial.C _ = MvPolynomial.aeval _ (MvPolynomial.C a)
    rw [MvPolynomial.aeval_C]
    exact congrArg MvPolynomial.C
      (IsScalarTower.algebraMap_apply K (SplitCoefficientField K β) (SplitResidue K α β Q) a).symm
  · intro i
    cases i with
    | inl i => simp [residueSlice]
    | inr i =>
      have hc := closedPointEvaluation_coefficient K α β Q hB (MvPolynomial.X i)
      simp only [closedPointEvaluation, MvPolynomial.aeval_C, MvPolynomial.aeval_X] at hc
      simpa [residueSlice] using congrArg (MvPolynomial.C (σ := α)) hc

theorem closedPolynomialIdeal_eq_contractedPoint :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    closedPolynomialIdeal K α β Q hB =
      SeparablePointLength.contractedPoint (K := SplitCoefficientField K β)
        (slicePoint K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  rw [closedPolynomialIdeal_eq_ker, SeparablePointLength.contractedPoint_eq_ker]
  rfl

include hB in

theorem length_eq_residueSlice [Finite α] [Finite β] [CharZero K]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap _ (Localization.AtPrime Q))) =
    Module.length (Localization.AtPrime (WeightedBezout.pointIdeal (slicePoint K α β Q)))
      (Localization.AtPrime (WeightedBezout.pointIdeal (slicePoint K α β Q)) ⧸
        (I.map (residueSlice K α β Q)).map (algebraMap _
          (Localization.AtPrime (WeightedBezout.pointIdeal (slicePoint K α β Q))))) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitResidue_finite K α β Q hB
  have hc := closedPolynomialIdeal_eq_contractedPoint K α β Q hB
  have h := length_eq_rationalized K α β Q hB I
  have hcongr := localizedLength_congr
    (closedPolynomialIdeal K α β Q hB)
    (SeparablePointLength.contractedPoint (K := SplitCoefficientField K β) (slicePoint K α β Q))
    hc (I.map (rationalizePolynomial K α β))
  have he := SeparablePointLength.pointLocal_quotient_length
    (K := SplitCoefficientField K β) (slicePoint K α β Q)
    (I.map (rationalizePolynomial K α β))
  have hi : (I.map (rationalizePolynomial K α β)).map
      (MvPolynomial.map (algebraMap (SplitCoefficientField K β) (SplitResidue K α β Q))) =
      I.map (residueSlice K α β Q) := by
    rw [Ideal.map_map, map_rationalize_eq_residueSlice K α β Q hB]
  rw [hi] at he
  exact h.trans (hcongr.trans he.symm)

include hB in

theorem slicePoint_mem_minimalPrimes [Finite α] [Finite β]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint K α β Q) ∈
      (I.map (residueSlice K α β Q)).minimalPrimes := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitResidue_finite K α β Q hB
  have h := closedPolynomialIdeal_mem_minimalPrimes K α β Q hB I hQ
  rw [closedPolynomialIdeal_eq_contractedPoint K α β Q hB] at h
  have he := SeparablePointLength.point_mem_minimalPrimes_map
    (K := SplitCoefficientField K β) (slicePoint K α β Q)
    (I.map (rationalizePolynomial K α β)) h
  rw [Ideal.map_map, map_rationalize_eq_residueSlice K α β Q hB] at he
  exact he

end PiExponent.CoordinateSliceLength

end

end OAI
