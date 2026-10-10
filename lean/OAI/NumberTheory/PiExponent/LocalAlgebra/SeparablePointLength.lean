import Mathlib
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout

namespace OAI

namespace PiExponent.SeparablePointLength

open IsLocalRing TensorProduct

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def coefficientBaseChangeEquiv :
    (MvPolynomial ι K) ⊗[K] E ≃ₐ[MvPolynomial ι K] MvPolynomial ι E :=
  Algebra.IsPushout.equiv K (MvPolynomial ι K) E (MvPolynomial ι E)

theorem coefficientExtension_flat :
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι E) :=
  Module.Flat.of_linearEquiv (coefficientBaseChangeEquiv (K := K) (E := E) (ι := ι)).symm.toLinearEquiv

theorem coefficientExtension_finite [Module.Finite K E] :
    Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) :=
  Module.Finite.equiv (coefficientBaseChangeEquiv (K := K) (E := E) (ι := ι)).toLinearEquiv

theorem coefficientExtension_unramified [Algebra.IsSeparable K E] :
    Algebra.FormallyUnramified (MvPolynomial ι K) (MvPolynomial ι E) := by
  let : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  exact Algebra.FormallyUnramified.of_equiv (coefficientBaseChangeEquiv (K := K) (E := E) (ι := ι))

theorem length_quotient_map_of_unramified
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, Algebra.FormallyUnramified.map_maximalIdeal]
  let : IsSimpleModule B (B ⧸ maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [Module.length_eq_one B (B ⧸ maximalIdeal B), mul_one]

noncomputable def contractedPoint (b : ι → E) : Ideal (MvPolynomial ι K) :=
  (WeightedBezout.pointIdeal b).comap (algebraMap (MvPolynomial ι K) (MvPolynomial ι E))

instance contractedPoint_isPrime (b : ι → E) : (contractedPoint (K := K) b).IsPrime := by
  unfold contractedPoint
  infer_instance

instance point_liesOver (b : ι → E) :
    (WeightedBezout.pointIdeal b).LiesOver (contractedPoint (K := K) b) := ⟨rfl⟩

theorem contractedPoint_eq_ker (b : ι → E) :
    contractedPoint (K := K) b = RingHom.ker (MvPolynomial.aeval b).toRingHom := by
  ext p
  change MvPolynomial.aeval b (MvPolynomial.map (algebraMap K E) p) = 0 ↔
    MvPolynomial.aeval b p = 0
  simp [MvPolynomial.aeval_def]

noncomputable def pointLocalMap (b : ι → E) :
    Localization.AtPrime (contractedPoint (K := K) b) →+*
      Localization.AtPrime (WeightedBezout.pointIdeal b) :=
  Localization.localRingHom (contractedPoint (K := K) b) (WeightedBezout.pointIdeal b)
    (algebraMap (MvPolynomial ι K) (MvPolynomial ι E)) rfl

@[instance_reducible] noncomputable def pointLocalAlgebra (b : ι → E) :
    Algebra (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) :=
  Localization.AtPrime.algebraOfLiesOver (contractedPoint (K := K) b) (WeightedBezout.pointIdeal b)

theorem pointLocal_flat (b : ι → E) :
    letI := pointLocalAlgebra (K := K) b
    Module.Flat (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) := by
  let := pointLocalAlgebra (K := K) b
  let : Module.Flat (MvPolynomial ι K) (MvPolynomial ι E) := coefficientExtension_flat
  infer_instance

theorem pointLocal_unramified [Algebra.IsSeparable K E] (b : ι → E) :
    letI := pointLocalAlgebra (K := K) b
    Algebra.FormallyUnramified (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) := by
  let := pointLocalAlgebra (K := K) b
  let : Algebra.FormallyUnramified (MvPolynomial ι K) (MvPolynomial ι E) :=
    coefficientExtension_unramified
  exact Algebra.FormallyUnramified.of_restrictScalars (MvPolynomial ι K) _ _

theorem pointLocal_essFiniteType [Module.Finite K E] (b : ι → E) :
    letI := pointLocalAlgebra (K := K) b
    Algebra.EssFiniteType (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) := by
  let := pointLocalAlgebra (K := K) b
  let : Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) := coefficientExtension_finite
  exact Algebra.EssFiniteType.of_comp (MvPolynomial ι K) _ _

@[simp] theorem pointLocalMap_algebraMap (b : ι → E) (p : MvPolynomial ι K) :
    pointLocalMap (K := K) b (algebraMap _ (Localization.AtPrime (contractedPoint (K := K) b)) p) =
      algebraMap _ (Localization.AtPrime (WeightedBezout.pointIdeal b))
        (MvPolynomial.map (algebraMap K E) p) :=
  Localization.localRingHom_to_map _ _ _ rfl p

instance pointLocalMap_isLocalHom (b : ι → E) :
    IsLocalHom (pointLocalMap (K := K) b) :=
  Localization.isLocalHom_localRingHom _ _ _ rfl

theorem pointLocalMap_ideal_map (b : ι → E) (I : Ideal (MvPolynomial ι K)) :
    (I.map (algebraMap _ (Localization.AtPrime (contractedPoint (K := K) b)))).map
        (pointLocalMap (K := K) b) =
      (I.map (MvPolynomial.map (algebraMap K E))).map
        (algebraMap _ (Localization.AtPrime (WeightedBezout.pointIdeal b))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact pointLocalMap_algebraMap b p

theorem pointLocal_quotient_length [Module.Finite K E] [Algebra.IsSeparable K E]
    (b : ι → E) (I : Ideal (MvPolynomial ι K)) :
    Module.length (Localization.AtPrime (WeightedBezout.pointIdeal b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b) ⧸
        (I.map (MvPolynomial.map (algebraMap K E))).map
          (algebraMap _ (Localization.AtPrime (WeightedBezout.pointIdeal b)))) =
    Module.length (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (contractedPoint (K := K) b) ⧸
        I.map (algebraMap _ (Localization.AtPrime (contractedPoint (K := K) b)))) := by
  let A := Localization.AtPrime (contractedPoint (K := K) b)
  let B := Localization.AtPrime (WeightedBezout.pointIdeal b)
  let := pointLocalAlgebra (K := K) b
  let : IsLocalHom (algebraMap A B) := pointLocalMap_isLocalHom b
  let : Module.Flat A B := pointLocal_flat b
  let : Algebra.EssFiniteType A B := pointLocal_essFiniteType b
  let : Algebra.FormallyUnramified A B := pointLocal_unramified b
  have h := length_quotient_map_of_unramified (B := B) (I.map (algebraMap _ A))
  change Module.length B (B ⧸ (I.map (algebraMap _ A)).map (pointLocalMap (K := K) b)) = _ at h
  rw [pointLocalMap_ideal_map] at h
  exact h

theorem point_mem_minimalPrimes_map [Module.Finite K E]
    (b : ι → E) (I : Ideal (MvPolynomial ι K))
    (hminimal : contractedPoint (K := K) b ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal b ∈
      (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes := by
  let : Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) := coefficientExtension_finite
  change WeightedBezout.pointIdeal b ∈
    (I.map (algebraMap (MvPolynomial ι K) (MvPolynomial ι E))).minimalPrimes
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr hminimal.1.2⟩, ?_⟩
  intro Q hQ hQP
  let : Q.IsPrime := hQ.1
  have hunder : Q.under (MvPolynomial ι K) ≤ contractedPoint (K := K) b :=
    Ideal.comap_mono hQP
  have hcont : contractedPoint (K := K) b ≤ Q.under (MvPolynomial ι K) :=
    hminimal.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hQ.2⟩ hunder
  exact (Ideal.IsIntegral.mem_minimalPrimes_map_under
    (R := MvPolynomial ι K) (WeightedBezout.pointIdeal b)).2
      ⟨hQ.1, Ideal.map_le_iff_le_comap.mpr hcont⟩ hQP

end PiExponent.SeparablePointLength

end OAI
