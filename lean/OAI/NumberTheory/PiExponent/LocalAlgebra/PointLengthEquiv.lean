import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout

namespace OAI

namespace PiExponent.PointLengthEquiv

open PiExponent.WeightedBezout

variable {E F ι : Type*} [Field E] [Field F]

theorem evaluation_map (e : E ≃+* F) (b : ι → E) (p : MvPolynomial ι E) :
    MvPolynomial.aeval (fun i => e (b i)) (MvPolynomial.map e.toRingHom p) =
      e (MvPolynomial.aeval b p) := by
  simpa [MvPolynomial.aeval_def] using
    ((MvPolynomial.eval_map e.toRingHom (fun i => e (b i)) p).trans
      (MvPolynomial.eval₂_comp e.toRingHom b p).symm)

theorem pointIdeal_comap (e : E ≃+* F) (b : ι → E) :
    pointIdeal b = (pointIdeal (fun i => e (b i))).comap
      (MvPolynomial.mapEquiv ι e).toRingHom := by
  ext p
  change MvPolynomial.aeval b p = 0 ↔
    MvPolynomial.aeval (fun i => e (b i)) (MvPolynomial.map e.toRingHom p) = 0
  rw [evaluation_map]
  exact e.map_eq_zero_iff.symm

theorem pointIdeal_map (e : E ≃+* F) (b : ι → E) :
    (pointIdeal b).map (MvPolynomial.mapEquiv ι e).toRingHom =
      pointIdeal (fun i => e (b i)) := by
  rw [pointIdeal_comap e b]
  exact Ideal.map_comap_of_surjective (MvPolynomial.mapEquiv ι e).toRingHom
    (MvPolynomial.mapEquiv ι e).surjective _

theorem pointLocal_quotient_length (e : E ≃+* F) (b : ι → E)
    (I : Ideal (MvPolynomial ι E)) :
    Module.length (Localization.AtPrime (pointIdeal b))
      (Localization.AtPrime (pointIdeal b) ⧸
        I.map (algebraMap _ (Localization.AtPrime (pointIdeal b)))) =
    Module.length (Localization.AtPrime (pointIdeal (fun i => e (b i))))
      (Localization.AtPrime (pointIdeal (fun i => e (b i))) ⧸
        (I.map (MvPolynomial.map e.toRingHom)).map
          (algebraMap _ (Localization.AtPrime (pointIdeal (fun i => e (b i)))))) := by
  exact PiExponentJets.W22.localized_quotient_length_eq_of_ringEquiv
    (MvPolynomial.mapEquiv ι e) (pointIdeal b) (pointIdeal (fun i => e (b i)))
    (pointIdeal_comap e b) I

theorem point_mem_minimalPrimes_map (e : E ≃+* F) (b : ι → E)
    (I : Ideal (MvPolynomial ι E)) (hI : pointIdeal b ∈ I.minimalPrimes) :
    pointIdeal (fun i => e (b i)) ∈ (I.map (MvPolynomial.map e.toRingHom)).minimalPrimes := by
  let φ := MvPolynomial.mapEquiv ι e
  change pointIdeal (fun i => e (b i)) ∈ (I.map φ.toRingHom).minimalPrimes
  have hker : RingHom.ker φ.toRingHom = ⊥ := by
    ext p
    change φ p = 0 ↔ p = 0
    exact φ.map_eq_zero_iff
  rw [Ideal.minimalPrimes_map_of_surjective (f := φ.toRingHom) φ.surjective, hker, sup_bot_eq]
  exact ⟨pointIdeal b, hI, pointIdeal_map e b⟩

end PiExponent.PointLengthEquiv

end OAI
