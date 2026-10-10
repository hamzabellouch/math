import OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedLocalLength
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing WeightedBezout

variable {k σ : Type*} [Field k]

noncomputable def translatedPowerLocalMap (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Localization.AtPrime (pointIdeal a) →ₐ[k]
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
  Localization.localAlgHom (pointIdeal a) (pointIdeal (0 : σ → k))
    (translatedPowerSubstitution w a)
    (translatedPowerSubstitution_comap_origin w a hw).symm

instance translatedPowerLocalMap_isLocalHom (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    IsLocalHom (translatedPowerLocalMap w a hw).toRingHom :=
  Localization.isLocalHom_localRingHom _ _ _
    (translatedPowerSubstitution_comap_origin w a hw).symm

@[simp] theorem translatedPowerLocalMap_algebraMap (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (p : MvPolynomial σ k) :
    translatedPowerLocalMap w a hw
      (algebraMap _ (Localization.AtPrime (pointIdeal a)) p) =
      algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k)))
        (translatedPowerSubstitution w a p) :=
  Localization.localRingHom_to_map _ _ _
    (translatedPowerSubstitution_comap_origin w a hw).symm p

theorem translatedPowerLocalResidue_surjective (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Function.Surjective (IsLocalRing.ResidueField.map
      (translatedPowerLocalMap w a hw).toRingHom) := by
  apply residueField_map_surjective_of_mod_surjective
    (pointIdeal a) (pointIdeal (0 : σ → k))
    (translatedPowerSubstitution w a).toRingHom
    (translatedPowerSubstitution_comap_origin w a hw).symm
  intro p
  refine ⟨MvPolynomial.C (MvPolynomial.aeval (0 : σ → k) p), ?_⟩
  simp [mem_pointIdeal]

theorem translatedPowerLocalMap_ideal_map (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k)) :
    (I.map (algebraMap _ (Localization.AtPrime (pointIdeal a)))).map
        (translatedPowerLocalMap w a hw).toRingHom =
      (I.map (translatedPowerSubstitution w a).toRingHom).map
        (algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k)))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact translatedPowerLocalMap_algebraMap w a hw p

@[instance_reducible] noncomputable def translatedPowerLocalAlgebra (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Algebra (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) :=
  (translatedPowerLocalMap w a hw).toRingHom.toAlgebra

end PiExponent.RamifiedLocalLength

end OAI
