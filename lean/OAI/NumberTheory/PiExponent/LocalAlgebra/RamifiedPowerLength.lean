import OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedLocalization
import OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPointMap
import OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover

namespace OAI

namespace PiExponent.RamifiedLocalLength

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

abbrev coverOriginIdeal (w : σ → ℕ) (a : σ → k) :
    Ideal (TranslatedPowerCover.Ring w a) :=
  (pointIdeal (0 : σ → k)).comap (TranslatedPowerCover.toPolynomial w a).toRingHom

instance coverOriginIdeal_isMaximal (w : σ → ℕ) (a : σ → k) :
    (coverOriginIdeal w a).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (TranslatedPowerCover.toPolynomial w a).surjective

omit [Fintype σ] in
theorem coverOriginIdeal_liesOver (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    (coverOriginIdeal w a).LiesOver (pointIdeal a) := by
  constructor
  change pointIdeal a =
    ((pointIdeal (0 : σ → k)).comap (TranslatedPowerCover.toPolynomial w a).toRingHom).comap
      (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
  rw [Ideal.comap_comap]
  exact (translatedPowerSubstitution_comap_origin w a hw).symm

omit [Fintype σ] in
theorem coverOriginIdeal_unique (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i)
    (Q : Ideal (TranslatedPowerCover.Ring w a)) (hQ : Q.IsPrime)
    (hQa : pointIdeal a ≤ Q.under (MvPolynomial σ k)) : Q = coverOriginIdeal w a := by
  let e := TranslatedPowerCover.toPolynomial w a
  let : Q.IsPrime := hQ
  have hmap : (Q.map e.toRingHom).IsPrime := Ideal.map_isPrime_of_equiv e
  let : (Q.map e.toRingHom).IsPrime := hmap
  have hcont : pointIdeal a ≤ (Q.map e.toRingHom).comap (translatedPowerSubstitution w a).toRingHom := by
    intro p hp
    exact Ideal.mem_map_of_mem e.toRingHom (hQa hp)
  have hle : pointIdeal (0 : σ → k) ≤ Q.map e.toRingHom := by
    rw [pointIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro polynomial ⟨index, rfl⟩
    have hcoordinate : MvPolynomial.X index - MvPolynomial.C (a index) ∈ pointIdeal a := by
      simp
    have hpower := hcont hcoordinate
    change translatedPowerSubstitution w a
      (MvPolynomial.X index - MvPolynomial.C (a index)) ∈ Q.map e.toRingHom at hpower
    have hvariable : MvPolynomial.X index ∈ Q.map e.toRingHom :=
      (hmap.pow_mem_iff_mem (w index) (hw index)).mp (by
        simpa only [map_sub, translatedPowerSubstitution_X, translatedPowerSubstitution_C,
          add_sub_cancel_left] using hpower)
    simpa using hvariable
  have hEq := ((inferInstance : (pointIdeal (0 : σ → k)).IsMaximal).eq_of_le
    hmap.ne_top hle).symm
  have hc := congrArg (Ideal.comap e.toRingHom) hEq
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

def coverOriginLocalEquiv (w : σ → ℕ) (a : σ → k) :
    Localization.AtPrime (coverOriginIdeal w a) ≃+*
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
  Localization.localRingEquiv (coverOriginIdeal w a) (pointIdeal (0 : σ → k))
    (TranslatedPowerCover.toPolynomial w a) rfl

def translatedPowerLocalBasis (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    letI := translatedPowerLocalAlgebra w a hw
    Module.Basis (∀ i, Fin (w i)) (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) := by
  classical
  letI := translatedPowerLocalAlgebra w a hw
  let : (coverOriginIdeal w a).LiesOver (pointIdeal a) := coverOriginIdeal_liesOver w a hw
  letI := Localization.AtPrime.algebraOfLiesOver (pointIdeal a) (coverOriginIdeal w a)
  have hcomm : (coverOriginLocalEquiv w a).toRingHom.comp
        (algebraMap (Localization.AtPrime (pointIdeal a))
          (Localization.AtPrime (coverOriginIdeal w a))) =
      (translatedPowerLocalMap w a hw).toRingHom := by
    change (Localization.localRingHom (coverOriginIdeal w a) (pointIdeal (0 : σ → k))
      (TranslatedPowerCover.toPolynomial w a).toRingHom rfl).comp
        (Localization.localRingHom (pointIdeal a) (coverOriginIdeal w a)
          (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
          (Ideal.over_def (coverOriginIdeal w a) (pointIdeal a))) = _
    exact (Localization.localRingHom_comp (pointIdeal a) (coverOriginIdeal w a)
      (pointIdeal (0 : σ → k))
      (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
      (Ideal.over_def (coverOriginIdeal w a) (pointIdeal a))
      (TranslatedPowerCover.toPolynomial w a).toRingHom rfl).symm
  let e : Localization.AtPrime (coverOriginIdeal w a) ≃ₐ[Localization.AtPrime (pointIdeal a)]
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
    { __ := coverOriginLocalEquiv w a
      commutes' := fun x => RingHom.congr_fun hcomm x }
  exact (basis_atPrime_of_unique_fibre (pointIdeal a) (coverOriginIdeal w a)
    (TranslatedPowerCover.basis w a hw) (coverOriginIdeal_unique w a hw)).map e.toLinearEquiv

theorem translatedPowerLocal_finrank (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    letI := translatedPowerLocalAlgebra w a hw
    Module.finrank (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) = ∏ i, w i := by
  classical
  let := translatedPowerLocalAlgebra w a hw
  rw [Module.finrank_eq_card_basis (translatedPowerLocalBasis w a hw)]
  simp [Fintype.card_pi]

theorem translatedPowerLocal_quotient_length (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k)) :
    Module.length (Localization.AtPrime (pointIdeal (0 : σ → k)))
      (Localization.AtPrime (pointIdeal (0 : σ → k)) ⧸
        (I.map (translatedPowerSubstitution w a).toRingHom).map
          (algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k))))) =
    Module.length (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal a) ⧸
        I.map (algebraMap _ (Localization.AtPrime (pointIdeal a)))) *
      ((∏ i, w i : ℕ) : ℕ∞) := by
  classical
  let A := Localization.AtPrime (pointIdeal a)
  let B := Localization.AtPrime (pointIdeal (0 : σ → k))
  let := translatedPowerLocalAlgebra w a hw
  let : IsLocalHom (algebraMap A B) := translatedPowerLocalMap_isLocalHom w a hw
  let : Module.Free A B := Module.Free.of_basis (translatedPowerLocalBasis w a hw)
  let : Module.Finite A B := Module.Finite.of_basis (translatedPowerLocalBasis w a hw)
  have hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) := translatedPowerLocalResidue_surjective w a hw
  have h := length_quotient_map_eq_finrank_mul hres (I.map (algebraMap _ A))
  rw [translatedPowerLocal_finrank w a hw] at h
  change Module.length B (B ⧸ (I.map (algebraMap _ A)).map
    (translatedPowerLocalMap w a hw).toRingHom) = _ at h
  rw [translatedPowerLocalMap_ideal_map] at h
  exact h

end
end PiExponent.RamifiedLocalLength

end OAI
