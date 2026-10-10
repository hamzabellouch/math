import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusConductor

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter
attribute [local instance] Ideal.Quotient.field
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]

lemma inertiaDeg_eq_one_of_one_isArithFrobAt
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E))
    [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    (h : (1 : (𝓞 E) →ₐ[𝓞 F] (𝓞 E)).IsArithFrobAt Q) :
    Q.inertiaDeg (𝓞 F) = 1 := by
  let : Fintype ((𝓞 F) ⧸ P) := Fintype.ofFinite _
  let : Fintype ((𝓞 E) ⧸ Q) := Fintype.ofFinite _
  rw [Ideal.inertiaDeg_eq_of_isMaximal P Q]
  have he : FiniteField.frobeniusAlgHom ((𝓞 F) ⧸ P) ((𝓞 E) ⧸ Q) = 1 := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx := h.mk_apply x
    simpa only [AlgHom.one_apply, ← Q.over_def P, Nat.card_eq_fintype_card,
      FiniteField.coe_frobeniusAlgHom] using hx.symm
  rw [← FiniteField.orderOf_frobeniusAlgHom ((𝓞 F) ⧸ P) ((𝓞 E) ⧸ Q), he, orderOf_one]

variable [FiniteDimensional F E] [IsGalois F E]

lemma inertiaDeg_eq_one_of_primeFrobenius_eq_one
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (h : primeFrobenius F E P = 1)
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P.asIdeal] :
    Q.inertiaDeg (𝓞 F) = 1 := by
  let Q₀ := primeAbove F E P
  let : Q₀.val.IsPrime := Q₀.property.1
  let : Q₀.val.IsMaximal := Q₀.property.1.isMaximal (primeAbove_ne_bot F E P)
  let : Q₀.val.LiesOver P.asIdeal := Q₀.property.2
  have hF := primeFrobenius_spec F E P
  rw [h] at hF
  rw [← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q₀.val Q (E ≃ₐ[F] E)]
  exact inertiaDeg_eq_one_of_one_isArithFrobAt F E P.asIdeal Q₀.val hF

lemma norm_eq_of_inertiaDeg_eq_one
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q₀ : Ideal (𝓞 E)) [Q₀.IsPrime] [Q₀.LiesOver P.asIdeal]
    (hf : Q₀.inertiaDeg (𝓞 F) = 1)
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P.asIdeal] :
    Ideal.absNorm Q = Ideal.absNorm P.asIdeal := by
  let : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q)
  rw [← Ideal.absNorm_pow_inertiaDeg P.asIdeal Q,
    ← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q₀ Q (E ≃ₐ[F] E), hf, pow_one]

lemma card_primesOver_of_unramified_of_inertia_one
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q₀ : Ideal (𝓞 E)) [Q₀.IsPrime] [Q₀.LiesOver P.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 F) Q₀]
    (hf : Q₀.inertiaDeg (𝓞 F) = 1) :
    Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) = finrank F E := by
  have HC := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    P.asIdeal (𝓞 E) (E ≃ₐ[F] E)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal Q₀ (E ≃ₐ[F] E),
    Ideal.inertiaDegIn_eq_inertiaDeg P.asIdeal Q₀ (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, hf, one_mul, mul_one,
    IsGalois.card_aut_eq_finrank] at HC
  exact HC

 

lemma one_isArithFrobAt_kernelFixedField
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hχP : χ (primeFrobenius F E P) = 1) :
    (1 : (𝓞 (IntermediateField.fixedField χ.ker)) →ₐ[𝓞 F]
      (𝓞 (IntermediateField.fixedField χ.ker))).IsArithFrobAt
        ((primeAbove F E P).val.under (𝓞 (IntermediateField.fixedField χ.ker))) := by
  let L : IntermediateField F E := IntermediateField.fixedField χ.ker
  let Q := (primeAbove F E P).val
  intro x
  have hfix : NumberField.RingOfIntegers.mapAlgHom (primeFrobenius F E P)
      (algebraMap (𝓞 L) (𝓞 E) x) = algebraMap (𝓞 L) (𝓞 E) x := by
    apply NumberField.RingOfIntegers.ext
    change primeFrobenius F E P ((x : L) : E) = ((x : L) : E)
    exact (IntermediateField.mem_fixedField_iff χ.ker _).mp (x : L).property
      (primeFrobenius F E P) hχP
  have hF := primeFrobenius_spec F E P
  change (NumberField.RingOfIntegers.mapAlgHom (primeFrobenius F E P)).IsArithFrobAt Q at hF
  have hx := hF (algebraMap (𝓞 L) (𝓞 E) x)
  rw [hfix] at hx
  change algebraMap (𝓞 L) (𝓞 E)
    (x - x ^ Nat.card ((𝓞 F) ⧸ (Q.under (𝓞 L)).under (𝓞 F))) ∈ Q
  simpa only [map_sub, map_pow, Ideal.under_under] using hx

lemma inertiaDeg_eq_one_kernelFixedField
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hχP : χ (primeFrobenius F E P) = 1)
    (R : Ideal (𝓞 (IntermediateField.fixedField χ.ker)))
    [R.IsPrime] [R.LiesOver P.asIdeal] :
    R.inertiaDeg (𝓞 F) = 1 := by
  let L : IntermediateField F E := IntermediateField.fixedField χ.ker
  let Q := (primeAbove F E P).val
  let : Q.IsPrime := (primeAbove F E P).property.1
  let : Q.LiesOver P.asIdeal := (primeAbove F E P).property.2
  let Q₀ := Q.under (𝓞 L)
  let : Q₀.IsPrime := inferInstance
  let : Q₀.LiesOver P.asIdeal := by
    constructor
    rw [Ideal.under_under, Q.over_def P.asIdeal]
  let : Q₀.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q₀)
  have hf := inertiaDeg_eq_one_of_one_isArithFrobAt F L P.asIdeal Q₀
    (one_isArithFrobAt_kernelFixedField F E χ P hχP)
  rw [← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q₀ R (L ≃ₐ[F] L)]
  exact hf

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
