import Mathlib
import OAI.NumberTheory.PrimePackets.RayContinuation

namespace OAI

noncomputable section
open Set Module Filter
open scoped NumberField nonZeroDivisors BigOperators Classical
namespace PrimeDegreePackets
namespace GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

 
def primeAbove (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Ideal.primesOver P.asIdeal (𝓞 E) := Classical.choice inferInstance

omit [NumberField F] [NumberField E] [FiniteDimensional F E] [IsGalois F E] in
lemma primeAbove_ne_bot (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (primeAbove F E P).val ≠ ⊥ :=
  Ideal.ne_bot_of_mem_primesOver P.ne_bot (primeAbove F E P).property

 
def primeFrobenius (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : E ≃ₐ[F] E := by
  let Q := primeAbove F E P
  letI : Q.val.IsPrime := Q.property.1
  letI : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E P)
  exact arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q.val

lemma primeFrobenius_spec (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    IsArithFrobAt (𝓞 F) (primeFrobenius F E P) (primeAbove F E P).val := by
  let Q := primeAbove F E P
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E P)
  exact IsArithFrobAt.arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q.val

variable (χ : (E ≃ₐ[F] E) →* ℂˣ)

lemma finite_factor_support (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Function.HasFiniteMulSupport (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val) := by
  have h : {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) |
      FractionalIdeal.count F P I.val ≠ 0}.Finite := by
    simpa only [Filter.eventually_cofinite] using
      FractionalIdeal.finite_factors I.val
  apply h.subset
  intro P hP
  change (χ (primeFrobenius F E P)) ^ FractionalIdeal.count F P I.val ≠ 1 at hP
  intro hzero
  exact hP (by rw [hzero, zpow_zero])

 

def idealHom : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* ℂˣ where
  toFun I := ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val
  map_one' := by simp only [Units.val_one, FractionalIdeal.count_one, zpow_zero, finprod_one]
  map_mul' I J := by
    simp only [Units.val_mul, FractionalIdeal.count_mul F _ (Units.ne_zero I) (Units.ne_zero J),
      zpow_add]
    exact finprod_mul_distrib (finite_factor_support F E χ I) (finite_factor_support F E χ J)

lemma idealHom_prime (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    idealHom F E χ (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      χ (primeFrobenius F E P) := by
  change (∏ᶠ Q : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    χ (primeFrobenius F E Q) ^ FractionalIdeal.count F Q
      (P.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) = _
  rw [finprod_eq_single _ P]
  · rw [FractionalIdeal.count_self, zpow_one]
  · intro Q hQP
    rw [FractionalIdeal.count_maximal, ite_eq_right hQP.symm, zpow_zero]

lemma idealHom_finiteOrder : ∃ e : ℕ, 0 < e ∧ ∀ I, idealHom F E χ I ^ e = 1 := by
  refine ⟨Nat.card (E ≃ₐ[F] E), Nat.card_pos, ?_⟩
  intro I
  change (∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val) ^ _ = 1
  rw [finprod_pow (finite_factor_support F E χ I)]
  have hpow (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      (χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val) ^
        Nat.card (E ≃ₐ[F] E) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow,
      pow_card_eq_one', map_one, one_zpow]
  simp only [hpow, finprod_one]

 

theorem idealHom_prime_frobenius
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (Q : Ideal (𝓞 E)) [Q.IsPrime] (hQ : Q.under (𝓞 F) = P.asIdeal)
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (τ : E ≃ₐ[F] E) (hτ : (NumberField.RingOfIntegers.mapAlgHom τ).IsArithFrobAt Q) :
    idealHom F E χ (integralIdealFractionalUnit P.asIdeal P.ne_bot) = χ τ := by
  rw [idealHom_prime]
  let Q₀ := primeAbove F E P
  let : Q₀.val.IsPrime := Q₀.property.1
  let : Q₀.val.IsMaximal := Q₀.property.1.isMaximal (primeAbove_ne_bot F E P)
  have hOver : Q ∈ Ideal.primesOver P.asIdeal (𝓞 E) := ⟨inferInstance, ⟨hQ.symm⟩⟩
  let : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_mem_primesOver P.ne_bot hOver)
  let : FaithfulSMul (E ≃ₐ[F] E) (𝓞 E) := IsGaloisGroup.faithful (𝓞 F)
  have hsame : arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q = τ := by
    apply MulSemiringAction.toAlgHom_injective (𝓞 F) (𝓞 E)
    exact (IsArithFrobAt.arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q).eq_of_isUnramifiedAt
      hτ Q.primeCompl_le_nonZeroDivisors
  have hc := isConj_arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q₀.val Q
    (Q₀.property.2.over.symm.trans hQ.symm)
  rw [hsame] at hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  change χ (arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q₀.val) = χ τ
  rw [← hg]
  simp only [map_mul, map_inv]
  simp [mul_assoc]

end GaloisIdealCharacter
end PrimeDegreePackets

end

end OAI
