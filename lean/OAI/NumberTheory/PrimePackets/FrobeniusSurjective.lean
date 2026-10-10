import Mathlib
import OAI.NumberTheory.PrimePackets.FrobeniusNonprincipal

namespace OAI

noncomputable section
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F : Type*) [Field F] [NumberField F]

 

def coprimeFractionalIdeals (N : ℕ) : Subgroup (FractionalIdeal (𝓞 F)⁰ F)ˣ where
  carrier := {I | ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    ¬ IsCoprime P.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) →
      FractionalIdeal.count F P I.val = 0}
  one_mem' := by intro P _; simp only [Units.val_one, FractionalIdeal.count_one]
  mul_mem' := by
    intro I J hI hJ P hP
    simp only [Units.val_mul, FractionalIdeal.count_mul F P (Units.ne_zero I) (Units.ne_zero J),
      hI P hP, hJ P hP, add_zero]
  inv_mem' := by
    intro I hI P hP
    simp only [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI P hP, neg_zero]

lemma prime_mem_coprimeFractionalIdeals (N : ℕ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hc : IsCoprime P.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N)) :
    integralIdealFractionalUnit P.asIdeal P.ne_bot ∈ coprimeFractionalIdeals F N := by
  intro Q hQ
  have hPQ : P ≠ Q := by intro he; exact hQ (he ▸ hc)
  change FractionalIdeal.count F Q (P.asIdeal : FractionalIdeal (𝓞 F)⁰ F) = 0
  rw [FractionalIdeal.count_maximal, ite_eq_right hPQ]

variable (E : Type*) [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup

lemma frobenius_finite_factor_support (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Function.HasFiniteMulSupport (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      primeFrobenius F E P ^ FractionalIdeal.count F P I.val) := by
  have h : {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) |
      FractionalIdeal.count F P I.val ≠ 0}.Finite := by
    simpa only [Filter.eventually_cofinite] using FractionalIdeal.finite_factors I.val
  apply h.subset
  intro P hP hzero
  apply hP
  change primeFrobenius F E P ^ FractionalIdeal.count F P I.val = 1
  rw [hzero, zpow_zero]

 

def frobeniusHom : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* (E ≃ₐ[F] E) where
  toFun I := ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    primeFrobenius F E P ^ FractionalIdeal.count F P I.val
  map_one' := by simp only [Units.val_one, FractionalIdeal.count_one, zpow_zero, finprod_one]
  map_mul' I J := by
    simp only [Units.val_mul, FractionalIdeal.count_mul F _ (Units.ne_zero I) (Units.ne_zero J),
      zpow_add]
    exact finprod_mul_distrib (frobenius_finite_factor_support F E I)
      (frobenius_finite_factor_support F E J)

lemma frobeniusHom_prime (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    frobeniusHom F E (integralIdealFractionalUnit P.asIdeal P.ne_bot) = primeFrobenius F E P := by
  change (∏ᶠ Q : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    primeFrobenius F E Q ^ FractionalIdeal.count F Q
      (P.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) = _
  rw [finprod_eq_single _ P]
  · rw [FractionalIdeal.count_self, zpow_one]
  · intro Q hQP
    rw [FractionalIdeal.count_maximal, ite_eq_right hQP.symm, zpow_zero]

lemma character_comp_frobeniusHom (χ : (E ≃ₐ[F] E) →* ℂˣ) :
    χ.comp (frobeniusHom F E) = idealHom F E χ := by
  apply DFunLike.ext
  intro I
  change χ (∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    primeFrobenius F E P ^ FractionalIdeal.count F P I.val) = _
  rw [χ.map_finprod (frobenius_finite_factor_support F E I)]
  simp only [map_zpow]
  rfl

 

def coprimeFrobeniusHom (N : ℕ) : coprimeFractionalIdeals F N →* (E ≃ₐ[F] E) :=
  (frobeniusHom F E).comp (coprimeFractionalIdeals F N).subtype

variable [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]

 

theorem coprimeFrobeniusHom_surjective (N : ℕ) (hN : 0 < N) :
    Function.Surjective (coprimeFrobeniusHom F E N) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro σ _
  by_contra hσ
  let H := (coprimeFrobeniusHom F E N).range
  have hq : QuotientGroup.mk' H σ ≠ 1 := by
    intro he
    exact hσ ((QuotientGroup.eq_one_iff σ).mp he)
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    ((E ≃ₐ[F] E) ⧸ H) ℂ hq
  let χ : (E ≃ₐ[F] E) →* ℂˣ := ψ.comp (QuotientGroup.mk' H)
  have hχ : χ ≠ 1 := by
    intro he
    exact hψ (DFunLike.congr_fun he σ)
  obtain ⟨P, hc, hP⟩ := Unfinished.actual_frobenius_nonprincipal F E χ hχ N hN
  apply hP
  change ψ (QuotientGroup.mk' H (primeFrobenius F E P)) = 1
  have hmem : primeFrobenius F E P ∈ H := by
    refine ⟨⟨integralIdealFractionalUnit P.asIdeal P.ne_bot,
      prime_mem_coprimeFractionalIdeals F N P hc⟩, ?_⟩
    exact frobeniusHom_prime F E P
  rw [show QuotientGroup.mk' H (primeFrobenius F E P) = 1 from
    (QuotientGroup.eq_one_iff _).mpr hmem, map_one]

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
