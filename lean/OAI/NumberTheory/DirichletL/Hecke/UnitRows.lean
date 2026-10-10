import OAI.NumberTheory.DirichletL.Hecke.RowClosure
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeUnitRows
open HeckeFamily CanonicalUnitEuler CanonicalRowCompletion
open ActualEisensteinCubic CubicRamified ConcreteTraceCRT
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "ω" => HeckeFamily.omega
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem seven_coprime_thirty_six : IsCoprime sevenPrime (36 : O) := by
  have hω : ω ^ 2 = -ω - 1 := by
    simpa [HeckeFamily.omega] using IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ HeckeFamily.K)
  change IsCoprime (1 + 3 * ω) (36 : O)
  refine ⟨31 * (-2 - 3 * ω), -6, ?_⟩
  linear_combination -279 * hω

theorem supported_unit_thirty_six (n : O) (hn : Supported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using hs.2)
  have h2 : IsCoprime n (2 : O) := (hneg2.of_isCoprime_of_dvd_left ⟨-1, by ring⟩).symm
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (h2.pow_right : IsCoprime n ((2 : O)^2)).mul_right h9 using 1 ; norm_num

theorem unitSupplement_unit (u v : Oˣ) : unitSupplement u (v : O) = 1 := by
  have hspan : (Ideal.span {(v : O)} : Ideal O) = 1 := by
    simpa only [Ideal.one_eq_top] using Ideal.span_singleton_eq_top.mpr v.isUnit
  have hs : Supported (1 : Ideal O) := ⟨one_ne_zero, by
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact False.elim (Multiset.notMem_zero P hP)⟩
  change (if Supported (Ideal.span {(v : O)}) then idealRowHom (u : O) (Ideal.span {(v : O)}) else 0) = 1
  rw [hspan, ite_eq_left hs, map_one]

private theorem unitSupplement_factorsModulo (u : Oˣ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36 : O)}) (unitSupplement u) :=
  unitSupplement_periodic u

def character (u : Oˣ) : Character :=
  HeckeRowClosure.rowCharacter (Ideal.span {(36 : O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)) (unitSupplement u)
    (unitSupplement_factorsModulo u) (unitSupplement_unit u)

theorem elementCoeff_character (u : Oˣ) (n : O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if Supported (Ideal.span {n}) then _ else 0
    rw [ite_eq_right (fun hs => hn (supported_unit_thirty_six n hs))]

theorem seven_supported : Supported (Ideal.span {sevenPrime}) := by
  rw [supported_span_iff]
  constructor
  · intro h
    have hd : λ₀ ∣ (36 : O) :=
      ((dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three).trans ⟨12, by norm_num⟩
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit
      (seven_coprime_thirty_six.isUnit_of_dvd' h hd)
  · intro h
    have hu := seven_coprime_thirty_six.isUnit_of_dvd' h (show (2 : O) ∣ 36 from ⟨18, by norm_num⟩)
    exact negative_two_prime.not_isUnit hu.neg

theorem unitSupplement_seven (u : Oˣ) :
    unitSupplement u sevenPrime = eisEmbedding (u : O) := by
  change (if Supported (Ideal.span {sevenPrime}) then idealRowHom (u : O) (Ideal.span {sevenPrime}) else 0) = _
  rw [ite_eq_left seven_supported,
    idealRowHom_unit_norm u _ seven_supported.1
      (supported_factors_good _ seven_supported)]
  change eisEmbedding ((u : O) ^ ((Ideal.absNorm sevenIdeal - 1) / 6)) = _
  rw [sevenIdeal_norm]
  norm_num

theorem character_nonprincipal (u : Oˣ) (hu : u ≠ 1) :
    (character u).residue ≠ 1 := by
  have hv : elementCoeff (character u) sevenPrime = eisEmbedding (u : O) := by
    rw [elementCoeff_character, unitSupplement_seven]
  have hv0 : elementCoeff (character u) sevenPrime ≠ 0 :=
    hv ▸ (u.isUnit.map eisEmbedding).ne_zero
  intro h
  have hunit := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff (character u) sevenPrime = 1 := by
    change (character u).residue _ = 1
    rw [h, MulChar.one_apply hunit]
  apply hu
  apply Units.ext
  apply eisEmbedding_injective
  simpa only [Units.val_one, map_one] using hv.symm.trans hv1

theorem masked_character_nonprincipal (u : Oˣ) (hu : u ≠ 1) (χ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff (character u) I else 0) :
    χ.residue ≠ 1 := by
  intro h
  exact character_nonprincipal u hu ((HeckeFiniteDeletion.principal_iff_of_mask χ (character u) hmask).mp h)

end SevenEighths.HeckeUnitRows

end

end OAI
