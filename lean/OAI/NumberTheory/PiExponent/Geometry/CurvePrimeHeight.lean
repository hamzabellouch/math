import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension

namespace OAI

namespace PiExponent.CurvePrimeHeight


open PiExponentJets.W24 PiExponentSiegel.W23
open PiExponentJets.PolynomialLocalResidueResolution

theorem height_add_one_eq_of_quotient_dimension
    (F : Type*) [Field F] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (hdim : ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = 1) :
    P.height + 1 = (n : ℕ∞) := by
  have h := fin_polynomial_prime_pair_local_dimension F n ⊥ P bot_le
  have hbot : parameterLocalizedIdeal (⊥ : Ideal (MvPolynomial (Fin n) F)) P = ⊥ :=
    Ideal.map_bot
  rw [hbot] at h
  have hlocal : ringKrullDim (Localization.AtPrime P ⧸ (⊥ : Ideal (Localization.AtPrime P))) =
      ringKrullDim (Localization.AtPrime P) := by
    with_unfolding_all exact (RingEquiv.quotientBot (Localization.AtPrime P)).ringKrullDim
  have hpoly : ringKrullDim (MvPolynomial (Fin n) F ⧸ (⊥ : Ideal (MvPolynomial (Fin n) F))) =
      ringKrullDim (MvPolynomial (Fin n) F) := by
    with_unfolding_all exact (RingEquiv.quotientBot (MvPolynomial (Fin n) F)).ringKrullDim
  rw [hlocal, hpoly, IsLocalization.AtPrime.ringKrullDim_eq_height P
    (Localization.AtPrime P), hdim] at h
  apply WithBot.coe_injective
  simpa only [WithBot.coe_add, WithBot.coe_one,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard,
    Nat.card_fin, zero_add, WithBot.coe_natCast] using h

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem residue_trdeg_toNat_eq {ι : Type*} (z : ι → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (P : Ideal (MvPolynomial ι F)) [P.IsPrime]
    (hker : P = RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom) :
    (Algebra.trdeg F P.ResidueField).toNat = (Algebra.trdeg F E).toNat := by
  have hk : P ≤ RingHom.ker (MvPolynomial.aeval (R := F) z) := by
    intro p hp
    rw [hker] at hp
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hp
  have hu : P.primeCompl ≤
      (IsUnit.submonoid E).comap (MvPolynomial.aeval (R := F) z) := by
    intro p hp
    change p ∉ P at hp
    change IsUnit (MvPolynomial.aeval (R := F) z p)
    rw [isUnit_iff_ne_zero]
    simpa only [hker, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hp
  let f : P.ResidueField →ₐ[F] E :=
    Ideal.ResidueField.liftₐ P (MvPolynomial.aeval (R := F) z) hk hu
  have hf : Function.Surjective f := by
    apply AlgHom.fieldRange_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨algebraMap (MvPolynomial ι F) P.ResidueField (MvPolynomial.X i), by
      change Ideal.ResidueField.liftₐ P (MvPolynomial.aeval (R := F) z) hk hu
        (algebraMap (MvPolynomial ι F) P.ResidueField (MvPolynomial.X i)) = z i
      rw [Ideal.ResidueField.liftₐ_algebraMap]
      exact MvPolynomial.aeval_X z i⟩
  have he := (AlgEquiv.ofBijective f ⟨f.injective, hf⟩).lift_trdeg_eq
  simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat he

theorem quotient_dimension_eq_one {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1)
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (hker : P = RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = 1 := by
  rw [PiExponentJets.W24.affine_prime_quotient_dimension_eq_residue_trdeg F _ P,
    residue_trdeg_toNat_eq z hgen P hker, htrdeg]
  simp

theorem kernel_height_add_one_eq {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height + 1 = (n : ℕ∞) := by
  let P := RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom
  let : P.IsPrime := RingHom.ker_isPrime (MvPolynomial.aeval (R := F) z).toRingHom
  exact height_add_one_eq_of_quotient_dimension F n P
    (quotient_dimension_eq_one z hgen htrdeg P rfl)

theorem kernel_height_le {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height ≤ (n : ℕ∞) := by
  calc
    _ ≤ (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height + 1 :=
      le_add_of_nonneg_right (by simp)
    _ = (n : ℕ∞) := kernel_height_add_one_eq z hgen htrdeg

theorem kernel_height_succ_eq {m : ℕ} (z : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height = (m : ℕ∞) := by
  apply (WithTop.add_right_inj (show (1 : ℕ∞) ≠ ⊤ by simp)).mp
  simpa only [Nat.cast_add, Nat.cast_one] using! kernel_height_add_one_eq z hgen htrdeg

theorem kernel_height_succ_le {m : ℕ} (z : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin F (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg F E = 1) :
    (RingHom.ker (MvPolynomial.aeval (R := F) z).toRingHom).height ≤ (m : ℕ∞) :=
  (kernel_height_succ_eq z hgen htrdeg).le

end PiExponent.CurvePrimeHeight

end OAI
