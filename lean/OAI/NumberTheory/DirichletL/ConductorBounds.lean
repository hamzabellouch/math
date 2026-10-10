import OAI.NumberTheory.DirichletL.FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

section QuotientBounds

variable {R : Type*} [CommRing R]

theorem quotient_card_le_of_le {I J : Ideal R} [Finite (R ⧸ J)] (hJI : J ≤ I) :
    Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) :=
  Nat.card_le_card_of_surjective _ (Ideal.Quotient.factor_surjective hJI)

theorem quotient_inf_card_le_mul (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

noncomputable def quotientComapEquiv (M : Ideal R) (I : Ideal (R ⧸ M)) :
    R ⧸ I.comap (Ideal.Quotient.mk M) ≃+* (R ⧸ M) ⧸ I :=
  RingEquiv.ofBijective (Ideal.quotientMap I (Ideal.Quotient.mk M) le_rfl)
    ⟨Ideal.quotientMap_injective,
      Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩

theorem quotientComapEquiv_mk (M : Ideal R) (I : Ideal (R ⧸ M)) (a : R) :
    quotientComapEquiv M I (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk I (Ideal.Quotient.mk M a) := rfl

theorem quotient_comap_card (M : Ideal R) (I : Ideal (R ⧸ M)) :
    Nat.card (R ⧸ I.comap (Ideal.Quotient.mk M)) = Nat.card ((R ⧸ M) ⧸ I) :=
  Nat.card_congr (quotientComapEquiv M I).toEquiv

end QuotientBounds

section FiniteRing

variable {R : Type*} [CommRing R] [Finite R]

theorem primitive_of_maximal_descent (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom)
    (hI : Maximal (FactorsThroughIdeal χ) I) : IsPrimitiveOnIdeals φ := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  apply (primitiveOnIdeals_iff_no_descent φ).mpr
  intro J hJ hdesc
  let K : Ideal R := J.comap (Ideal.Quotient.mk I)
  have hK : FactorsThroughIdeal χ K := by
    apply (factorsThroughIdeal_iff χ K).mpr
    intro u hu
    have huJ : ((quotientUnits I u : (R ⧸ I)ˣ) : R ⧸ I) - 1 ∈ J := by
      change Ideal.Quotient.mk I ((u : R) - 1) ∈ J at hu
      change Ideal.Quotient.mk I (u : R) - 1 ∈ J
      simpa only [map_sub, map_one] using hu
    have heq := congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ
    exact heq.symm.trans ((factorsThroughIdeal_iff φ J).mp hdesc _ huJ)
  have hIK : I ≤ K := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hKI : K ≤ I := hI.2 hK hIK
  apply hJ
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hKI hx)

theorem exists_primitive_quotient_above (χ : MulChar R ℂ) (J : Ideal R)
    (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by
  let : Finite (Ideal R) := Finite.of_injective
    (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  obtain ⟨I, hJI, hI⟩ := Finite.exists_le_maximal hJ
  obtain ⟨φ, hφ⟩ := hI.1
  exact ⟨I, φ, hJI, hφ, primitive_of_maximal_descent χ I φ hφ hI, hI⟩

theorem exists_primitive_quotient_above_with_bound_and_mask
    (χ : MulChar R ℂ) (J : Ideal R) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  let : Finite (R ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal⟩ := exists_primitive_quotient_above χ J hJ
  exact ⟨I, φ, hJI, hφ, hprimitive, hmaximal, quotient_card_le_of_le hJI,
    factorization_with_source_mask χ I φ hφ⟩

theorem FactorsThroughIdeal.mul {χ ψ : MulChar R ℂ} {I J : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    FactorsThroughIdeal (χ * ψ) (I ⊓ J) := by
  rw [factorsThroughIdeal_iff] at hχ hψ ⊢
  intro u hu
  rw [MulChar.mul_apply, hχ u hu.1, hψ u hu.2, one_mul]

theorem exists_primitive_product_quotient_with_bound_and_mask
    (χ ψ : MulChar R ℂ) (I J : Ideal R)
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    ∃ (K : Ideal R) (φ : MulChar (R ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ φ.toUnitHom.comp (quotientUnits K) = (χ * ψ).toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal (χ * ψ)) K ∧
      Nat.card (R ⧸ K) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a * ψ a = if IsUnit a then φ (Ideal.Quotient.mk K a) else 0 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  let : Finite (R ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))
  obtain ⟨K, φ, hIK, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_quotient_above_with_bound_and_mask (χ * ψ) (I ⊓ J) (hχ.mul hψ)
  exact ⟨K, φ, hIK, hφ, hprimitive, hmaximal,
    hcard.trans (quotient_inf_card_le_mul I J), hmask⟩

end FiniteRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]

theorem absNorm_le_of_le {I J : Ideal A} [Finite (A ⧸ J)] (hJI : J ≤ I) :
    I.absNorm ≤ J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_card_le_of_le hJI

theorem absNorm_inf_le_mul (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).absNorm ≤ I.absNorm * J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_inf_card_le_mul I J

theorem absNorm_comap_eq_quotient_card (M : Ideal A) (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).absNorm = Nat.card ((A ⧸ M) ⧸ I) := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using quotient_comap_card M I

theorem absNorm_comap_le (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).absNorm ≤ M.absNorm := by
  apply absNorm_le_of_le
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem

theorem exists_primitive_residue_quotient_above_with_norm_and_mask
    (M : Ideal A) [Finite (A ⧸ M)] (χ : MulChar (A ⧸ M) ℂ)
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal (A ⧸ M)) (φ : MulChar ((A ⧸ M) ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      (I.comap (Ideal.Quotient.mk M)).absNorm ≤
        (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A ⧸ M, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_quotient_above_with_bound_and_mask χ J hJ
  refine ⟨I, φ, hJI, hφ, hprimitive, hmaximal, ?_, hmask⟩
  simpa only [absNorm_comap_eq_quotient_card] using hcard

theorem exists_primitive_residue_product_with_norm_and_mask
    (M : Ideal A) [Finite (A ⧸ M)] (χ ψ : MulChar (A ⧸ M) ℂ)
    (I J : Ideal (A ⧸ M))
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    ∃ (K : Ideal (A ⧸ M)) (φ : MulChar ((A ⧸ M) ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ φ.toUnitHom.comp (quotientUnits K) = (χ * ψ).toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal (χ * ψ)) K ∧
      (K.comap (Ideal.Quotient.mk M)).absNorm ≤
        (I.comap (Ideal.Quotient.mk M)).absNorm *
          (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A ⧸ M, χ a * ψ a = if IsUnit a then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hIK, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_product_quotient_with_bound_and_mask χ ψ I J hχ hψ
  refine ⟨K, φ, hIK, hφ, hprimitive, hmaximal, ?_, hmask⟩
  simpa only [absNorm_comap_eq_quotient_card] using hcard

end

end SevenEighths.FiniteConductor

end OAI
