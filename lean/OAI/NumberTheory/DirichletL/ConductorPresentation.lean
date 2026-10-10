import OAI.NumberTheory.DirichletL.ConductorBounds
import OAI.NumberTheory.DirichletL.CharacterTransport

namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

section Transport

variable {A : Type*} [CommRing A]

def quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) : MulChar (A ⧸ I.comap (Ideal.Quotient.mk M)) ℂ :=
  CharacterTransport.pullback (quotientComapEquiv M I) φ

@[simp] theorem quotientCharacter_mk (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := rfl

theorem primitive_quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (hφ : IsPrimitiveOnIdeals φ) :
    IsPrimitiveOnIdeals (quotientCharacter M I φ) :=
  CharacterTransport.primitive_pullback _ _ hφ

theorem source_le_comap (M : Ideal A) (I : Ideal (A ⧸ M)) :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem

theorem unit_factorization_of_mask (M K : Ideal A) (hMK : M ≤ K)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0) :
    φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMK).toMonoidHom) =
      χ.toUnitHom := by
  apply MonoidHom.ext
  intro u
  apply Units.ext
  change φ (Ideal.Quotient.factor hMK (u : A ⧸ M)) = χ (u : A ⧸ M)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ M)
  have h := hmask a
  simp only [ha, u.isUnit, ite_true] at h
  simpa only [← ha, Ideal.Quotient.factor_mk] using h.symm

end Transport

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]

theorem comap_ne_bot (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by
  let : Finite ((A ⧸ M) ⧸ I) :=
    Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hpos : 0 < (I.comap (Ideal.Quotient.mk M)).absNorm := by
    rw [absNorm_comap_eq_quotient_card]
    exact Nat.card_pos
  intro hzero
  rw [hzero, Ideal.absNorm_bot] at hpos
  exact (lt_irrefl 0) hpos

theorem exists_primitive_presentation_above_quotient
    (M : Ideal A) [Finite (A ⧸ M)] (χ : MulChar (A ⧸ M) ℂ)
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ J.comap (Ideal.Quotient.mk M) ≤ K ∧ K ≠ ⊥ ∧
      IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, ψ, hJI, hψ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_quotient_above_with_norm_and_mask M χ J hJ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I ψ,
    source_le_comap M I, Ideal.comap_mono hJI, comap_ne_bot M I,
    primitive_quotientCharacter M I ψ hprimitive, hnorm, ?_⟩
  intro a
  simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)

theorem exists_primitive_presentation (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hMK, hbotK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation_above_quotient M χ ⊥ (FactorsThroughIdeal.bot χ)
  refine ⟨K, φ, hMK, hK, hprimitive, ?_, hmask⟩
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hnorm

theorem exists_primitive_presentation_above
    (M L : Ideal A) [Finite (A ⧸ M)] (hML : M ≤ L)
    (χ : MulChar (A ⧸ M) ℂ)
    (hL : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ L.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  simpa only [Ideal.comap_map_mk hML] using
    exists_primitive_presentation_above_quotient M χ (L.map (Ideal.Quotient.mk M)) hL

theorem exists_primitive_product_presentation
    (M L₁ L₂ : Ideal A) [Finite (A ⧸ M)] (hML₁ : M ≤ L₁) (hML₂ : M ≤ L₂)
    (χ ψ : MulChar (A ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L₁.map (Ideal.Quotient.mk M)))
    (hψ : FactorsThroughIdeal ψ (L₂.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L₁ ⊓ L₂ ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ L₁.absNorm * L₂.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) * ψ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_product_with_norm_and_mask M χ ψ
      (L₁.map (Ideal.Quotient.mk M)) (L₂.map (Ideal.Quotient.mk M)) hχ hψ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I φ,
    source_le_comap M I, ?_, comap_ne_bot M I,
    primitive_quotientCharacter M I φ hprimitive, ?_, ?_⟩
  · have h := Ideal.comap_mono (f := Ideal.Quotient.mk M) hJI
    simpa only [Ideal.comap_inf, Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using h
  · simpa only [Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using hnorm
  · intro a
    simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)

theorem exists_primitive_power_presentation
    (M L : Ideal A) [Finite (A ⧸ M)] (hML : M ≤ L)
    (χ : MulChar (A ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) (n : ℕ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ L.absNorm ∧
      ∀ a : A, (χ ^ n) (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 :=
  exists_primitive_presentation_above M L hML (χ ^ n) (hχ.pow n)

end

end ConductorPresentation

end SevenEighths

end OAI
