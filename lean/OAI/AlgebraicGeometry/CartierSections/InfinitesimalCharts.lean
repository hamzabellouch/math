/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

/-!
# Infinitesimal neighbourhoods in formally étale charts

Formal smoothness and formal unramifiedness give compatible isomorphisms on the
quotients by powers of an ideal whenever the residue map is an isomorphism.
-/

namespace CartierSections

/-- The multiplication action of a commutative ring on itself forms a scalar tower. -/
theorem scalarTower_self {R : Type*} [CommRing R] : IsScalarTower R R R :=
  IsScalarTower.right

attribute [local instance 10001] scalarTower_self

section NilpotentLifting
variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S]

/-- The image of an ideal modulo a power of itself is nilpotent. -/
theorem quotient_reduction_nilpotent (I : Ideal S) (n : ℕ) :
    IsNilpotent (I.map (Ideal.Quotient.mkₐ R (I^n))) := by
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow]
  exact Ideal.map_quotient_self _

/-- Formal smoothness lifts a residue map to every finite infinitesimal
neighbourhood. -/
theorem formally_smooth_lift_to_power [Algebra.FormallySmooth R A]
    (I : Ideal S) {n : ℕ} (hn : 0 < n) (f : A →ₐ[R] S ⧸ I) :
    ∃ g : A →ₐ[R] S ⧸ I^n,
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')).comp g = f := by
  let e := DoubleQuot.quotQuotEquivQuotOfLEₐ R (Ideal.pow_le_self (I := I) hn.ne')
  let g := Algebra.FormallySmooth.lift _ (quotient_reduction_nilpotent (R := R) I n)
    (e.symm.toAlgHom.comp f)
  refine ⟨g, ?_⟩
  rw [← DoubleQuot.quotQuotEquivQuotOfLEₐ_comp_mkₐ R]
  rw [AlgHom.comp_assoc, Algebra.FormallySmooth.comp_lift]
  ext a
  exact e.apply_symm_apply (f a)

/-- Formal unramifiedness gives uniqueness of lifts of a residue map. -/
theorem formally_unramified_unique_to_power [Algebra.FormallyUnramified R A]
    (I : Ideal S) {n : ℕ} (hn : 0 < n) (f g : A →ₐ[R] S ⧸ I^n)
    (h : (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')).comp f =
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')).comp g) : f = g := by
  apply Algebra.FormallyUnramified.lift_unique
    (I.map (Ideal.Quotient.mkₐ R (I^n))) (quotient_reduction_nilpotent (R := R) I n)
  ext a
  apply (DoubleQuot.quotQuotEquivQuotOfLEₐ R (Ideal.pow_le_self (I := I) hn.ne')).injective
  have he := DoubleQuot.quotQuotEquivQuotOfLEₐ_comp_mkₐ R
    (Ideal.pow_le_self (I := I) hn.ne')
  exact (AlgHom.congr_fun he (f a)).trans
    ((AlgHom.congr_fun h a).trans (AlgHom.congr_fun he (g a)).symm)
end NilpotentLifting

section QuotientIsomorphism
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The map on each infinitesimal neighbourhood induced by the algebra map. -/
def quotientPowerMap (I : Ideal R) (n : ℕ) :
    R ⧸ I^n →ₐ[R] A ⧸ (I.map (algebraMap R A))^n :=
  Ideal.quotientMapₐ _ (Algebra.ofId R A) (by
    rw [← Ideal.map_pow]
    exact Ideal.le_comap_map)

@[simp] theorem quotientPowerMap_mk (I : Ideal R) (n : ℕ) (r : R) :
    quotientPowerMap (A := A) I n (Ideal.Quotient.mk (I^n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R A))^n) (algebraMap R A r) := rfl

@[simp] theorem quotientPowerMap_algebraMap (I : Ideal R) (n : ℕ) (r : R) :
    quotientPowerMap (A := A) I n (algebraMap R (R ⧸ I^n) r) =
      algebraMap R (A ⧸ (I.map (algebraMap R A))^n) r := by
  exact (quotientPowerMap (A := A) I n).commutes r

theorem quotientPowerMap_factor (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I.map (algebraMap R A)) h)).comp
        (quotientPowerMap I n) =
      (quotientPowerMap I m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) h)) := by
  ext r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

def quotientBaseMap (I : Ideal R) : R ⧸ I →ₐ[R] A ⧸ I.map (algebraMap R A) :=
  Ideal.quotientMapₐ _ (Algebra.ofId R A) Ideal.le_comap_map

/-- A formally étale map which is an isomorphism modulo I is an
isomorphism modulo every power of I. -/
theorem etale_quotient_power_bijective [Algebra.FormallyEtale R A]
    (I : Ideal R) (hI : Function.Bijective (quotientBaseMap (A := A) I)) (n : ℕ) :
    Function.Bijective (quotientPowerMap (A := A) I n) := by
  classical
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (R ⧸ I^0) := by simp only [pow_zero, Ideal.one_eq_top]; infer_instance
    have : Subsingleton (A ⧸ (I.map (algebraMap R A))^0) := by
      simp only [pow_zero, Ideal.one_eq_top]; infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  let J := I.map (algebraMap R A)
  let φ₀ : R ⧸ I →ₐ[R] A ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R A) Ideal.le_comap_map
  have hφ₀ : Function.Bijective φ₀ := hI
  let e := AlgEquiv.ofBijective φ₀ hφ₀
  let f : A →ₐ[R] R ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  obtain ⟨g, hg⟩ := formally_smooth_lift_to_power I hn' f
  have hkill : J^n ≤ RingHom.ker g := by
    dsimp [J]
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro r hr
    change g (algebraMap R A r) = 0
    rw [g.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  let q : A ⧸ J^n →ₐ[R] R ⧸ I^n := Ideal.Quotient.liftₐ (J^n) g
    (fun a ha => hkill ha)
  have hleft : Function.LeftInverse q (quotientPowerMap (A := A) I n) := by
    intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact g.commutes r
  have heq : (quotientPowerMap (A := A) I n).comp g = Ideal.Quotient.mkₐ R (J^n) := by
    apply formally_unramified_unique_to_power J hn'
    have hfactor :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (I := J) hn)).comp
            (quotientPowerMap (A := A) I n) =
          φ₀.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (I := I) hn)) := by
      ext r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rfl
    rw [← AlgHom.comp_assoc, hfactor, AlgHom.comp_assoc, hg]
    ext a
    exact e.apply_symm_apply (Ideal.Quotient.mk J a)
  have hright : Function.RightInverse q (quotientPowerMap (A := A) I n) := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact AlgHom.congr_fun heq a
  exact ⟨hleft.injective, hright.surjective⟩
end QuotientIsomorphism
end CartierSections

end OAI
