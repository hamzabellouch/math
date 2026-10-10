import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Lean.Elab.Tactic.Omega

namespace OAI

universe uR uA

/-!
# Cyclotomic conjugation and norm divisibility in a DVR

The conjugation fixes the coefficient ring and sends the actual
adjoined root to its multiplicative inverse. In a DVR every ring
automorphism preserves the canonical additive valuation, because it sends
units to units and uniformizers to uniformizers. Consequently a norm equal
to a unit times an even scalar power forces the corresponding half-power
to divide the element.
-/

noncomputable section

namespace CirculantHadamard.RamifiedConjugation

open Polynomial IsDiscreteValuationRing

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Ring automorphisms of a DVR preserve its integer-valued order. -/
theorem addVal_ringEquiv (e : R ≃+* R) (x : R) :
    addVal R (e x) = addVal R x := by
  by_cases hx : x = 0
  · simp only [hx, map_zero]
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ
  have heπ : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have heu : e x = (Units.map e.toMonoidHom u : R) * (e π) ^ m := by
    simpa only [map_mul, map_pow, Units.coe_map,
      show e.toMonoidHom (u : R) = e (u : R) from rfl] using congrArg e hu
  rw [addVal_def x u hπ m hu,
    addVal_def (e x) (Units.map e.toMonoidHom u) heπ m heu]

private theorem enat_add_self_injective {a b : ℕ∞} (h : a + a = b + b) : a = b := by
  cases a using ENat.recTopCoe with
  | top =>
      cases b using ENat.recTopCoe with
      | top => rfl
      | coe b => simp only [← ENat.natCast_add, top_add, ENat.top_ne_natCast] at h
  | coe a =>
      cases b using ENat.recTopCoe with
      | top => simp only [← ENat.natCast_add, top_add, ENat.natCast_ne_top] at h
      | coe b =>
          have hab : a + a = b + b := ENat.natCast_inj.mp h
          have : a = b := by omega
          exact congrArg (fun n : ℕ => (n : ℕ∞)) this

/-- A norm with an even scalar exponent gives divisibility by half that
power. The statement includes zero and needs no normalization assumption
on the scalar's valuation. -/
theorem pow_dvd_of_norm_eq (e : R ≃+* R) (a x b : R) (t : ℕ)
    (hb : IsUnit b) (h : x * e x = a ^ (2 * t) * b) : a ^ t ∣ x := by
  have hsq : x * e x = (a ^ t * a ^ t) * b := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm t 2]
    exact h
  have hv := congrArg (addVal R) hsq
  have hbval : addVal R b = 0 := addVal_eq_zero_iff.mpr hb
  simp only [addVal_mul, addVal_ringEquiv, hbval, add_zero] at hv
  exact addVal_le_iff_dvd.mp (enat_add_self_injective hv).symm.le

end Valuation

section Cyclotomic

variable (A : Type uA) [CommRing A] (n : ℕ)

/-- The actual cyclotomic quotient used by the ramified construction. -/
abbrev CyclotomicRing := AdjoinRoot (cyclotomic n A)

/-- The adjoined root satisfies the stated order relation even before
domainhood or characteristic zero has been established. -/
theorem root_pow_order : AdjoinRoot.root (cyclotomic n A) ^ n = 1 := by
  have h : AdjoinRoot.mk (cyclotomic n A) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one n A)
  simpa only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] using h

variable (hn : 0 < n)
variable [domain : IsDomain (CyclotomicRing A n)] [charZero : CharZero (CyclotomicRing A n)]

include hn

/-- The quotient root is a primitive root of the exact specified order. -/
theorem root_isPrimitiveRoot :
    IsPrimitiveRoot (AdjoinRoot.root (cyclotomic n A)) n := by
  apply (isRoot_cyclotomic_iff_charZero hn).mp
  simpa only [map_cyclotomic] using AdjoinRoot.isRoot_root (cyclotomic n A)

omit domain charZero in
theorem root_pow_pred_mul_root [IsDomain (CyclotomicRing A n)]
    [CharZero (CyclotomicRing A n)] :
    AdjoinRoot.root (cyclotomic n A) ^ (n - 1) *
      AdjoinRoot.root (cyclotomic n A) = 1 := by
  rw [← pow_succ, Nat.sub_add_cancel hn, root_pow_order]

private theorem inverse_root_aeval :
    aeval (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (cyclotomic n A) = 0 := by
  have hcoprime : (n - 1).Coprime n :=
    (Nat.coprime_self_sub_left hn).mpr (Nat.coprime_one_left n)
  have hroot :=
    ((root_isPrimitiveRoot A n hn).pow_of_coprime (n - 1) hcoprime).isRoot_cyclotomic hn
  rw [aeval_def, ← eval_map, map_cyclotomic]
  exact hroot

/-- The root-inverting endomorphism fixes the coefficient algebra. -/
def conjugationHom : CyclotomicRing A n →ₐ[A] CyclotomicRing A n :=
  AdjoinRoot.liftAlgHom (cyclotomic n A)
    (Algebra.ofId A (CyclotomicRing A n))
    (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (inverse_root_aeval A n hn)

@[simp] theorem conjugationHom_root :
    conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A)) =
      AdjoinRoot.root (cyclotomic n A) ^ (n - 1) := by
  exact AdjoinRoot.liftAlgHom_root (cyclotomic n A)
    (Algebra.ofId A (CyclotomicRing A n))
    (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (inverse_root_aeval A n hn)

theorem conjugationHom_comp_self :
    (conjugationHom A n hn).comp (conjugationHom A n hn) =
      AlgHom.id A (CyclotomicRing A n) := by
  apply AdjoinRoot.algHom_ext
  change conjugationHom A n hn
    (conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A))) =
      AdjoinRoot.root (cyclotomic n A)
  rw [conjugationHom_root]
  have hzero : AdjoinRoot.root (cyclotomic n A) ≠ 0 :=
    ((root_isPrimitiveRoot A n hn).isUnit (ne_of_gt hn)).ne_zero
  apply mul_right_cancel₀ (pow_ne_zero (n - 1) hzero)
  calc
    conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) *
        AdjoinRoot.root (cyclotomic n A) ^ (n - 1) =
      conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A) ^ (n - 1) *
        AdjoinRoot.root (cyclotomic n A)) := by rw [map_mul, conjugationHom_root]
    _ = 1 := by rw [root_pow_pred_mul_root A n hn, map_one]
    _ = AdjoinRoot.root (cyclotomic n A) *
        AdjoinRoot.root (cyclotomic n A) ^ (n - 1) := by
      simpa only [mul_comm] using (root_pow_pred_mul_root A n hn).symm

/-- The actual involutive algebra automorphism inverting the cyclotomic root. -/
def cyclotomicConjugation : CyclotomicRing A n ≃ₐ[A] CyclotomicRing A n :=
  AlgEquiv.ofAlgHom (conjugationHom A n hn) (conjugationHom A n hn)
    (conjugationHom_comp_self A n hn) (conjugationHom_comp_self A n hn)

@[simp] theorem cyclotomicConjugation_root :
    cyclotomicConjugation A n hn (AdjoinRoot.root (cyclotomic n A)) =
      AdjoinRoot.root (cyclotomic n A) ^ (n - 1) :=
  conjugationHom_root A n hn

theorem cyclotomicConjugation_involutive :
    Function.Involutive (cyclotomicConjugation A n hn) := by
  intro x
  exact DFunLike.congr_fun (conjugationHom_comp_self A n hn) x

variable [IsDiscreteValuationRing (CyclotomicRing A n)]

@[simp] theorem cyclotomicConjugation_addVal (x : CyclotomicRing A n) :
    addVal (CyclotomicRing A n) (cyclotomicConjugation A n hn x) =
      addVal (CyclotomicRing A n) x :=
  addVal_ringEquiv (cyclotomicConjugation A n hn).toRingEquiv x

theorem cyclotomic_pow_dvd_of_norm_eq (a x b : CyclotomicRing A n) (t : ℕ)
    (hb : IsUnit b)
    (h : x * cyclotomicConjugation A n hn x = a ^ (2 * t) * b) : a ^ t ∣ x :=
  pow_dvd_of_norm_eq (cyclotomicConjugation A n hn).toRingEquiv a x b t hb h

end Cyclotomic

end CirculantHadamard.RamifiedConjugation

end

end OAI
