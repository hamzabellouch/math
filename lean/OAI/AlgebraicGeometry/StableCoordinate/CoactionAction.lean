import OAI.AlgebraicGeometry.StableCoordinate.CoactionLND

namespace OAI

/-!
# Polynomial additive actions: invariants and scalar automorphisms

Additional interfaces for the genuine two-parameter polynomial coaction from
`CoactionLND`: coefficient-law construction, scalar specializations as algebra
automorphisms, pointwise invariants, and characteristic-zero uniqueness.
-/

noncomputable section
namespace StableCoordinate.CoactionLND.PolynomialAdditiveAction
open Polynomial
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Construct an additive algebraic action from the coefficient identities of
the actual two-parameter additive group law. -/
def ofCoeffLaw (φ : A →ₐ[k] A[X])
    (hzero : ∀ a, (φ a).coeff 0 = a)
    (hadd : ∀ a m n, (φ ((φ a).coeff n)).coeff m =
      (m + n).choose m • (φ a).coeff (m + n)) : PolynomialAdditiveAction k A where
  toAlgHom := φ
  identity := hzero
  coassoc a := by
    ext n m
    rw [coeff_map, coeff_universal_translate, hasseDeriv_coeff]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Nat.choose_symm_add, nsmul_eq_mul] using hadd a m n

section Specialization

/-- Evaluate the additive action at a scalar parameter. -/
noncomputable def specialize (ρ : PolynomialAdditiveAction k A) (t : k) : A →ₐ[k] A :=
  (Polynomial.eval₂AlgHom (AlgHom.id k A) (algebraMap k A t)
    (fun _ => Commute.all _ _)).comp ρ.toAlgHom

@[simp] theorem specialize_apply (ρ : PolynomialAdditiveAction k A) (t : k) (a : A) :
    ρ.specialize t a = (ρ.toAlgHom a).eval (algebraMap k A t) := by
  simp [specialize, Polynomial.eval₂AlgHom_apply]

/-- Applying a scalar specialization to coefficients translates the action
parameter by that scalar. -/
theorem map_specialize (ρ : PolynomialAdditiveAction k A) (t : k) (a : A) :
    (ρ.toAlgHom a).map (ρ.specialize t).toRingHom =
      taylor (algebraMap k A t) (ρ.toAlgHom a) := by
  have he : (Polynomial.evalRingHom (algebraMap k A t)).comp
      ρ.toAlgHom.toRingHom = (ρ.specialize t).toRingHom := by
    ext b
    simp [specialize_apply]
  have hc : (Polynomial.evalRingHom (algebraMap k A t)).comp
      (C : A →+* A[X]) = RingHom.id A := by
    ext b
    simp
  have h := congrArg (Polynomial.map (Polynomial.evalRingHom (algebraMap k A t)))
    (ρ.coassoc a)
  simpa only [map_map, he, map_taylor, coe_evalRingHom, eval_X, hc, map_id] using h

@[simp] theorem specialize_zero (ρ : PolynomialAdditiveAction k A) (a : A) :
    ρ.specialize 0 a = a := by
  simp [specialize_apply, ← coeff_zero_eq_eval_zero, ρ.identity]

/-- The two-parameter polynomial group law specializes to the group law on
algebra automorphisms. -/
theorem specialize_add (ρ : PolynomialAdditiveAction k A) (s t : k) (a : A) :
    ρ.specialize s (ρ.specialize t a) = ρ.specialize (s + t) a := by
  have h := Polynomial.eval_map_apply (ρ.specialize s).toRingHom
    (p := ρ.toAlgHom a) (algebraMap k A t)
  rw [ρ.map_specialize, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes, taylor_eval] at h
  simpa only [specialize_apply, map_add, add_comm] using h.symm

/-- An algebraic additive coaction gives genuine algebra automorphisms at
all scalar parameters, with inverse parameter `-t`. -/
noncomputable def specializeEquiv (ρ : PolynomialAdditiveAction k A) (t : k) : A ≃ₐ[k] A :=
  AlgEquiv.ofAlgHom (ρ.specialize t) (ρ.specialize (-t))
    (by
      ext a
      change ρ.specialize t (ρ.specialize (-t) a) = a
      rw [ρ.specialize_add, add_neg_cancel, ρ.specialize_zero])
    (by
      ext a
      change ρ.specialize (-t) (ρ.specialize t a) = a
      rw [ρ.specialize_add, neg_add_cancel, ρ.specialize_zero])

@[simp] theorem specializeEquiv_apply (ρ : PolynomialAdditiveAction k A) (t : k) (a : A) :
    ρ.specializeEquiv t a = ρ.specialize t a := rfl

end Specialization

section Invariants

variable [IsDomain A] [CharZero A]

/-- In characteristic zero, the kernel of the infinitesimal derivation is
exactly the ring of invariants of the algebraic additive action. -/
theorem invariant_iff_derivation_eq_zero (ρ : PolynomialAdditiveAction k A) (a : A) :
    ρ.toAlgHom a = C a ↔ ρ.derivation a = 0 := by
  constructor
  · intro h
    simp [derivation_apply, h]
  · intro h
    ext n
    by_cases hn : n = 0
    · subst n
      simp [ρ.identity]
    · rw [coeff_C, ite_eq_right hn]
      have hz : (ρ.derivation : A → A)^[n] a = 0 := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        rw [Function.iterate_succ_apply, h]
        exact Function.iterate_fixed (map_zero ρ.derivation) m
      rw [ρ.iterate_derivation, nsmul_eq_mul] at hz
      exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Over a characteristic-zero domain the infinitesimal derivation determines
an additive polynomial coaction. -/
theorem toAlgHom_eq_of_derivation_eq (ρ σ : PolynomialAdditiveAction k A)
    (h : ρ.derivation = σ.derivation) : ρ.toAlgHom = σ.toAlgHom := by
  ext a n
  have hi : n.factorial • (ρ.toAlgHom a).coeff n =
      n.factorial • (σ.toAlgHom a).coeff n := by
    rw [← ρ.iterate_derivation, ← σ.iterate_derivation, h]
  simp only [nsmul_eq_mul] at hi
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n) hi

end Invariants

end StableCoordinate.CoactionLND.PolynomialAdditiveAction

end

end OAI
