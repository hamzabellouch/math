import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Tactic

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial

private theorem gridPolynomial_monic (R : Type*) [CommRing R] [Nontrivial R]
    (q : ℕ) (hq : 1 < q) : (X ^ q - X : R[X]).Monic := by
  apply monic_X_pow_sub
  rw [degree_X]
  exact_mod_cast hq

private theorem gridPolynomial_natDegree (R : Type*) [CommRing R] [Nontrivial R]
    (q : ℕ) (hq : 1 < q) : (X ^ q - X : R[X]).natDegree = q := by
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simpa using hq

variable {F : Type*} [Field F] [Fintype F]

theorem gridPolynomial_dvd_of_eval_zero (f : F[X])
    (hf : ∀ x : F, f.eval x = 0) : (X ^ Fintype.card F - X : F[X]) ∣ f := by
  let g : F[X] := X ^ Fintype.card F - X
  have hg : g.Monic := gridPolynomial_monic F _ Fintype.one_lt_card
  have hd : g.natDegree = Fintype.card F :=
    gridPolynomial_natDegree F _ Fintype.one_lt_card
  have hg1 : g ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hd, natDegree_one] at this
    exact Fintype.card_ne_zero this
  apply (modByMonic_eq_zero_iff_dvd hg).mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
  · intro x
    have hx : g.eval x = 0 := by simp [g, FiniteField.pow_card]
    change (f %ₘ g).eval x = 0
    rw [show (f %ₘ g).eval x = f.eval x from
      eval₂_modByMonic_eq_self_of_root (f := RingHom.id F) hx]
    exact hf x
  · exact (natDegree_modByMonic_lt f hg hg1).trans_eq hd

theorem nested_finite_grid_decomposition (P : F[X][X])
    (hP : ∀ x y : F, (P.map (Polynomial.evalRingHom y)).eval x = 0) :
    ∃ A B : F[X][X], P =
      (X ^ Fintype.card F - X) * A +
      C (X ^ Fintype.card F - X : F[X]) * B := by
  let g : F[X][X] := X ^ Fintype.card F - X
  let r := P %ₘ g
  have hg : g.Monic := gridPolynomial_monic F[X] _ Fintype.one_lt_card
  have hd : g.natDegree = Fintype.card F :=
    gridPolynomial_natDegree F[X] _ Fintype.one_lt_card
  have hg1 : g ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hd, natDegree_one] at this
    exact Fintype.card_ne_zero this
  have hr : ∀ y : F, r.map (Polynomial.evalRingHom y) = 0 := by
    intro y
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
    · intro x
      have hx : (g.map (Polynomial.evalRingHom y)).eval x = 0 := by
        simp [g, FiniteField.pow_card]
      change ((P %ₘ g).map (Polynomial.evalRingHom y)).eval x = 0
      rw [map_modByMonic _ hg]
      rw [show ((P.map (Polynomial.evalRingHom y)) %ₘ
        (g.map (Polynomial.evalRingHom y))).eval x =
        (P.map (Polynomial.evalRingHom y)).eval x from
          eval₂_modByMonic_eq_self_of_root (f := RingHom.id F) hx]
      exact hP x y
    · exact (natDegree_map_le).trans_lt
        ((natDegree_modByMonic_lt P hg hg1).trans_eq hd)
  have hdiv : C (X ^ Fintype.card F - X : F[X]) ∣ r := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    apply gridPolynomial_dvd_of_eval_zero
    intro y
    have h := congrArg (fun f : F[X] => f.coeff n) (hr y)
    simpa using h
  obtain ⟨B, hB⟩ := hdiv
  refine ⟨P /ₘ g, B, ?_⟩
  have heq := modByMonic_add_div P g
  change r + g * (P /ₘ g) = P at heq
  rw [hB] at heq
  exact heq.symm.trans (add_comm _ _)

end Balanced.StabilityPolynomial

end OAI
