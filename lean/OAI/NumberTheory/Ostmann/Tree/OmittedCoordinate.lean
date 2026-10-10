import OAI.NumberTheory.Ostmann.Tree.IndependentCoordinate
import OAI.NumberTheory.Ostmann.Characters.PolynomialLineBounds

namespace OAI

/-! # Independence supplied by an absent compensation coordinate -/

namespace Ostmann

theorem polynomial_eval_insertNth_independent {A R : Type*} [CommRing R] {n : ℕ}
    (value : A → R) (P : MvPolynomial (Fin (n + 1)) ℤ) (i : Fin (n + 1))
    (hi : i ∉ P.vars) (x : Fin n → A) (a b : A) :
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun j => value ((i.insertNth a x : Fin (n + 1) → A) j)) P =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun j => value ((i.insertNth b x : Fin (n + 1) → A) j)) P := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro j hj _
  have hji : j ≠ i := by
    intro heq
    exact hi (heq ▸ hj)
  have hjrange : j ∈ Set.range i.succAbove := by
    rw [Fin.range_succAbove]
    exact hji
  obtain ⟨q, rfl⟩ := hjrange
  simp only [Fin.insertNth_apply_succAbove]

theorem integerTestValue_insertNth_independent {A : Type*} {n : ℕ}
    (value : A → ℤ) (P : MvPolynomial (Fin (n + 1)) ℤ) (i : Fin (n + 1))
    (hi : i ∉ P.vars) (x : Fin n → A) (a b : A) :
    integerTestValue value P (i.insertNth a x) = integerTestValue value P (i.insertNth b x) :=
  polynomial_eval_insertNth_independent value P i hi x a b

end Ostmann

end OAI
