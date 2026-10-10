import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Polynomial restrictions to coordinate lines -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial

/-- Each coordinate-line restriction is a polynomial of degree at most `D`. -/
def CoordinatePolynomial (n D : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n) (x : Fin n → ℝ), ∃ p : ℝ[X], p.natDegree ≤ D ∧
    ∀ t : ℝ, p.eval t = f (Function.update x i t)

theorem CoordinatePolynomial.head {n D : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : CoordinatePolynomial (n + 1) D f) (x : Fin n → ℝ) :
    ∃ p : ℝ[X], p.natDegree ≤ D ∧ ∀ t, p.eval t = f (Fin.cons t x) := by
  obtain ⟨p, hp, he⟩ := hf 0 (Fin.cons 0 x)
  exact ⟨p, hp, fun t => by simpa only [Fin.update_cons_zero] using he t⟩

theorem CoordinatePolynomial.tail {n D : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : CoordinatePolynomial (n + 1) D f) (t : ℝ) :
    CoordinatePolynomial n D (fun x => f (Fin.cons t x)) := by
  intro i x
  obtain ⟨p, hp, he⟩ := hf i.succ (Fin.cons t x)
  exact ⟨p, hp, fun u => by simpa only [← Fin.cons_update] using he u⟩

theorem coordinatePolynomial_eval {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ D) :
    CoordinatePolynomial n D (fun x => MvPolynomial.eval x p) := by
  classical
  intro i x
  let e := Equiv.optionSubtypeNe i
  let q := MvPolynomial.rename e.symm p
  let P := MvPolynomial.optionEquivLeft ℝ {j : Fin n // j ≠ i} q
  let r := Polynomial.map (MvPolynomial.eval (fun j : {j : Fin n // j ≠ i} => x j)) P
  refine ⟨r, ?_, ?_⟩
  · calc
      r.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
      _ = p.degreeOf i := (MvPolynomial.degreeOf_eq_natDegree i p).symm
      _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p i
      _ ≤ D := hp
  · intro t
    change Polynomial.eval t (Polynomial.map (MvPolynomial.eval
      (fun j : {j : Fin n // j ≠ i} => x j)) (MvPolynomial.optionEquivLeft ℝ _ q)) = _
    rw [← MvPolynomial.optionEquivLeft_elim_eval, MvPolynomial.eval_rename]
    apply congrArg (fun v : Fin n → ℝ => MvPolynomial.eval v p)
    funext j
    by_cases hj : j = i
    · subst j
      simp [e]
    · simp [e, Equiv.optionSubtypeNe_symm_apply, hj]

end PolycyclicRecognition

end

end OAI
