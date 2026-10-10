import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

namespace OAI

namespace Laughlin.PairDiagonal
open Polynomial
open scoped Polynomial.Bivariate

abbrev Poly := Polynomial (Polynomial ℂ)
noncomputable def diagonal : Poly := X - C (X : Polynomial ℂ)

theorem eval_swap_diagonal (p : Poly) :
    (Bivariate.swap p).eval (X : Polynomial ℂ) = p.eval X := by
  have he : (evalRingHom (X : Polynomial ℂ)).comp Bivariate.swap.toRingHom =
      evalRingHom (X : Polynomial ℂ) := by
    ext <;> simp [Bivariate.swap_X, Bivariate.swap_Y, Bivariate.swap_C_C]
  exact congrArg (fun f : Poly →+* Polynomial ℂ => f p) he

theorem antisymmetric_eval_zero (p : Poly) (ha : Bivariate.swap p = -p) :
    p.eval (X : Polynomial ℂ) = 0 := by
  have he := eval_swap_diagonal p
  rw [ha, eval_neg] at he
  have hz : (2 : ℂ) • p.eval (X : Polynomial ℂ) = 0 := by
    simp only [two_smul]
    calc
      _ = -p.eval (X : Polynomial ℂ) + p.eval X :=
        congrArg (fun z : Polynomial ℂ => z+p.eval X) he.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left two_ne_zero

theorem swap_diagonal : Bivariate.swap diagonal = -diagonal := by
  simp only [diagonal, map_sub, Bivariate.swap_X, Bivariate.swap_Y]
  ring

theorem cube_dvd_of_antisymmetric_first_jet (p : Poly)
    (ha : Bivariate.swap p = -p) (hj : p.derivative.eval (X : Polynomial ℂ) = 0) :
    diagonal^3 ∣ p := by
  have hd : diagonal ∣ p := by
    apply dvd_iff_isRoot.mpr
    exact antisymmetric_eval_zero p ha
  obtain ⟨g,hg⟩ := hd
  have hg0 : g.eval (X : Polynomial ℂ) = 0 := by
    rw [hg, derivative_mul] at hj
    simpa [diagonal] using hj
  have hdg : diagonal ∣ g := by
    apply dvd_iff_isRoot.mpr
    exact hg0
  obtain ⟨h,hh⟩ := hdg
  have hp : p = diagonal^2*h := by rw [hg,hh]; ring
  have hb : diagonal ≠ 0 := by
    exact X_sub_C_ne_zero (X : Polynomial ℂ)
  have hanti : Bivariate.swap h = -h := by
    rw [hp, map_mul, map_pow, swap_diagonal] at ha
    have hsq : (-diagonal)^2 = diagonal^2 := by ring
    rw [hsq] at ha
    apply mul_left_cancel₀ (pow_ne_zero 2 hb)
    calc
      _ = -(diagonal^2*h) := ha
      _ = _ := by ring
  have hdh : diagonal ∣ h := by
    apply dvd_iff_isRoot.mpr
    exact antisymmetric_eval_zero h hanti
  obtain ⟨k,hk⟩ := hdh
  refine ⟨k, ?_⟩
  rw [hp,hk]
  ring

end Laughlin.PairDiagonal

end OAI
