import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Ring
import OAI.Analysis.Laughlin.EnergyNonnegative

namespace OAI

namespace Laughlin

theorem bracket_swap {N : ℕ} (i j : Fin N) : bracket j i = -bracket i j := by
  unfold bracket
  ring

theorem bracket_ne_zero {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    bracket i j ≠ 0 := by
  intro h
  let f : SpinorVariables N → ℂ := fun kb =>
    if (kb.1 = i ∧ kb.2 = false) ∨ (kb.1 = j ∧ kb.2 = true) then 1 else 0
  have := congrArg (MvPolynomial.eval f) h
  have hji : j ≠ i := Ne.symm hij
  simp [bracket, f, hij, hji] at this

theorem laughlinPolynomial_ne_zero (N : ℕ) : laughlinPolynomial N ≠ 0 := by
  classical
  unfold laughlinPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split_ifs with hij
  · exact pow_ne_zero 3 (bracket_ne_zero (ne_of_lt hij))
  · exact one_ne_zero

theorem bracket_cube_dvd_laughlin {N : ℕ} {i j : Fin N} (hij : i < j) :
    bracket i j ^ 3 ∣ laughlinPolynomial N := by
  classical
  unfold laughlinPolynomial
  have h₁ : bracket i j ^ 3 ∣ ∏ k : Fin N, if i < k then bracket i k ^ 3 else 1 := by
    simpa [hij] using
    (Finset.dvd_prod_of_mem (fun j => if i < j then bracket i j ^ 3 else 1)
      (Finset.mem_univ j))
  exact h₁.trans
    (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin N, if i < j then bracket i j ^ 3 else 1)
      (Finset.mem_univ i))

end Laughlin

end OAI
