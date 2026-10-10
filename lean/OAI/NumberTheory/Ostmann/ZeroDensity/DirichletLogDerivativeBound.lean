import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # A uniform Euler-series bound for real arguments

This part uses proved Mathlib theorems only: the continued zeta pole, the
Euler logarithmic derivative, and the norm bound for Dirichlet characters.
-/

namespace Ostmann

open scoped BigOperators ComplexOrder
open Complex LSeries

theorem residue_one_eq_vonMangoldt :
    ArithmeticFunction.vonMangoldt.residueClass (0 : ZMod 1) = ArithmeticFunction.vonMangoldt := by
  funext n
  simp [ArithmeticFunction.vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) 0]

theorem exists_vonMangoldt_series_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)‖ ≤ 1 / (s - 1) + C := by
  let F := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (0 : ZMod 1)
  have hcont : ContinuousOn (fun s : ℝ => F (s : ℂ)) (Set.Icc 1 2) := by
    apply ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (0 : ZMod 1) |>.comp
      Complex.continuous_ofReal.continuousOn
    intro s hs
    exact hs.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro s hs hs2
  have hunit : IsUnit (0 : ZMod 1) := by
    rw [Subsingleton.elim (0 : ZMod 1) 1]
    exact isUnit_one
  have heq := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux hunit
    (show (s : ℂ) ∈ {z : ℂ | 1 < z.re} by exact hs)
  rw [residue_one_eq_vonMangoldt] at heq
  simp only [Nat.totient_one, Nat.cast_one, inv_one] at heq
  have he : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) =
      F (s : ℂ) + 1 / ((s : ℂ) - 1) := by
    change F (s : ℂ) = _ at heq
    rw [heq]
    ring
  have hnorm : ‖1 / ((s : ℂ) - 1)‖ = 1 / (s - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [he]
  have hb := norm_add_le (F (s : ℂ)) (1 / ((s : ℂ) - 1))
  rw [hnorm] at hb
  have hg := hM s ⟨hs.le, hs2⟩
  have hMabs := le_abs_self M
  linarith

theorem dirichlet_logDerivative_le_vonMangoldt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℝ) (hs : 1 < s) :
    ‖deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
      DirichletCharacter.LFunction χ (s : ℂ)‖ ≤
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)‖ := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs' : 1 < (s : ℂ).re := hs
  have ha : LSeriesSummable a (s : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs'
  have ht := χ.LSeriesSummable_twist_vonMangoldt hs'
  have he := χ.LSeries_twist_vonMangoldt_eq hs'
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs', ← χ.LFunction_eq_LSeries hs'] at he
  have hn (n : ℕ) : ‖LSeries.term (fun n => χ n * a n) (s : ℂ) n‖ ≤
      ‖LSeries.term a (s : ℂ) n‖ := by
    apply LSeries.norm_term_le
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hr (n : ℕ) : ‖LSeries.term a (s : ℂ) n‖ = (LSeries.term a (s : ℂ) n).re := by
    have hp : (0 : ℂ) ≤ a n := by
      change (0 : ℂ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ)
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hh := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg hp s))
    simpa only [Complex.ofReal_re] using hh.symm
  calc
    _ = ‖LSeries (fun n => χ n * a n) (s : ℂ)‖ := by
      change LSeries (fun n => χ n * a n) (s : ℂ) = _ at he
      rw [he]
      simp only [neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (fun n => χ n * a n) (s : ℂ) n‖ := norm_tsum_le_tsum_norm ht.norm
    _ ≤ ∑' n, ‖LSeries.term a (s : ℂ) n‖ := ht.norm.tsum_le_tsum hn ha.norm
    _ = (LSeries a (s : ℂ)).re := by simp_rw [hr]; exact (Complex.re_tsum ha).symm
    _ ≤ ‖LSeries a (s : ℂ)‖ := Complex.re_le_norm _

theorem exists_dirichlet_logDerivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (s : ℝ), 1 < s → s ≤ 2 →
      ‖deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
        DirichletCharacter.LFunction χ (s : ℂ)‖ ≤ 1 / (s - 1) + C := by
  obtain ⟨C, hC, hbound⟩ := exists_vonMangoldt_series_bound
  refine ⟨C, hC, ?_⟩
  intro q hq χ s hs hs2
  exact (dirichlet_logDerivative_le_vonMangoldt χ s hs).trans (hbound s hs hs2)

end Ostmann

end OAI
