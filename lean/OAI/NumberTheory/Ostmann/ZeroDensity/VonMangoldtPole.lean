import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletLogDerivativeBound

namespace OAI

/-! # The bounded remainder at the pole of the von Mangoldt series -/

namespace Ostmann

open scoped BigOperators ComplexOrder
open Complex LSeries

theorem exists_vonMangoldt_pole_error :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) -
        (1 / (s - 1) : ℝ)‖ ≤ C := by
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
  have he : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) -
      (1 / (s - 1) : ℝ) = F (s : ℂ) := by
    change F (s : ℂ) = _ at heq
    rw [heq]
    push_cast
    ring
  rw [he]
  have hb := hM s ⟨hs.le, hs2⟩
  linarith [le_abs_self M]

end Ostmann

end OAI
