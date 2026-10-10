import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.PrimitiveTransfer
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaLogDerivative

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

theorem exists_principal_all_height_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
      1 < s.re → s.re ≤ 2 →
      (-logDeriv (DirichletCharacter.LFunctionTrivChar q) s).re ≤
        C * modulusHeight q s.im + (1 / (s - 1)).re := by
  obtain ⟨C, hC, hb⟩ := exists_zeta_all_height_log_bound
  refine ⟨C + 1, by positivity, ?_⟩
  intro q _ s hs hs2
  have h := principal_neg_real_log_derivative_le q hs
  have hz := hb s hs hs2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlogq := Real.log_nonneg hq
  have hlogt : 0 ≤ Real.log (|s.im| + 6) :=
    Real.log_nonneg (by have := abs_nonneg s.im; linarith)
  unfold modulusHeight
  nlinarith only [h, hz, mul_nonneg hC.le hlogq, hlogt]

end Ostmann.Dirichlet

end OAI
