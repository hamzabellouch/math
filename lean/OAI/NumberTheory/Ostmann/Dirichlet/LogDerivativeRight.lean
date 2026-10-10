import OAI.NumberTheory.Jacobsthal.Primes.ZetaPoleBounds
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open ArithmeticFunction DirichletCharacter
open scoped LSeries.notation BigOperators ComplexOrder
end Ostmann.Dirichlet

namespace Ostmann.Dirichlet
open ArithmeticFunction DirichletCharacter
open scoped LSeries.notation BigOperators

noncomputable def absoluteMangoldtTwo : ℝ :=
  ∑' n : ℕ, ‖LSeries.term ↗Λ (2 : ℂ) n‖

lemma absoluteMangoldtTwo_summable :
    Summable (fun n : ℕ => ‖LSeries.term ↗Λ (2 : ℂ) n‖) :=
  (LSeriesSummable_vonMangoldt (by norm_num : 1 < (2 : ℂ).re)).norm

lemma absoluteMangoldtTwo_nonneg : 0 ≤ absoluteMangoldtTwo :=
  tsum_nonneg (fun _ => norm_nonneg _)

lemma norm_log_derivative_re_ge_two {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ absoluteMangoldtTwo := by
  have hs1 : 1 < s.re := by linarith
  have htw := LSeriesSummable_twist_vonMangoldt χ hs1
  calc
    _ = ‖LSeries (↗χ * ↗Λ) s‖ := by
      rw [LSeries_twist_vonMangoldt_eq χ hs1,
        deriv_LFunction_eq_deriv_LSeries χ hs1, LFunction_eq_LSeries χ hs1]
      simp [neg_div]
    _ ≤ ∑' n, ‖LSeries.term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm htw.norm
    _ ≤ absoluteMangoldtTwo := by
      apply htw.norm.tsum_le_tsum _ absoluteMangoldtTwo_summable
      intro n
      have hcoeff : ‖(↗χ * ↗Λ) n‖ ≤ ‖(↗Λ n : ℂ)‖ := by
        simpa using mul_le_of_le_one_left (norm_nonneg (vonMangoldt n : ℂ))
          (χ.norm_le_one (n : ZMod q))
      exact (LSeries.norm_term_le s hcoeff).trans
        (LSeries.norm_term_le_of_re_le_re ↗Λ (by simpa using hs) n)

end Ostmann.Dirichlet

end OAI
