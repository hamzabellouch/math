import OAI.NumberTheory.Jacobsthal.Estimates.PrincipalLogPower

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem all_character_log_power (A M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), (q:ℝ) ≤ (Real.log X)^A →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)‖ ≤ K*X/(Real.log X)^M := by
  classical
  obtain ⟨C,hC,hNon⟩ := sharp_character_log_power A M hA hM
  obtain ⟨D,hD,hPrin⟩ := principal_character_log_power A M hA hM
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [hNon,hPrin,eventually_ge_atTop (3:ℝ)] with X hNon hPrin hX
  intro q _ chi hq
  have hXp : 0 < X := by linarith
  have hLp : 0 < Real.log X := Real.log_pos (by linarith)
  have hcb : C*X/(Real.log X)^M ≤ (C+D)*X/(Real.log X)^M :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hXp.le) (Real.rpow_nonneg hLp.le _)
  have hdb : D*X/(Real.log X)^M ≤ (C+D)*X/(Real.log X)^M :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hXp.le) (Real.rpow_nonneg hLp.le _)
  by_cases hc : chi=1
  · subst chi
    simpa using! (hPrin q hq).trans hdb
  · simpa [hc] using! (hNon q chi hc hq).trans hcb

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
