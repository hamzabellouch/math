import OAI.NumberTheory.TotientAsymptotic.FordTruncatedRows
import OAI.NumberTheory.TotientAsymptotic.TerminalPrimeGap

namespace OAI

/-! The last two boundaries of a truncated Ford simplex supply a strict
prime gap and the row system required by the residual counting bridge. -/
noncomputable section
namespace TotientAsymptotic

lemma fixed_simplex_terminal_data {x : ℝ} {H n : ℕ}
    (hs : fordSimplexCondition x H n) (hL : 3 ≤ m x-H) :
    ∃ j : ℕ, (j=m x-H ∨ j=m x-H-1) ∧
      j ≤ n.primeFactorsList.length ∧
      fordPrime n j < fordPrime n (j-1) ∧
      2 < fordPrimeCoordinate n j ∧
      ∀ i < j,fordRowSum j (fordPrimeCoordinate n) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate n i) := by
  have hrows := ford_simplex_truncated_rows hs
  have hrow : fordRowSum (m x-H) (fordPrimeCoordinate n) (m x-H-2) ≤
      xi x (m x-H-2)*fordPrimeCoordinate n (m x-H-2) := by
    simpa only [ite_eq_right (show m x-H-2≠0 by omega)] using
      hrows (m x-H-2) (by omega)
  obtain ⟨j,hlo,hhi,hgap,he⟩ := terminal_strict_prime_gap hL
    (by linarith only [hs.1]) hrow
  have hj : j=m x-H ∨ j=m x-H-1 := by omega
  have hlarge : 2 < fordPrimeCoordinate n j := by rw [he]; exact hs.1
  have hlen : j < n.primeFactorsList.length := by
    apply fordPrime_index_of_doubleLog_pos
    rw [←fordPrimeCoordinate_eq_raw_of_pos (by linarith only [hlarge])]
    linarith only [hlarge]
  refine ⟨j,hj,hlen.le,hgap,hlarge,?_⟩
  intro i hi
  exact (fordRowSum_truncate hhi _ (fun _=>le_max_left _ _)).trans (hrows i (by omega))

end TotientAsymptotic

end

end OAI
