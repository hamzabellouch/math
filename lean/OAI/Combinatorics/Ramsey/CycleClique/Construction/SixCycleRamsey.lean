import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK5
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertifiedRamseyReduction

namespace OAI

/-! The full six-cycle main clause, with its seven finite obstructions
excluded by finite certificates. -/

namespace CycleClique.Construction
theorem certificateCoverageAt_five : CertificateCoverageAt 5 := by
  intro t ht htk _ _
  interval_cases t using ht, htk
  · exact CertifiedCoverage.coverage_k5_t3
  · exact CertifiedCoverage.coverage_k5_t4
  · exact CertifiedCoverage.coverage_k5_t5

theorem cycle_clique_six (hCE : CEAlphaTwo) {n : ℕ} (hn : 3 ≤ n) (hnm : n ≤ 6) :
    IsRamseyNumber 6 n (5 * (n - 1) + 1) :=
  isRamseyNumber_of_certificate_coverage hCE (by omega) hn hnm certificateCoverageAt_five

end CycleClique.Construction

end OAI
