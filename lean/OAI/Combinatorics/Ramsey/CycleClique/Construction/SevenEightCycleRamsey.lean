import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK6
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK7
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertifiedRamseyReduction

namespace OAI

/-! The seven- and eight-cycle main clauses, with all finite obstructions
excluded by finite certificates. -/

namespace CycleClique.Construction
theorem certificateCoverageAt_six : CertificateCoverageAt 6 := by
  intro t ht htk _ _
  interval_cases t using ht, htk
  · exact CertifiedCoverage.coverage_k6_t3
  · exact CertifiedCoverage.coverage_k6_t4
  · exact CertifiedCoverage.coverage_k6_t5
  · exact CertifiedCoverage.coverage_k6_t6

theorem certificateCoverageAt_seven : CertificateCoverageAt 7 := by
  intro t ht htk _ _
  interval_cases t using ht, htk
  · exact CertifiedCoverage.coverage_k7_t3
  · exact CertifiedCoverage.coverage_k7_t4
  · exact CertifiedCoverage.coverage_k7_t5
  · exact CertifiedCoverage.coverage_k7_t6
  · exact CertifiedCoverage.coverage_k7_t7

theorem cycle_clique_seven (hCE : CEAlphaTwo) {n : ℕ} (hn : 3 ≤ n) (hnm : n ≤ 7) :
    IsRamseyNumber 7 n (6 * (n - 1) + 1) :=
  isRamseyNumber_of_certificate_coverage hCE (by omega) hn hnm certificateCoverageAt_six

theorem cycle_clique_eight (hCE : CEAlphaTwo) {n : ℕ} (hn : 3 ≤ n) (hnm : n ≤ 8) :
    IsRamseyNumber 8 n (7 * (n - 1) + 1) :=
  isRamseyNumber_of_certificate_coverage hCE (by omega) hn hnm certificateCoverageAt_seven

end CycleClique.Construction

end OAI
