import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK5
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK6
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK7
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK8
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK9
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK10
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK11
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK12
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK13
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK14
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK15
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK16
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CoverageK17

namespace OAI

/-! Exact coverage of all 42 finite canonical domains by checked certificates. -/

namespace CycleClique.Construction
theorem checked_certificate_coverage {k t : ℕ}
    (hk : 5 ≤ k) (hk' : k ≤ 17) (ht : 3 ≤ t) (htk : t ≤ k)
    (ht' : t ≤ 8) (hhalf : k / 2 ≤ t) :
    ∀ P ∈ pathPatterns t (k - t), HasCheckedCertificate k t P := by
  interval_cases k using hk, hk'
  · interval_cases t using ht, ht'
    · exact CertifiedCoverage.coverage_k5_t3
    · exact CertifiedCoverage.coverage_k5_t4
    · exact CertifiedCoverage.coverage_k5_t5
    · omega
    · omega
    · omega
  · interval_cases t using ht, ht'
    · exact CertifiedCoverage.coverage_k6_t3
    · exact CertifiedCoverage.coverage_k6_t4
    · exact CertifiedCoverage.coverage_k6_t5
    · exact CertifiedCoverage.coverage_k6_t6
    · omega
    · omega
  · interval_cases t using ht, ht'
    · exact CertifiedCoverage.coverage_k7_t3
    · exact CertifiedCoverage.coverage_k7_t4
    · exact CertifiedCoverage.coverage_k7_t5
    · exact CertifiedCoverage.coverage_k7_t6
    · exact CertifiedCoverage.coverage_k7_t7
    · omega
  · interval_cases t using ht, ht'
    · omega
    · exact CertifiedCoverage.coverage_k8_t4
    · exact CertifiedCoverage.coverage_k8_t5
    · exact CertifiedCoverage.coverage_k8_t6
    · exact CertifiedCoverage.coverage_k8_t7
    · exact CertifiedCoverage.coverage_k8_t8
  · interval_cases t using ht, ht'
    · omega
    · exact CertifiedCoverage.coverage_k9_t4
    · exact CertifiedCoverage.coverage_k9_t5
    · exact CertifiedCoverage.coverage_k9_t6
    · exact CertifiedCoverage.coverage_k9_t7
    · exact CertifiedCoverage.coverage_k9_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k10_t5
    · exact CertifiedCoverage.coverage_k10_t6
    · exact CertifiedCoverage.coverage_k10_t7
    · exact CertifiedCoverage.coverage_k10_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k11_t5
    · exact CertifiedCoverage.coverage_k11_t6
    · exact CertifiedCoverage.coverage_k11_t7
    · exact CertifiedCoverage.coverage_k11_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k12_t6
    · exact CertifiedCoverage.coverage_k12_t7
    · exact CertifiedCoverage.coverage_k12_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k13_t6
    · exact CertifiedCoverage.coverage_k13_t7
    · exact CertifiedCoverage.coverage_k13_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k14_t7
    · exact CertifiedCoverage.coverage_k14_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k15_t7
    · exact CertifiedCoverage.coverage_k15_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k16_t8
  · interval_cases t using ht, ht'
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact CertifiedCoverage.coverage_k17_t8

end CycleClique.Construction

end OAI
