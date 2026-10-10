import Mathlib
import OAI.Combinatorics.KMedian.Machines.RawCSP

namespace OAI

section Inline_PCPTablePromises
namespace MetricKMedian.PCP.Compiler.CSPTable
open scoped Classical

variable {A V E : Type} [Fintype A] [DecidableEq A] [Fintype V] [Fintype E]
variable {s : CSPTable A} {C : BinaryCSP V E A}
omit [Fintype A] [DecidableEq A] [Fintype V] in
lemma Represents.rejection (r : s.Represents C) (h : s.WellFormed) (a : Fin s.1.length → A) :
    (s.csp h).rejection a=C.rejection (a ∘ r.vertex) := by
  rw [r.csp_eq h]
  exact BinaryCSP.reindex_rejection _ _ _ _
omit [Fintype A] [DecidableEq A] [Fintype V] [Fintype E] in
lemma Represents.satisfies (r : s.Represents C) (h : s.WellFormed) :
    (∃ a, (s.csp h).Satisfies a) ↔ ∃ a, C.Satisfies a := by
  rw [r.csp_eq h]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a ∘ r.vertex,(C.reindex_satisfies _ _ _).mp ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a ∘ r.vertex.symm,C.reindex_complete _ _ _ ha⟩
omit [Fintype A] [DecidableEq A] [Fintype V] in
lemma Represents.gap (r : s.Represents C) (h : s.WellFormed) (δ : ℝ)
    (hg : ∀ a, δ≤C.rejection a) : ∀ a, δ≤(s.csp h).rejection a := by
  intro a
  rw [r.rejection h]
  exact hg _
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPTablePromises

end OAI
