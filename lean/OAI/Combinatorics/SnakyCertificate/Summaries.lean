import OAI.Combinatorics.SnakyCertificate.Cache

namespace OAI

namespace SnakyCertificate.Check

theorem cache_summary_557 :
    (denote cache_557).A = {(-1, 0)} ∧
    (denote cache_557).H.card = 118 ∧
    (denote cache_557).height = 19 := by
  decide +kernel

theorem cache_omits_557 : ∀ p ∈ cache_557.H, ¬(p.1 ≤ -3 ∧ p.2 ≤ -2) := by
  decide +kernel

theorem cache_summary_595 :
    (denote cache_595).A = {(-1, 0)} ∧
    (denote cache_595).H.card = 222 ∧
    (denote cache_595).height = 27 := by
  decide +kernel

theorem cache_omits_595 : ∀ p ∈ cache_595.H, ¬(p.1 = -2 ∧ p.2 ≤ -2) := by
  decide +kernel

theorem cache_summary_603 :
    (denote cache_603).A = {(-1, 0)} ∧
    (denote cache_603).H.card = 275 ∧
    (denote cache_603).height = 27 := by
  decide +kernel

theorem cache_omits_603 : ∀ p ∈ cache_603.H, ¬(p.1 ≤ -3 ∧ p.2 = 0) := by
  decide +kernel

theorem cache_summary_615 :
    (denote cache_615).A = {(1, 0)} ∧
    (denote cache_615).H.card = 686 ∧
    (denote cache_615).height = 34 := by
  decide +kernel

theorem cache_omits_615 : ∀ p ∈ cache_615.H, ¬(p = (1, -1)) := by
  decide +kernel

theorem output_of_row_eq (i : ℕ) (d : ListRow) (p : Cell) (size height : ℕ)
    (omitted : Set Cell) (he : rowAt i = denote d)
    (summary : (denote d).A = {p} ∧ (denote d).H.card = size ∧
      (denote d).height = height)
    (omits : ∀ q ∈ d.H, q ∉ omitted) : Output i p size height omitted := by
  unfold Output
  rw [he]
  refine ⟨summary.1, summary.2.1, summary.2.2, ?_⟩
  apply Set.disjoint_left.mpr
  intro q hq hq'
  exact omits q (List.mem_toFinset.mp hq) hq'

end SnakyCertificate.Check

end OAI
