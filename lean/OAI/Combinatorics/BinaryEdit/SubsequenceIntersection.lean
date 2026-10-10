import OAI.Combinatorics.BinaryEdit.LCSCore

namespace OAI

namespace TreeEdit.BinaryLower

/-- Composing two common-subsequence loss bounds adds their costs. -/
theorem common_subsequence_compose {α : Type*} {x y z : List α} {m n : ℕ}
    (hxy : ∃ u : List α, u.Sublist x ∧ u.Sublist y ∧
      x.length + y.length ≤ m + 2 * u.length)
    (hyz : ∃ v : List α, v.Sublist y ∧ v.Sublist z ∧
      y.length + z.length ≤ n + 2 * v.length) :
    ∃ w : List α, w.Sublist x ∧ w.Sublist z ∧
      x.length + z.length ≤ m + n + 2 * w.length := by
  obtain ⟨u, hux, huy, hu⟩ := hxy
  obtain ⟨v, hvy, hvz, hv⟩ := hyz
  obtain ⟨w, hwu, hwv, hw⟩ := common_sublist_lower_bound huy hvy
  exact ⟨w, hwu.trans hux, hwv.trans hvz, by omega⟩

end TreeEdit.BinaryLower

end OAI
