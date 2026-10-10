import OAI.Analysis.IrrationalRotation.Model.PhaseBlocks
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.ProductScaleData

theorem exists_block_of_lt_prefixCount (p : ProductScaleData) (j : ℕ)
    {i : ℕ} (hi : i < p.prefixCount j) :
    ∃ s < j, i ∈ ProductPhases.consecutiveBlock p.m s := by
  induction j with
  | zero => simp [prefixCount] at hi
  | succ j ih =>
      by_cases hij : i < p.prefixCount j
      · obtain ⟨s, hs, his⟩ := ih hij
        exact ⟨s, Nat.lt_succ_of_lt hs, his⟩
      · refine ⟨j, Nat.lt_succ_self j, ?_⟩
        have hi' : i < p.prefixCount j + p.m j := by
          simpa only [prefixCount, Finset.sum_range_succ] using hi
        simpa only [ProductPhases.consecutiveBlock, Finset.mem_Ico, prefixCount]
          using And.intro (Nat.le_of_not_gt hij) hi'

end Invariant233.ProductScaleData

namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem coordinate_scale_bounds (S : ℕ → ℝ)
    (hblock : ∀ s, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      S i = (p.m s : ℝ) * p.K s)
    (j : ℕ) {i : ℕ} (hi : i < p.prefixCount (j + 1)) :
    0 < S i ∧ S i ≤ p.N j := by
  obtain ⟨s, hs, his⟩ := p.exists_block_of_lt_prefixCount (j + 1) hi
  rw [hblock s i his]
  exact ⟨mul_pos (by exact_mod_cast hp.m_pos s) (hp.real_K_pos s),
    hp.N_strictMono.monotone (Nat.lt_succ_iff.mp hs)⟩

theorem fin_coordinate_scale_bounds (S : ℕ → ℝ)
    (hblock : ∀ s, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      S i = (p.m s : ℝ) * p.K s)
    (j : ℕ) (i : Fin (p.prefixCount (j + 1))) :
    0 < S i ∧ S i ≤ p.N j :=
  hp.coordinate_scale_bounds S hblock j i.isLt

theorem fin_coordinate_scale_le_square (S : ℕ → ℝ)
    (hblock : ∀ s, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      S i = (p.m s : ℝ) * p.K s)
    (j : ℕ) (i : Fin (p.prefixCount (j + 1))) :
    S i ≤ (p.m j : ℝ) ^ 2 :=
  (hp.fin_coordinate_scale_bounds S hblock j i).2.trans (hp.N_le_square j)

end Invariant233.ProductScaleLaws

end

end OAI
