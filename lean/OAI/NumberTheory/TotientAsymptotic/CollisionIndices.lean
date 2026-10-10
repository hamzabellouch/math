import OAI.NumberTheory.TotientAsymptotic.CollisionCutoff
import OAI.NumberTheory.TotientAsymptotic.TailCutScale

namespace OAI

/-! Validity of every collision cutoff, uniformly over the retained indices. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma eventually_collision_indices : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, H ≤ m x → ∀ i ≤ R x H,
      H ≤ m x-i ∧ 2*collisionCutoff (m x-i) < m x-i ∧
        i+collisionCutoff (m x-i) < L x H := by
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp collisionCutoff_eventually_small
  filter_upwards [eventually_ge_atTop H₀, eventually_tail_cut_separated] with H hH hsep
  intro x hHm i hi
  have hh : H ≤ m x-i := by unfold R at hi; omega
  have hJ := hH₀ (m x-i) (hH.trans hh)
  have hmi : i ≤ m x := by unfold R at hi; omega
  refine ⟨hh, hJ, ?_⟩
  unfold L
  have hP := hsep.2.2.2
  omega

end TotientAsymptotic

end

end OAI
