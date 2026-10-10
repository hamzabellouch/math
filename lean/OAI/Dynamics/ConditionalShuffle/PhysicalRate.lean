import OAI.Dynamics.ConditionalShuffle.Rates

namespace OAI

noncomputable section
namespace Revealed.Physical
open scoped Classical
open Thorp Thorp.Conditional Revealed.Split Revealed.Instrument Revealed.Disintegration
variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]

lemma block_weighted_cost (d t : ℕ) (e : Outside ι α (Position d))
    (c : (Equiv.Perm α → ℝ) → ℝ) :
    (∑ p, probability (block (instrument d) t) e p * c (kernel (block (instrument d) t) e p)) =
      ∑ p, marginal (frameJoint (sectionFrame e) t) p * c (frameKernel (sectionFrame e) t p) := by
  have h := weighted_conditional_map (observed (instrument d) e t)
    (groupRun (instrument d) e t) (fullPath e) (fullPath_injective e) c
  simp_rw [physical_path_frame, physical_group_frame] at h
  simpa only [probability, kernel, joint, block, frameKernel, frameJoint, physical_group_frame] using h.symm

lemma block_discarded_le (d : ℕ) (e : Outside ι (Position (d + 1 + 2)) (Position (d + 2 + 2))) :
    (∑ p, probability (block (instrument (d+2+2)) (400*(d+2+2))) e p *
      Trim.discarded (Block.embedding (Block.eightEquiv d))
        (kernel (block (instrument (d+2+2)) (400*(d+2+2))) e p)) ≤ 16 * conditionalRate d := by
  rw [block_weighted_cost]
  exact average_discarded_le d (sectionFrame e)

end Revealed.Physical

end

end OAI
