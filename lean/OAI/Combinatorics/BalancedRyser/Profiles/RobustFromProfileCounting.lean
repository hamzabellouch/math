import OAI.Combinatorics.BalancedRyser.Probability.RobustNearCover
import OAI.Combinatorics.BalancedRyser.Selection.OccupancyClassVisibility

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem robustDeletion_of_profileCounting
    (hcounting : ProfileCountingResult.{u}) : RobustDeletionResult.{u} := by
  intro k hk K _hK
  have hTV := fun τ hτ => robustMultiplicity_of_profileCounting hcounting k hk K τ hτ
  have hOcc := fun lam η hlam hη =>
    robustOccupancy_of_profileCounting hcounting k hk K lam hlam η hη
  exact ⟨hTV, hOcc,
    fun δ hδ => robust_nearCover_of_profileCounting hcounting k hk K hTV hOcc δ hδ⟩

end Balanced

end OAI
