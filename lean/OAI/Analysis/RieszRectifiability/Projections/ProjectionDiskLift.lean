import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Projection between subspace disks

Projecting a displacement orthogonally and translating its center carries a closed
disk into a disk of the same radius. The disk lift records this range constraint.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

def projectionDiskLift {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) : closedBall b ρ → closedBall a ρ :=
  fun u => ⟨a + P.orthogonalProjectionOnto ((u.val : Ambient d) - (b : Ambient d)), by
    change dist (a + P.orthogonalProjectionOnto ((u.val : Ambient d) - (b : Ambient d))) a ≤ ρ
    calc
      _ = ‖P.starProjection ((u.val : Ambient d) - (b : Ambient d))‖ := by
        rw [dist_eq_norm, add_sub_cancel_left]
        rfl
      _ ≤ ‖(u.val : Ambient d) - (b : Ambient d)‖ := P.norm_starProjection_apply_le _
      _ ≤ ρ := u.property⟩

theorem projectionDiskLift_sub {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) (u v : closedBall b ρ) :
    ((projectionDiskLift P Q a b ρ u).val : Ambient d) -
      ((projectionDiskLift P Q a b ρ v).val : Ambient d) =
        P.starProjection ((u.val : Ambient d) - (v.val : Ambient d)) := by
  change ((a : Ambient d) + P.starProjection ((u.val : Ambient d) - (b : Ambient d))) -
    ((a : Ambient d) + P.starProjection ((v.val : Ambient d) - (b : Ambient d))) = _
  calc
    _ = P.starProjection ((u.val : Ambient d) - (b : Ambient d)) -
        P.starProjection ((v.val : Ambient d) - (b : Ambient d)) := by abel
    _ = P.starProjection (((u.val : Ambient d) - (b : Ambient d)) -
        ((v.val : Ambient d) - (b : Ambient d))) := (map_sub _ _ _).symm
    _ = _ := by rw [sub_sub_sub_cancel_right]

theorem projectionDiskLift_lipschitz {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) : LipschitzWith 1 (projectionDiskLift P Q a b ρ) := by
  apply LipschitzWith.mk_one
  intro u v
  change ‖((projectionDiskLift P Q a b ρ u).val : Ambient d) -
    ((projectionDiskLift P Q a b ρ v).val : Ambient d)‖ ≤ dist u v
  rw [projectionDiskLift_sub]
  exact P.norm_starProjection_apply_le _

theorem projectionDiskLift_center {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    projectionDiskLift P Q a b ρ ⟨b, mem_closedBall_self hρ⟩ = ⟨a, mem_closedBall_self hρ⟩ := by
  apply Subtype.ext
  simp only [projectionDiskLift, sub_self, map_zero, add_zero]

end

end RieszRectifiability

end OAI
