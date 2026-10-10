import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionDiskLift

namespace OAI

/-!
# Parameter maps under a change of plane

The disk lift and orthogonal projection transfer a parametrization to another
plane. Normal Lipschitz control and the distance between projections bound its
deviation from the identity parameter map.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def planeChangedParameterMap {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) (g : closedBall a ρ → Ambient d) : closedBall b ρ → Q :=
  fun v => Q.orthogonalProjectionOnto (g (projectionDiskLift P Q a b ρ v))

theorem planeChangedParameterMap_error_lipschitz {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (a : P) (b : Q) (ρ : ℝ)
    (g : closedBall a ρ → Ambient d) (L α : ℝ≥0)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ)) :
    LipschitzWith (L + α) (fun v : closedBall b ρ =>
      planeChangedParameterMap P Q a b ρ g v - v.val) := by
  let u := projectionDiskLift P Q a b ρ
  let N : closedBall b ρ → Ambient d :=
    fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g (u v))
  have hdecomp (v : closedBall a ρ) :
      g v = (v.val : Ambient d) + (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v) := by
    have hs : P.starProjection (g v) = (v.val : Ambient d) :=
      congrArg (fun w : P => (w : Ambient d)) (hcoordinates v)
    have h := (P.starProjection_add_starProjection_orthogonal (g v)).symm
    rwa [hs] at h
  apply LipschitzWith.of_dist_le_mul
  intro v w
  let z : Ambient d := (v.val : Ambient d) - (w.val : Ambient d)
  have hQz : Q.starProjection z = z :=
    Q.starProjection_eq_self_iff.mpr (Q.sub_mem v.val.property w.val.property)
  have hPz : ‖P.starProjection z - z‖ ≤ (α : ℝ) * ‖z‖ := by
    have h := ((P.starProjection - Q.starProjection).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg z))
    change ‖P.starProjection z - Q.starProjection z‖ ≤ (α : ℝ) * ‖z‖ at h
    rwa [hQz] at h
  have hgdiff : g (u v) - g (u w) = P.starProjection z + (N v - N w) := by
    calc
      _ = (((u v).val : Ambient d) - ((u w).val : Ambient d)) + (N v - N w) := by
        rw [hdecomp (u v), hdecomp (u w)]
        dsimp only [N]
        abel
      _ = _ := by rw [projectionDiskLift_sub]
  have hN : ‖N v - N w‖ ≤ (L : ℝ) * dist v w := by
    have hn : ‖N v - N w‖ ≤ (L : ℝ) * dist (u v) (u w) := hnormal.dist_le_mul (u v) (u w)
    have hu : dist (u v) (u w) ≤ dist v w := by
      simpa only [NNReal.coe_one, one_mul] using!
        (projectionDiskLift_lipschitz P Q a b ρ).dist_le_mul v w
    exact hn.trans (mul_le_mul_of_nonneg_left hu L.coe_nonneg)
  have heq : (Q.starProjection (g (u v)) - (v.val : Ambient d)) -
      (Q.starProjection (g (u w)) - (w.val : Ambient d)) =
        Q.starProjection (P.starProjection z - z) + Q.starProjection (N v - N w) := by
    calc
      _ = Q.starProjection (g (u v) - g (u w)) - z := by
        rw [map_sub]
        dsimp only [z]
        abel
      _ = Q.starProjection (P.starProjection z + (N v - N w)) - Q.starProjection z := by
        rw [hgdiff, hQz]
      _ = _ := by simp only [map_add, map_sub]; abel
  change ‖(Q.starProjection (g (u v)) - (v.val : Ambient d)) -
    (Q.starProjection (g (u w)) - (w.val : Ambient d))‖ ≤ _
  rw [heq, NNReal.coe_add]
  calc
    _ ≤ ‖Q.starProjection (P.starProjection z - z)‖ + ‖Q.starProjection (N v - N w)‖ :=
      norm_add_le _ _
    _ ≤ (α : ℝ) * ‖z‖ + (L : ℝ) * dist v w :=
      add_le_add ((Q.norm_starProjection_apply_le _).trans hPz)
        ((Q.norm_starProjection_apply_le _).trans hN)
    _ = ((L : ℝ) + (α : ℝ)) * dist v w := by
      have hz : ‖z‖ = dist v w := rfl
      rw [hz]
      ring

end

end RieszRectifiability

end OAI
