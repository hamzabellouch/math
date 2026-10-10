import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Projection bounds for chart residuals

A Lipschitz bound on the displacement residual controls the tangential coordinate
error of a perturbed chart. The normal component inherits the sum of this bound
and the original normal Lipschitz constant, by contractivity of orthogonal projection.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem projected_chart_error_lipschitz_of_residual {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (D : Set P) (g : D → Ambient d)
    (T : Ambient d → Ambient d) (A : ℝ) (hA : 0 ≤ A)
    (hcoords : ∀ u, P.orthogonalProjectionOnto (g u) = u.val)
    (hres : ∀ u v, ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤ A * dist u v) :
    LipschitzWith (Real.toNNReal A) (fun u => P.orthogonalProjectionOnto (T (g u)) - u.val) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.coe_toNNReal _ hA, dist_eq_norm]
  change ‖(P.starProjection (T (g u)) - (u.val : Ambient d)) -
    (P.starProjection (T (g v)) - (v.val : Ambient d))‖ ≤ _
  have hpu : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun w : P => (w : Ambient d)) (hcoords u)
  have hpv : P.starProjection (g v) = (v.val : Ambient d) :=
    congrArg (fun w : P => (w : Ambient d)) (hcoords v)
  have hid : (P.starProjection (T (g u)) - (u.val : Ambient d)) -
      (P.starProjection (T (g v)) - (v.val : Ambient d)) =
      P.starProjection ((T (g u) - T (g v)) - (g u - g v)) := by
    rw [map_sub, map_sub, map_sub, hpu, hpv]
    abel
  rw [hid]
  exact (P.norm_starProjection_apply_le _).trans (hres u v)

theorem normal_chart_lipschitz_of_residual {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (D : Set P) (g : D → Ambient d)
    (T : Ambient d → Ambient d) (A : ℝ) (hA : 0 ≤ A) (L : ℝ≥0)
    (hNormal : LipschitzWith L (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g u)))
    (hres : ∀ u v, ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤ A * dist u v) :
    LipschitzWith (Real.toNNReal (A + L))
      (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (T (g u))) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, ← map_sub]
  have hb := hNormal.dist_le_mul u v
  rw [dist_eq_norm, ← map_sub] at hb
  let e := (T (g u) - T (g v)) - (g u - g v)
  have hid : T (g u) - T (g v) = e + (g u - g v) := by dsimp [e]; abel
  calc
    _ ≤ ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection e‖ +
        ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (g u - g v)‖ := by
      rw [hid, map_add]
      exact norm_add_le _ _
    _ ≤ ‖e‖ + (L : ℝ) * dist u v :=
      add_le_add ((Pᗮ : Submodule ℝ (Ambient d)).norm_starProjection_apply_le e) hb
    _ ≤ (A + L) * dist u v := by have h := hres u v; change ‖e‖ ≤ _ at h; nlinarith

end

end RieszRectifiability

end OAI
