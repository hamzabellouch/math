import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.PerturbedBallCoverage

namespace OAI

/-!
# Centered coverage for perturbed charts

Lipschitz perturbations of the identity cover balls centered at any parameter
with sufficient room in the domain. Applied to tangential projection, this gives
a disk covered by the portion of the surface inside a controlled ambient ball.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem centered_ball_covered_by_lipschitz_perturbation {X : Type*}
    [NormedAddCommGroup X] [CompleteSpace X]
    (c : X) (R : ℝ) (f : closedBall c R → X) (K : ℝ≥0) (hK : K < 1)
    (herr : LipschitzWith K (fun u => f u - u.val))
    (a : closedBall c R) (r : ℝ) (hr : 0 ≤ r) (hroom : dist a.val c + r ≤ R) :
    ∀ z ∈ closedBall (f a) ((1 - (K : ℝ)) * r),
      ∃ u : closedBall c R, dist u a ≤ r ∧ f u = z := by
  have hsub : closedBall a.val r ⊆ closedBall c R := by
    intro x hx
    have hx' : dist x a.val ≤ r := hx
    change dist x c ≤ R
    exact (dist_triangle x a.val c).trans (by linarith)
  let j : closedBall a.val r → closedBall c R := fun u => ⟨u.val, hsub u.property⟩
  let g : closedBall a.val r → X := fun u => f (j u) - f a + a.val
  have hdisp : ∀ u, dist (g u) u.val ≤ (K : ℝ) * r := by
    intro u
    have hid : g u - u.val = (f (j u) - (j u).val) - (f a - a.val) := by
      dsimp [g, j]
      abel
    rw [dist_eq_norm, hid]
    have h := (herr.dist_le_mul (j u) a).trans
      (mul_le_mul_of_nonneg_left (show dist (j u) a ≤ r from u.property) K.coe_nonneg)
    simpa only [dist_eq_norm] using! h
  have hLip : LipschitzWith K (fun u : closedBall a.val r => g u - u.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hid : (g u - u.val) - (g v - v.val) =
        (f (j u) - (j u).val) - (f (j v) - (j v).val) := by
      dsimp [g, j]
      abel
    rw [dist_eq_norm, hid]
    simpa only [dist_eq_norm] using! herr.dist_le_mul (j u) (j v)
  intro z hz
  have hz' : z - f a + a.val ∈ closedBall a.val (r - (K : ℝ) * r) := by
    have hd : dist (z - f a + a.val) a.val = dist z (f a) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [mem_closedBall, hd]
    have hzr : dist z (f a) ≤ (1 - (K : ℝ)) * r := hz
    nlinarith
  obtain ⟨u, hu⟩ := closedBall_covered_by_lipschitz_perturbation a.val r ((K : ℝ) * r)
    hr K hK g hdisp hLip hz'
  refine ⟨j u, u.property, ?_⟩
  change f (j u) - f a + a.val = z - f a + a.val at hu
  exact sub_left_inj.mp (add_right_cancel hu)

theorem centered_projection_disk_in_surface_ball {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (c : P) (R : ℝ)
    (H : closedBall c R → Ambient d) (K L : ℝ≥0)
    (hK : (K : ℝ) ≤ 1 / 2) (hL : (L : ℝ) ≤ 1 / 2)
    (hError : LipschitzWith K (fun u => P.orthogonalProjectionOnto (H u) - u.val))
    (hNormal : LipschitzWith L (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (H u)))
    (a : closedBall c R) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hroom : dist a.val c + 2 * ρ ≤ R)
    (surface : Set (Ambient d)) (hSurface : ∀ u, dist u a ≤ 2 * ρ → H u ∈ surface) :
    closedBall (P.orthogonalProjectionOnto (H a)) ρ ⊆
      P.orthogonalProjectionOnto '' (surface ∩ closedBall (H a) (2 * ρ)) := by
  have hKone : K < 1 := by
    have hreal : (K : ℝ) < 1 := by linarith
    exact_mod_cast hreal
  intro z hz
  have hz' : z ∈ closedBall (P.orthogonalProjectionOnto (H a)) ((1 - (K : ℝ)) * (2 * ρ)) := by
    have hdist : dist z (P.orthogonalProjectionOnto (H a)) ≤ ρ := hz
    change dist z (P.orthogonalProjectionOnto (H a)) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hK hρ]
  obtain ⟨u, hua, hu⟩ := centered_ball_covered_by_lipschitz_perturbation c R
    (fun v => P.orthogonalProjectionOnto (H v)) K hKone hError a (2 * ρ)
    (by positivity) hroom z hz'
  change P.orthogonalProjectionOnto (H u) = z at hu
  refine ⟨H u, ⟨hSurface u hua, ?_⟩, hu⟩
  have hp : ‖P.starProjection (H u - H a)‖ ≤ ρ := by
    rw [map_sub]
    change dist (P.orthogonalProjectionOnto (H u)) (P.orthogonalProjectionOnto (H a)) ≤ ρ
    rw [hu]
    exact hz
  have hn := hNormal.dist_le_mul u a
  rw [dist_eq_norm, ← map_sub] at hn
  have ht := norm_add_le (P.starProjection (H u - H a))
    ((Pᗮ : Submodule ℝ (Ambient d)).starProjection (H u - H a))
  rw [P.starProjection_add_starProjection_orthogonal] at ht
  change dist (H u) (H a) ≤ 2 * ρ
  rw [dist_eq_norm]
  have hnr : (L : ℝ) * dist u a ≤ ρ := by
    have hb := mul_le_mul_of_nonneg_left hua L.coe_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hL hρ]
  linarith

end

end RieszRectifiability

end OAI
