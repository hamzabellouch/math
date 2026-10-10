import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionPieceParameterization

namespace OAI

/-!
# Noncollapsing projections of pairwise plane approximations

A contraction bounded below on an approximating plane separates nearby points
up to the plane-fitting error. Under a quantitative smallness condition, this
separation yields a Lipschitz ball map covering a set with pairwise plane fits.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped NNReal

theorem projection_lower_bound_of_pairwise_plane {d e : ℕ}
    (T : Ambient d →L[ℝ] Ambient e) (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (x y : Ambient d) (ε κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖)
    (hx : infDist x (S : Set (Ambient d)) ≤ ε * dist x y)
    (hy : infDist y (S : Set (Ambient d)) ≤ ε * dist x y)
    (hlower : ∀ v ∈ S.direction, κ * ‖v‖ ≤ ‖T v‖) :
    (κ - 2 * ε * (κ + 1)) * dist x y ≤ dist (T x) (T y) := by
  let sx : Ambient d := orthogonalProjection S x
  let sy : Ambient d := orthogonalProjection S y
  let w := sx - sy
  let a := (x - y) - w
  have hw : w ∈ S.direction :=
    AffineSubspace.vsub_mem_direction (orthogonalProjection_mem x) (orthogonalProjection_mem y)
  have ha : ‖a‖ ≤ 2 * ε * dist x y := by
    have hid : a = (x - sx) - (y - sy) := by dsimp [a, w]; abel
    calc
      _ = ‖(x - sx) - (y - sy)‖ := by rw [hid]
      _ ≤ ‖x - sx‖ + ‖y - sy‖ := norm_sub_le _ _
      _ = infDist x (S : Set (Ambient d)) + infDist y (S : Set (Ambient d)) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact congrArg₂ (· + ·) (dist_orthogonalProjection_eq_infDist S x)
          (dist_orthogonalProjection_eq_infDist S y)
      _ ≤ _ := by linarith
  have hsplit : x - y = w + a := by dsimp [a]; abel
  have hdist : dist x y ≤ ‖w‖ + ‖a‖ := by
    rw [dist_eq_norm, hsplit]
    exact norm_add_le _ _
  have hTw : ‖T w‖ ≤ dist (T x) (T y) + ‖a‖ := by
    have hw' : w = (x - y) - a := by dsimp [a]; abel
    calc
      _ = ‖T (x - y) - T a‖ := by rw [hw', map_sub]
      _ ≤ ‖T (x - y)‖ + ‖T a‖ := norm_sub_le _ _
      _ ≤ dist (T x) (T y) + ‖a‖ := by
        rw [map_sub, ← dist_eq_norm]
        exact add_le_add le_rfl (hT a)
  have hscaled := mul_le_mul_of_nonneg_left hdist hκ
  have herr := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ κ + 1)
  nlinarith [hlower w hw]

theorem projection_separates_of_lower_bound {d e : ℕ}
    (T : Ambient d →L[ℝ] Ambient e) (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (x y : Ambient d) (ε κ : ℝ) (hκ : 0 < κ)
    (hsmall : 4 * ε * (κ + 1) ≤ κ)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖)
    (hx : infDist x (S : Set (Ambient d)) ≤ ε * dist x y)
    (hy : infDist y (S : Set (Ambient d)) ≤ ε * dist x y)
    (hlower : ∀ v ∈ S.direction, κ * ‖v‖ ≤ ‖T v‖) :
    dist x y ≤ (2 / κ) * dist (T x) (T y) := by
  have h := projection_lower_bound_of_pairwise_plane T S x y ε κ hκ.le hT hx hy hlower
  have hs := mul_le_mul_of_nonneg_right hsmall (dist_nonneg (x := x) (y := y))
  have hhalf : κ * dist x y ≤ 2 * dist (T x) (T y) := by nlinarith
  have hdiv := (le_div_iff₀ hκ).mpr (by nlinarith : dist x y * κ ≤ 2 * dist (T x) (T y))
  convert! hdiv using 1; ring

theorem exists_ball_cover_of_noncollapsing_pairwise_planes {n d : ℕ}
    (E : Set (Ambient d)) (a : Ambient d) (r : ℝ) (hE : E ⊆ ball a r)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (κ : ℝ≥0) (hκ : 0 < κ) (ε : ℝ) (hsmall : 4 * ε * ((κ : ℝ) + 1) ≤ κ)
    (hfit : ∀ x ∈ E, ∀ y ∈ E, ∃ S : AffineSubspace ℝ (Ambient d),
      IsAffineNPlane n S ∧
      infDist x (S : Set (Ambient d)) ≤ ε * dist x y ∧
      infDist y (S : Set (Ambient d)) ≤ ε * dist x y ∧
      ∀ v ∈ S.direction, (κ : ℝ) * ‖v‖ ≤ ‖P.starProjection v‖) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * (2 / κ)) g ∧ E ⊆ range g := by
  apply exists_ball_lipschitz_cover_of_projection E a r hE P hdim (2 / κ)
  intro x hx y hy
  obtain ⟨S, hS, hxS, hyS, hlower⟩ := hfit x hx y hy
  let : Nonempty S := hS.1.to_subtype
  have hκreal : 0 < (κ : ℝ) := hκ
  simpa only [NNReal.coe_div, NNReal.coe_ofNat] using!
    projection_separates_of_lower_bound P.starProjection S x y ε κ hκreal hsmall
      (fun v => P.norm_starProjection_apply_le v) hxS hyS hlower

end

end RieszRectifiability

end OAI
