import OAI.Geometry.RCD.Metric.CoarseFineImageHoleVolume
import OAI.Geometry.RCD.Coordinates.LocalCoordinateImageMass

namespace OAI

/-! # Absolute source mass from the actual coarse and fine coordinate data -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.coarse_fine_source_mass {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hEuclidean : hausdorff n (Euclidean n) = volume)
    {p : X} {R ρ η : ℝ} {C L : ℝ≥0}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : 64*ρ ≤ R) (hC : 1 ≤ (C:ℝ))
    (hcurv : -1 ≤ K*(32*R)^2) (hη : (2*R)*(η/4) ≤ ρ/4)
    {v : X → Euclidean n} {U : Set X} (hU : IsCompact U) (hUsub : U ⊆ closedBall p R)
    (hgood : LipschitzOnWith L v U) (hglobal : LipschitzOnWith C v (ball p (4*R)))
    (hcoarse : IsPointedApproximation p 0 (2*R) (1/2) (η/4)
      (fun x => (2*R)⁻¹ • (v x-v p)))
    (hfine : ∀ z ∈ U, ∀ r : ℝ, 0 < r → r < R →
      IsPointedApproximation z 0 r (1/16) (1/128) (fun x => r⁻¹ • (v x-v z)))
    (hpoint : ∃ z ∈ U, dist z p < ρ/4) :
    volume.real (ball (0 : Euclidean n) ρ) -
      (2*5^n*volume.real (ball (0 : Euclidean n) 1))*
        (((4*(C:ℝ))^n*(Real.cosh 1^(n-1)*2^n)*(16*R)^n/
          (hausdorff n X).real (ball p (16*R)))*
          (hausdorff n X).real (ball p R \ U)) ≤
      (L:ℝ)^n*(hausdorff n X).real (ball p (ρ+(2*R)*(η/4))) := by
  have hu : LipschitzOnWith L (fun x => v x-v p) U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_sub_right] using hgood.dist_le_mul x hx y hy
  apply local_source_mass_of_image_error hEuclidean hU hu
    (hX.finiteOnBounded _ isBounded_ball).ne 0 hρ
  · intro x hx hi
    exact centered_coordinate_preimage_ball (by positivity : 0 < 2*R)
      (by norm_num : (0:ℝ)≤1/2) le_rfl hcoarse
      (by have hh := hUsub hx; change dist x p ≤ R at hh; linarith only [hh]) hi
  · exact hX.coarse_fine_image_hole_volume hn hR hρ hρR hC hcurv hη
      hU hUsub hglobal hcoarse hfine hpoint

end RegularPointCoordinates

end

end OAI
