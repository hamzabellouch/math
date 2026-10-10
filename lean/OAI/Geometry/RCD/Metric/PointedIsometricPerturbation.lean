import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # A uniform perturbation of rotated Euclidean coordinates -/

open Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_isometric_perturbation {n : ℕ} {p : X} {r S R ε η : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hRS : R ≤ S) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    {V w : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    (T : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) (hw : w p=0)
    (hclose : ∀ x, dist x p ≤ R*r → dist (w x) (T (V x)) ≤ η) :
    IsPointedApproximation p 0 r R (2*η+3*ε) w := by
  have hlarge {x : X} (hx : dist x p ≤ R*r) : dist x p ≤ S*r :=
    hx.trans (mul_le_mul_of_nonneg_right hRS hr.le)
  refine ⟨by rw [hw,dist_self]; positivity,?_,?_⟩
  · intro x y hx hy
    have hv := abs_le.mp (hV.2.1 x y (hlarge hx) (hlarge hy))
    have hx' := hclose x hx
    have hy' := hclose y hy
    have h1 := dist_triangle4 (w x) (T (V x)) (T (V y)) (w y)
    have h2 := dist_triangle4 (T (V x)) (w x) (w y) (T (V y))
    rw [T.dist_map,dist_comm (T (V y)) (w y)] at h1
    rw [T.dist_map,dist_comm (T (V x)) (w x)] at h2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · intro z hz
    have hzn : ‖z‖ ≤ R-(2*η+3*ε) := by simpa only [dist_zero_right] using hz
    have hz' : dist (T.symm z) (0 : Euclidean n) ≤ S-ε := by
      simpa only [dist_zero_right,T.symm.norm_map] using
        (show ‖z‖ ≤ S-ε by linarith)
    obtain ⟨x,hx,hxz⟩ := hV.2.2 (T.symm z) hz'
    have hrad := (abs_le.mp (pointed_radial_distance hr (hR.trans hRS) hV hx)).1
    have hnorm : ‖V x‖ ≤ ‖z‖+ε := by
      have ht := norm_le_norm_add_norm_sub (T.symm z) (V x)
      rw [T.symm.norm_map,← dist_eq_norm,dist_comm (T.symm z) (V x)] at ht
      linarith
    have hxR : dist x p ≤ R*r := (div_le_iff₀ hr).mp (by
      simp only [dist_zero_right] at hz
      linarith)
    refine ⟨x,hxR,?_⟩
    have hdist : dist (T (V x)) z ≤ ε := by
      simpa only [T.apply_symm_apply] using (T.dist_map (V x) (T.symm z)).le.trans hxz
    have ht := dist_triangle (w x) (T (V x)) z
    linarith [hclose x hxR]

end RegularPointCoordinates

end

end OAI
