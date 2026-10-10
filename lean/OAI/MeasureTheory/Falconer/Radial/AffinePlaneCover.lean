import OAI.MeasureTheory.Falconer.Geometry.EuclideanBallNet

namespace OAI

/-! # Covering a bounded neighborhood of an affine plane -/

namespace Falconer
open Set Metric
variable {k d : ℕ}

theorem affine_plane_neighborhood_cover (F : Space k →ₗᵢ[ℝ] Space d) (a : Space d)
    {M A r : ℝ} (hM : 0 ≤ M) (hA : ‖a‖ ≤ A) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ S : Finset (Space d), (S.card:ℝ) ≤ (2*(M+A+1)/r+1)^k ∧
      ∀ x : Space d, ‖x‖ ≤ M → (∃ y : Space k, ‖x-(a+F y)‖ ≤ r) →
        ∃ c ∈ S, x ∈ ball c (3*r) := by
  classical
  have hA0 : 0 ≤ A := (norm_nonneg a).trans hA
  obtain ⟨T,_,hcover,hcard⟩ := finite_euclidean_ball_net k
    (by positivity : 0 ≤ M+A+1) hr
  let S := T.image (fun y => a+F y)
  refine ⟨S,?_,?_⟩
  · exact (Nat.cast_le.mpr (Finset.card_image_le)).trans hcard
  · intro x hx hnear
    obtain ⟨y,hy⟩ := hnear
    have hyR : ‖y‖ ≤ M+A+1 := by
      have hF := norm_sub_le (a+F y) a
      have hxF := norm_le_norm_add_norm_sub' (a+F y) x
      rw [add_sub_cancel_left,F.norm_map] at hF
      rw [norm_sub_rev] at hy
      linarith only [hF,hxF,hy,hx,hA,hr1]
    obtain ⟨z,hz,hyz⟩ := hcover y hyR
    refine ⟨a+F z,Finset.mem_image.mpr ⟨z,hz,rfl⟩,?_⟩
    have hd : dist (a+F y) (a+F z) ≤ r := by
      simpa only [dist_add_left,F.dist_map] using hyz
    apply mem_ball.mpr
    have ht := dist_triangle x (a+F y) (a+F z)
    have hxF : dist x (a+F y) ≤ r := by simpa only [dist_eq_norm] using hy
    linarith only [ht,hxF,hd,hr]

end Falconer

end OAI
