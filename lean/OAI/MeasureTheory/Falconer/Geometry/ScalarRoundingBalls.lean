import OAI.MeasureTheory.Falconer.Geometry.ScalarRoundingCovers

namespace OAI

/-! The original scalar Frostman estimate survives dyadic rounding with
 a fixed factor, including radii near the diameter of the unit interval. -/
namespace Falconer.Regularization

 theorem scalar_rounding_ball_bound (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (1/2:ℝ)^N ≤ |x-y|)
    {K κ : ℝ} (hK : 1 ≤ K) (hκ : 0 ≤ κ)
    (hball : ∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass X u r ≤ K*r^κ*(X.card:ℝ)) :
    ∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass (scalarRoundedPoints N X) u r ≤
        ((2:ℝ)^κ*K)*r^κ*((scalarRoundedPoints N X).card:ℝ) := by
  intro u r hr _
  have hδ : (0:ℝ) < (1/2:ℝ)^N := by positivity
  have hr0 : 0 < r := hδ.trans_le hr
  have hcard := scalarRoundedPoints_card N X hX hsep
  have hnear : ∀ x ∈ X, |scalarPathCenter (scalarPointPath N x)-x| ≤ (1/2:ℝ)^N/2 := by
    intro x hx
    simpa only [abs_sub_comm] using scalar_point_path_error N (hX x hx)
  have hm := scalar_image_ball_bound X (fun x => scalarPathCenter (scalarPointPath N x)) hnear u r
  rw [← scalarRoundedPoints_eq_image] at hm
  rw [hcard]
  by_cases hsmall : r ≤ 1/2
  · have hlow : (1/2:ℝ)^N ≤ r+(1/2:ℝ)^N/2 := by linarith
    have hhigh : r+(1/2:ℝ)^N/2 ≤ 1 := by linarith
    have hb := hball u (r+(1/2:ℝ)^N/2) hlow hhigh
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ r+(1/2:ℝ)^N/2)
      (show r+(1/2:ℝ)^N/2 ≤ 2*r by linarith) hκ
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le] at hp
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ K*(X.card:ℝ) by positivity)
    nlinarith
  · have hp : 1 ≤ (2*r)^κ := Real.one_le_rpow (by linarith) hκ
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le] at hp
    have hmass : scalarBallMass (scalarRoundedPoints N X) u r ≤ (X.card:ℝ) := by
      unfold scalarBallMass
      rw [← hcard]
      exact_mod_cast Finset.card_filter_le _ _
    have hfactor : 1 ≤ (2:ℝ)^κ*K*r^κ := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg X.card)
    nlinarith

end Falconer.Regularization

end OAI
