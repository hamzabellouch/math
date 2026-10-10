import OAI.Geometry.NodalSets.Elliptic.RealBallCutoffChain

namespace OAI

namespace Yau.Geometry
open MeasureTheory Metric
open scoped ContDiff
noncomputable section

lemma real_cutoff_inner_integral_le (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H)
    (hpos : ∀ x, 0 ≤ H x) (y : Yau.Jets.Coord) (r : ℝ)
    (hone : ∀ x ∈ closedBall y r, eta x=1) :
    (∫ x in closedBall y r, H x) ≤ ∫ x, eta x^2*H x := by
  have hi := real_cutoff_square_integrable eta H heta hc hH
  calc
    _ = ∫ x in closedBall y r, eta x^2*H x := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro x hx
      dsimp only
      rw [hone x hx]; simp
    _ ≤ _ := setIntegral_le_integral hi
      (Filter.Eventually.of_forall (fun x ↦ mul_nonneg (sq_nonneg _) (hpos x)))

lemma real_cutoff_outer_integral_le (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H)
    (hpos : ∀ x, 0 ≤ H x) (hval : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1)
    (y : Yau.Jets.Coord) (R : ℝ) (hs : tsupport eta ⊆ closedBall y R) :
    (∫ x, eta x^2*H x) ≤ ∫ x in closedBall y R, H x := by
  have hi := real_cutoff_square_integrable eta H heta hc hH
  have hI := hH.continuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall y R)
  calc
    _ = ∫ x in closedBall y R, eta x^2*H x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : eta x=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
      rw [hz]; simp
    _ ≤ _ := setIntegral_mono_on hi.integrableOn hI measurableSet_closedBall (fun x _ ↦ by
      have hsq : eta x^2 ≤ 1 := by nlinarith [(hval x).1,(hval x).2]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (hpos x))

end
end Yau.Geometry

end OAI
