import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicReconstruction

namespace OAI

/-! Passing from the literal closed dyadic prime intervals to the full
prime comparison. The endpoint mass is proved negligible explicitly. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem primeCutoffSum_isLittleO_of_dyadic (c : Eisenstein → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ p : Eisenstein, primaryPrime p → ‖c p‖ ≤ M)
    (hd : (fun X => primeDyadicSum c X) =o[atTop] firstMomentScale) :
    primeCutoffSum c =o[atTop] firstMomentScale := by
  apply dyadic_littleO_firstMoment (primeCutoffSum c)
    (fun _ hX => primeCutoffSum_zero_small c hX) (show 0 ≤ 27*M by positivity)
  · intro X hX
    have hXp : 0 ≤ X := (by norm_num : (0:ℝ) ≤ 1).trans hX
    have h1 := primeCutoffSum_norm_le c hM hc hXp
    have h2 := primeCutoffSum_norm_le c (X := X/2) hM hc (div_nonneg hXp (by norm_num))
    apply (norm_sub_le _ _).trans
    change ‖primeCutoffSum c X‖+‖primeCutoffSum c (X/2)‖ ≤ _
    linarith
  · have hhalf : (fun X : ℝ => primeDyadicSum c (X/2)) =o[atTop] firstMomentScale := by
      have hs : (firstMomentScale ∘ (fun X : ℝ => X/2)) =O[atTop] firstMomentScale := by
        change (fun X : ℝ => firstMomentScale (X/2)) =O[atTop] firstMomentScale
        simpa only [pow_one] using firstMomentScale_dyadic_isBigO 1
      exact (hd.comp_tendsto
        (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2))).trans_isBigO hs
    have he : (fun X : ℝ => dyadicDifference (primeCutoffSum c) X-primeDyadicSum c (X/2))
        =O[atTop] (fun _ : ℝ => (1:ℝ)) := by
      apply IsBigO.of_bound (2*M)
      filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
      simpa only [norm_one,mul_one] using prime_dyadic_endpoint_bound c hM hc hX
    have hconst : (fun _ : ℝ => (1:ℝ)) =o[atTop] firstMomentScale := by
      apply isLittleO_const_left.mpr
      right
      apply tendsto_firstMomentScale.congr'
      filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
      exact (Real.norm_of_nonneg (firstMomentScale_pos hX).le).symm
    apply ((he.trans_isLittleO hconst).add hhalf).congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)

theorem angularPrimeDifference_isLittleO_of_dyadic (ℓ : ℤ)
    (hd : (fun X => sharpDyadicPrimeComparison ℓ X) =o[atTop] firstMomentScale) :
    primeCutoffSum (primeComparisonCoefficient ℓ) =o[atTop] firstMomentScale :=
  primeCutoffSum_isLittleO_of_dyadic (primeComparisonCoefficient ℓ)
    (by linarith [cStar_pos]) (fun _ hp => primeComparisonCoefficient_bound ℓ hp) hd

end CubicFirstMoment

end

end OAI
