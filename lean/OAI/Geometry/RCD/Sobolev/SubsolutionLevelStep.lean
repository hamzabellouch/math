import OAI.Geometry.RCD.Sobolev.SubsolutionLevelMoment
import OAI.Geometry.RCD.Sobolev.LevelSetHolderStep
import OAI.Geometry.RCD.Sobolev.NestedBallCutoff

namespace OAI

/-! # Three-level step for a weak subsolution with bounded potential -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.subsolution_level_step {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (a : ℝ), 0 ≤ a →
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball x R) u a →
      ∀ r s j k h : ℝ, 0 ≤ r → r < s → s < R → 0 ≤ j → j < k → k < h →
      let U := SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      let J := ∫ y in closedBall x s, (max (U y-j) 0)^2 ∂hausdorff n X
      (∫ y in closedBall x r, (max (U y-h) 0)^2 ∂hausdorff n X) ≤
        C*((hausdorff n X).real (ball x R))^(2/p-1)*
          (10*R^2*((s-r)⁻¹)^2+4*R^2*a*(k/(k-j))+1)*J*(J/(h-k)^2)^(1-2/p) := by
  obtain ⟨p,C,hp,hC,hM⟩ := hX.subsolution_level_cutoff_moment hn
  refine ⟨p,C,hp,hC,?_⟩
  intro x R hR hcurv u a ha hu r s j k h _hr hrs hsR hj hjk hkh
  have hk0 : 0 ≤ k := hj.trans hjk.le
  let μ := hausdorff n X
  let U := SobolevSpace.toLp μ hX.quadratic u
  let J := ∫ y in closedBall x s, (max (U y-j) 0)^2 ∂μ
  let Jk := ∫ y in closedBall x s, (max (U y-k) 0)^2 ∂μ
  let χ := nestedBallCutoff x r s
  let L : ℝ≥0 := ⟨(s-r)⁻¹,inv_nonneg.mpr (sub_pos.mpr hrs).le⟩
  have hχ : LipschitzWith L χ := nestedBallCutoff_lipschitz x hrs
  have hc := nestedBallCutoff_hasCompactSupport x hrs
  have hsupp : tsupport χ ⊆ closedBall x s := nestedBallCutoff_tsupport x hrs
  have hsball : closedBall x s ⊆ ball x R := closedBall_subset_ball hsR
  obtain ⟨w,hrep,hi,hbound⟩ := hM x R hR hcurv u a ha hu j k hj hjk χ L hχ hc
    (nestedBallCutoff_bounds x r s) (hsupp.trans hsball) (closedBall x s) measurableSet_closedBall hsupp
  have hrball : closedBall x r ⊆ ball x R := closedBall_subset_ball (hrs.trans hsR)
  have hrrep : SobolevSpace.toLp μ hX.quadratic w.val =ᵐ[μ.restrict (closedBall x r)]
      fun y => max (U y-k) 0 := by
    filter_upwards [ae_restrict_of_ae hrep,ae_restrict_mem measurableSet_closedBall] with y hy hyr
    have hx : dist x y ≤ r := by simpa only [mem_closedBall,dist_comm] using hyr
    simpa only [χ,nestedBallCutoff_eq_one x hrs hx,one_mul] using hy
  have hh := level_set_holder_step μ measurableSet_ball measurableSet_closedBall hrball
    (closedBall_subset_closedBall hrs.le) (hX.finiteOnBounded _ isBounded_ball)
    U (SobolevSpace.toLp μ hX.quadratic w.val) (hj.trans hjk.le) hkh hp hrrep hi
  have hJk : Jk ≤ J := integral_upper_level_mono μ hX.quadratic u hj hjk.le (closedBall x s)
  have hpow : (Jk/(h-k)^2)^(1-2/p) ≤ (J/(h-k)^2)^(1-2/p) := by
    apply Real.rpow_le_rpow (by dsimp [Jk]; positivity)
      (div_le_div_of_nonneg_right hJk (sq_nonneg _))
    have hp0 : 0 < p := by linarith
    have hh := (div_le_one hp0).mpr hp.le
    linarith
  exact hh.trans (mul_le_mul hbound hpow (by positivity) (by positivity))

end RegularPointCoordinates

end

end OAI
