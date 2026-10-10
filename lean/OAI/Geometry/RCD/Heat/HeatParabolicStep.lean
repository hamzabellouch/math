import OAI.Geometry.RCD.Heat.HeatCylinderEnergy
import OAI.Geometry.RCD.Sobolev.InhomogeneousSobolev
import OAI.Geometry.RCD.Sobolev.LevelSetHolderStep

namespace OAI

/-! # A superlinear parabolic level estimate

The actual heat cylinder energy and the proved RCD Sobolev inequality
control the next upper level. The constants are uniform at bounded
rescaled curvature, and no heat-kernel estimate is assumed.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_parabolic_level_step {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    letI : (hausdorff n X).Regular := inferInstance
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ (f : Lp ℝ 2 (hausdorff n X)) (r s : ℝ), r < s → s < R →
      ∀ (a c b k h : ℝ), 0 < a → a < c → c ≤ b → ∀ (hk : 0 ≤ k), k < h →
      let μ := hausdorff n X
      let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
      let Y := ∫ t in a..b, ∫ y in closedBall x s, (P (heatAt μ hX.quadratic t f) y)^2 ∂μ
      let Q := (c-a)⁻¹+5*((s-r)⁻¹)^2
      (∫ t in c..b, ∫ y in closedBall x r, (max (heatAt μ hX.quadratic t f y-h) 0)^2 ∂μ) ≤
        C*(μ.real (ball x R))^(2/p-1)*(2*R^2*Q+1)*Y*(Q*Y/(h-k)^2)^(1-2/p) := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : (hausdorff n X).Regular := inferInstance
  dsimp only
  obtain ⟨p,C,hp,hC,hSob⟩ := hX.inhomogeneous_dirichlet_sobolev hn
  refine ⟨p,C,hp,hC,?_⟩
  intro x R hR hcurv f r s hrs hsR a c b k h ha hac hcb hk hkh
  let μ := hausdorff n X
  let P : Lp ℝ 2 μ → Lp ℝ 2 μ := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
  let U := fun t => P (heatAt μ hX.quadratic t f)
  let χ := nestedBallCutoff x r s
  let L : ℝ≥0 := ⟨(s-r)⁻¹,inv_nonneg.mpr (sub_pos.mpr hrs).le⟩
  have hχ : LipschitzWith L χ := nestedBallCutoff_lipschitz x hrs
  have hsupp : tsupport χ ⊆ closedBall x s := nestedBallCutoff_tsupport x hrs
  have hcompact := nestedBallCutoff_hasCompactSupport x hrs
  have hb (y : X) : |χ y| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (nestedBallCutoff_bounds x r s y).1]
    exact (nestedBallCutoff_bounds x r s y).2
  have hnonneg (y : X) : 0 ≤ χ y := (nestedBallCutoff_bounds x r s y).1
  have hplateau (y : X) (hy : y ∈ closedBall x r) : χ y = 1 :=
    nestedBallCutoff_eq_one x hrs (by simpa only [mem_closedBall,dist_comm] using hy)
  let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable 1 hb)
  let Z := fun t => N (U t)
  let E := fun t => (energyLp μ (Z t)).toReal
  let F := fun t => ‖Z t‖^2
  let J := fun t => ∫ y in closedBall x s, (U t y)^2 ∂μ
  let Y := ∫ t in a..b, J t
  let Q := (c-a)⁻¹+5*(L:ℝ)^2
  let A := C*(μ.real (ball x R))^(2/p-1)
  let β := 1-2/p
  let T := (Q*Y/(h-k)^2)^β
  have hβ : 0 ≤ β := by
    have hp0 : 0 < p := by linarith
    have hd : 2/p < 1 := (div_lt_one hp0).mpr hp
    dsimp only [β]
    linarith
  have hYn : 0 ≤ Y := intervalIntegral.integral_nonneg_of_forall (hac.le.trans hcb)
    (fun t => integral_nonneg fun y => sq_nonneg (U t y))
  have hQn : 0 ≤ Q := by dsimp only [Q]; positivity
  have hTn : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  have hAn : 0 ≤ A := by dsimp only [A]; positivity
  have hPc : Continuous P := (upperLevelPart_lipschitz k).continuous_compLp (upperLevelPart_zero hk)
  have hUc : Continuous U := hPc.comp (heatAt_continuous μ hX.quadratic f)
  have hZc : Continuous Z := N.continuous.comp hUc
  have hFc : Continuous F := hZc.norm.pow 2
  have hJc : Continuous J := continuous_setIntegral_sq_path μ hUc measurableSet_closedBall
  have hCyl := heat_level_cylinder_energy μ hX.quadratic f hχ hcompact hb hnonneg
    measurableSet_closedBall measurableSet_closedBall hplateau hsupp hk ha hac hcb
  change (∫ t in c..b, E t) ≤ Q*Y ∧
    ∀ t ∈ Icc c b, (∫ y in closedBall x r, (U t y)^2 ∂μ) ≤ Q*Y at hCyl
  have hEi : IntervalIntegrable E volume c b :=
    (heat_level_local_energy μ hX.quadratic f hχ hcompact hb hnonneg
      measurableSet_closedBall measurableSet_closedBall hplateau hsupp hk (ha.trans hac) hcb).1
  have hFJ (t : ℝ) : F t ≤ J t := by
    simpa only [NNReal.coe_one,one_pow,one_mul] using
      cutoff_L2_norm_sq_le_setIntegral μ (U t) hχ hb measurableSet_closedBall hsupp
  have hFi : (∫ t in c..b, F t) ≤ Y := by
    have h1 := intervalIntegral.integral_mono_on hcb
      (hFc.intervalIntegrable (μ := volume) c b) (hJc.intervalIntegrable (μ := volume) c b)
      (fun t _ => hFJ t)
    have h2 : (∫ t in c..b, J t) ≤ Y := intervalIntegral.integral_mono_interval
      hac.le hcb le_rfl (Eventually.of_forall fun t => integral_nonneg fun y => sq_nonneg (U t y))
        (hJc.intervalIntegrable (μ := volume) a b)
    exact h1.trans h2
  have hUrep (t : ℝ) : U t =ᵐ[μ] fun y => max (heatAt μ hX.quadratic t f y-k) 0 :=
    (upperLevelPart_lipschitz k).coeFn_compLp (upperLevelPart_zero hk) _
  have hZrep (t : ℝ) : Z t =ᵐ[μ] fun y => χ y*max (heatAt μ hX.quadratic t f y-k) 0 := by
    filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ χ hχ.continuous.measurable 1 hb) (U t),
      boundedMultiplier_coe μ χ hχ.continuous.measurable 1 hb,hUrep t] with y h1 h2 h3
    rw [h1,h2,h3]
  let H := fun t => ∫ y in closedBall x r, (max (heatAt μ hX.quadratic t f y-h) 0)^2 ∂μ
  have hHc : Continuous H := by
    let Ph : Lp ℝ 2 μ → Lp ℝ 2 μ := (upperLevelPart_lipschitz h).compLp (upperLevelPart_zero (hk.trans hkh.le))
    have hPh : Continuous Ph := (upperLevelPart_lipschitz h).continuous_compLp
      (upperLevelPart_zero (hk.trans hkh.le))
    have hh := continuous_setIntegral_sq_path μ (S := closedBall x r)
      (hPh.comp (heatAt_continuous μ hX.quadratic f))
      measurableSet_closedBall
    convert hh using 1
    funext t
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ((upperLevelPart_lipschitz h).coeFn_compLp
      (upperLevelPart_zero (hk.trans hkh.le)) (heatAt μ hX.quadratic t f))] with y hy
    exact (congrArg (fun z : ℝ => z^2) hy).symm
  have hstep (t : ℝ) (ht : t ∈ Icc c b) : H t ≤ A*T*(2*R^2*E t+F t) := by
    let u := (heatSobolev μ hX.quadratic t ((ha.trans hac).trans_le ht.1) f).upperPositivePart μ hX.quadratic hk
    let w : SobolevSpace.dirichlet μ hX.quadratic (ball x R) :=
      ⟨SobolevSpace.cutoffCLM μ hX.quadratic hχ hcompact hb hnonneg u,
        SobolevSpace.cutoffCLM_mem_dirichlet μ hX.quadratic hχ hcompact hb hnonneg
          (hsupp.trans (closedBall_subset_ball hsR)) u⟩
    have hw : SobolevSpace.toLp μ hX.quadratic w.val = Z t := by
      change N (P (SobolevSpace.toLp μ hX.quadratic (heatSobolev μ hX.quadratic t
        ((ha.trans hac).trans_le ht.1) f))) = _
      rw [heatSobolev_toLp]
    obtain ⟨hwi,hwSob⟩ := hSob x R hR hcurv w
    rw [hw] at hwi
    rw [energyForm_self] at hwSob
    change (∫ y in ball x R, |SobolevSpace.toLp μ hX.quadratic w.val y|^p ∂μ)^(2/p) ≤
      A*(R^2*(2*(energyLp μ (SobolevSpace.toLp μ hX.quadratic w.val)).toReal)+
        ‖SobolevSpace.toLp μ hX.quadratic w.val‖^2) at hwSob
    rw [hw] at hwSob
    have hrep : Z t =ᵐ[μ.restrict (closedBall x r)] fun y => max (heatAt μ hX.quadratic t f y-k) 0 := by
      filter_upwards [ae_restrict_of_ae (hZrep t),ae_restrict_mem measurableSet_closedBall] with y hy hym
      rw [hy,hplateau y hym,one_mul]
    have hholder := level_set_holder_step μ measurableSet_ball measurableSet_closedBall
      (closedBall_subset_ball (hrs.trans hsR)) (Subset.refl _) (hX.finiteOnBounded _ isBounded_ball)
      (heatAt μ hX.quadratic t f) (Z t) hk hkh hp hrep hwi
    have hmass : (∫ y in closedBall x r, (max (heatAt μ hX.quadratic t f y-k) 0)^2 ∂μ) ≤ Q*Y := by
      have he : (∫ y in closedBall x r, (U t y)^2 ∂μ) =
          ∫ y in closedBall x r, (max (heatAt μ hX.quadratic t f y-k) 0)^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (hUrep t)] with y hy
        exact congrArg (fun z : ℝ => z^2) hy
      rw [← he]
      exact hCyl.2 t ht
    have hpow : ((∫ y in closedBall x r, (max (heatAt μ hX.quadratic t f y-k) 0)^2 ∂μ)/(h-k)^2)^β ≤ T :=
      Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hmass (sq_nonneg _)) hβ
    have hprod := mul_le_mul hwSob hpow (by positivity)
      (by positivity : 0 ≤ A*(R^2*(2*(energyLp μ (Z t)).toReal)+‖Z t‖^2))
    exact hholder.trans (by dsimp only [H,E,F]; nlinarith only [hprod])
  have hi := hEi.const_mul (2*R^2) |>.add (hFc.intervalIntegrable (μ := volume) c b)
  have hint := intervalIntegral.integral_mono_on hcb (hHc.intervalIntegrable (μ := volume) c b)
    (hi.const_mul (A*T)) hstep
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hEi.const_mul (2*R^2)) (hFc.intervalIntegrable (μ := volume) c b),
    intervalIntegral.integral_const_mul] at hint
  have hsum : 2*R^2*(∫ t in c..b, E t)+(∫ t in c..b, F t) ≤ (2*R^2*Q+1)*Y := by
    have hh := mul_le_mul_of_nonneg_left hCyl.1 (by positivity : 0 ≤ 2*R^2)
    nlinarith only [hh,hFi]
  have hfinal := hint.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hAn hTn))
  change (∫ t in c..b, H t) ≤ A*(2*R^2*Q+1)*Y*T
  nlinarith only [hfinal]

end RegularPointCoordinates

end

end OAI
