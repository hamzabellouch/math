import OAI.Geometry.RCD.Heat.HeatCutoffEnergy

namespace OAI

/-! # Time-integrated local heat energy

The error remains a space-time integral against the squared cutoff gradient.
The positive starting time avoids imposing Sobolev regularity on the datum.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

theorem integral_energy_inequality {F D E I : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hD : Continuous D) (hE : Continuous E) (hI : Continuous I)
    (hF : ∀ s ∈ uIcc a b, HasDerivAt F (D s) s)
    (hdiff : ∀ s ∈ Icc a b, D s+(1/2:ℝ)*E s ≤ 5*I s) :
    F b+(1/2:ℝ)*(∫ s in a..b, E s) ≤ F a+5*(∫ s in a..b, I s) := by
  have hDi := hD.intervalIntegrable (μ := volume) a b
  have hEi := hE.intervalIntegrable (μ := volume) a b
  have hIi := hI.intervalIntegrable (μ := volume) a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hDi
  have hint := intervalIntegral.integral_mono_on hab (hDi.add (hEi.const_mul (1/2:ℝ)))
    (hIi.const_mul 5) hdiff
  rw [intervalIntegral.integral_add hDi (hEi.const_mul (1/2:ℝ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hFTC] at hint
  linarith only [hint]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_weighted_square_continuous (f : Lp ℝ 2 μ) {w : X → ℝ}
    (hw : MemLp w ∞ μ) :
    Continuous (fun t => ∫ x, w x*(heatAt μ hQ t f x)^2 ∂μ) := by
  let V := hw.toLp w
  have hV : V =ᵐ[μ] w := hw.coeFn_toLp
  have he : (fun t => ∫ x, w x*(heatAt μ hQ t f x)^2 ∂μ) =
      fun t => inner ℝ (heatAt μ hQ t f) (lpMultiplier μ V (heatAt μ hQ t f)) := by
    funext t
    exact (lpMultiplier_integral_sq μ V (heatAt μ hQ t f) hV).2.symm
  rw [he]
  exact (heatAt_continuous μ hQ f).inner
    ((lpMultiplier μ V).continuous.comp (heatAt_continuous μ hQ f))

theorem heatTail_continuous (a : ℝ) (ha : 0 < a) (f : Lp ℝ 2 μ) :
    Continuous (heatTail μ hQ a ha f) := by
  change Continuous (fun t => (heatSobolevMap μ hQ a ha) (heatAt μ hQ (t-a) f))
  exact (heatSobolevMap μ hQ a ha).continuous.comp
    ((heatAt_continuous μ hQ f).comp (continuous_id.sub continuous_const))

theorem heat_cutoff_error_continuous (f : Lp ℝ 2 μ) (η : SobolevSpace μ hQ)
    {A : ℝ≥0} (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A) :
    Continuous (fun s => ∫ x, (heatAt μ hQ s f x)^2*
      (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ) := by
  have hgm : MemLp (fun x => (SobolevSpace.minimalSlope μ hQ η x)^2) ∞ μ := by
    apply memLp_top_of_bound ((Lp.aestronglyMeasurable _).pow 2) ((A:ℝ)^2)
    filter_upwards [hgrad] with x hx
    change ‖(SobolevSpace.minimalSlope μ hQ η x)^2‖ ≤ (A:ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) A.coe_nonneg).mpr hx
  have hh := heat_weighted_square_continuous μ hQ f hgm
  convert hh using 1
  funext s
  apply integral_congr_ae
  exact Eventually.of_forall fun x => mul_comm _ _

theorem heat_cutoff_energy_integral (f : Lp ℝ 2 μ) (η : SobolevSpace μ hQ)
    {χ : X → ℝ} {L B A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let V := boundedMultiplier μ χ hχ.continuous.measurable B hb
    let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
    let u := heatTail μ hQ (a/2) (half_pos ha) f
    ‖lpMultiplier μ V (heatAt μ hQ b f)‖^2+
        (1/2:ℝ)*(∫ s in a..b, energyForm μ hQ (M (u s)) (M (u s))) ≤
      ‖lpMultiplier μ V (heatAt μ hQ a f)‖^2+
        5*(∫ s in a..b, ∫ x, (heatAt μ hQ s f x)^2*
          (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ) := by
  intro V M u
  let F := fun s => ‖lpMultiplier μ V (heatAt μ hQ s f)‖^2
  let D := fun s => -2*energyForm μ hQ (u s) (M (M (u s)))
  let E := fun s => energyForm μ hQ (M (u s)) (M (u s))
  let I := fun s => ∫ x, (heatAt μ hQ s f x)^2*
    (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ
  have hu : Continuous u := heatTail_continuous μ hQ (a/2) (half_pos ha) f
  have hMu : Continuous (fun s => M (u s)) := M.continuous.comp hu
  have hMMu : Continuous (fun s => M (M (u s))) := M.continuous.comp hMu
  have hpair : Continuous (fun s : ℝ => (u s,M (M (u s)))) := hu.prodMk hMMu
  have hform : Continuous (fun s => energyForm μ hQ (u s) (M (M (u s)))) := by
    simpa only [Function.comp_apply] using! (energyForm_continuous μ hQ).comp hpair
  have hDc : Continuous D := by
    exact (continuous_const (y := (-2:ℝ))).mul hform
  have hEc : Continuous E := by
    simpa only [Function.comp_apply] using! (energyForm_continuous μ hQ).comp (hMu.prodMk hMu)
  have hIc : Continuous I := heat_cutoff_error_continuous μ hQ f η hgrad
  have hueq (s : ℝ) (hs : s ∈ Icc a b) :
      u s = heatSobolev μ hQ s (ha.trans_le hs.1) f :=
    heatTail_eq μ hQ (a/2) (half_pos ha) f s (by linarith [hs.1])
  have hFd (s : ℝ) (hst : s ∈ uIcc a b) : HasDerivAt F (D s) s := by
    have hsa : a ≤ s := ((uIcc_of_le hab) ▸ hst).1
    have hd := heat_cutoff_norm_hasDerivAt μ hQ f hχ hs hb hn s (ha.trans_le hsa)
    change HasDerivAt F (-2*energyForm μ hQ _ _) s at hd
    simpa only [D,hueq s ((uIcc_of_le hab) ▸ hst)] using hd
  have hdiff (s : ℝ) (hst : s ∈ Icc a b) : D s+(1/2:ℝ)*E s ≤ 5*I s := by
    have hd := heat_cutoff_energy_differential μ hQ f η hχ hs hb hn hrep hgrad
      s (ha.trans_le hst.1)
    change deriv F s+(1/2:ℝ)*energyForm μ hQ
      (M (heatSobolev μ hQ s (ha.trans_le hst.1) f))
      (M (heatSobolev μ hQ s (ha.trans_le hst.1) f)) ≤ 5*I s at hd
    rw [(hFd s ((uIcc_of_le hab).symm ▸ hst)).deriv] at hd
    simpa only [E,hueq s hst] using hd
  exact integral_energy_inequality hab hDc hEc hIc hFd hdiff

end RegularPointCoordinates

end

end OAI
