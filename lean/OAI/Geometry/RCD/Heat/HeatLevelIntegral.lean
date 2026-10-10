import OAI.Geometry.RCD.Heat.HeatLevelEnergy
import OAI.Geometry.RCD.Heat.HeatCutoffIntegral

namespace OAI

/-! # Time integration of the heat upper-level inequality

Measurability of the cutoff energy follows from lower semicontinuity of
the actual Cheeger energy. The differential inequality itself gives its
time integrability, without asserting continuity of Sobolev truncation.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

private theorem measurable_energy_integral {F D E I : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hD : ContinuousOn D (Icc a b)) (hI : ContinuousOn I (Icc a b))
    (hE : Measurable E) (hEn : ∀ s, 0 ≤ E s)
    (hF : ∀ s ∈ uIcc a b, HasDerivAt F (D s) s)
    (hdiff : ∀ s ∈ Icc a b, D s+(1/2:ℝ)*E s ≤ 5*I s) :
    IntervalIntegrable E volume a b ∧
      F b+(1/2:ℝ)*(∫ s in a..b, E s) ≤ F a+5*(∫ s in a..b, I s) := by
  have hEi : IntegrableOn E (Icc a b) volume := by
    apply ((hI.const_mul 10).sub (hD.const_mul 2)).integrableOn_Icc.mono'
      hE.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (hEn s)]
    have hh := hdiff s hs
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    linarith only [hh]
  have hEi' : IntervalIntegrable E volume a b :=
    ((uIcc_of_le hab).symm ▸ hEi).intervalIntegrable
  refine ⟨hEi',?_⟩
  have hDi := hD.intervalIntegrable_of_Icc (μ := volume) hab
  have hIi := hI.intervalIntegrable_of_Icc (μ := volume) hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hDi
  have hint := intervalIntegral.integral_mono_on hab (hDi.add (hEi'.const_mul (1/2:ℝ)))
    (hIi.const_mul 5) hdiff
  rw [intervalIntegral.integral_add hDi (hEi'.const_mul (1/2:ℝ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hFTC] at hint
  linarith only [hint]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
theorem continuous_weighted_square_path {u : ℝ → Lp ℝ 2 μ} (hu : Continuous u)
    {w : X → ℝ} (hw : MemLp w ∞ μ) :
    Continuous (fun s => ∫ x, w x*(u s x)^2 ∂μ) := by
  let W := hw.toLp w
  have hW : W =ᵐ[μ] w := hw.coeFn_toLp
  have he : (fun s => ∫ x, w x*(u s x)^2 ∂μ) =
      fun s => inner ℝ (u s) (lpMultiplier μ W (u s)) := by
    funext s
    exact (lpMultiplier_integral_sq μ W (u s) hW).2.symm
  rw [he]
  exact hu.inner ((lpMultiplier μ W).continuous.comp hu)

theorem heat_level_cutoff_energy_measurable (f : Lp ℝ 2 μ)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hb : ∀ x, |χ x| ≤ B) {k : ℝ} (hk : 0 ≤ k) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    Measurable (fun s => 2*(energyLp μ (N (P (heatAt μ hQ s f)))).toReal) := by
  intro N P
  have hP : Continuous P := (upperLevelPart_lipschitz k).continuous_compLp (upperLevelPart_zero hk)
  have hZ : Continuous (fun s => N (P (heatAt μ hQ s f))) :=
    N.continuous.comp (hP.comp (heatAt_continuous μ hQ f))
  have he := (energyLp_lowerSemicontinuous μ).comp hZ
  exact measurable_const.mul he.measurable.ennreal_toReal

theorem heat_level_cutoff_energy_integral (f : Lp ℝ 2 μ) (η : SobolevSpace μ hQ)
    {χ : X → ℝ} {L B A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A)
    {k : ℝ} (hk : 0 ≤ k) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    IntervalIntegrable (fun s => (energyLp μ (N (P (heatAt μ hQ s f)))).toReal) volume a b ∧
      ‖N (P (heatAt μ hQ b f))‖^2+
        ∫ s in a..b, (energyLp μ (N (P (heatAt μ hQ s f)))).toReal ≤
      ‖N (P (heatAt μ hQ a f))‖^2+
        5*(∫ s in a..b, ∫ x, (P (heatAt μ hQ s f) x)^2*
          (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ) := by
  intro N P
  let U := fun s => P (heatAt μ hQ s f)
  let F := fun s => ‖N (U s)‖^2
  let D := fun s => -2*inner ℝ (N (N (U s))) (heatGeneratorAt μ hQ s f)
  let E := fun s => 2*(energyLp μ (N (U s))).toReal
  let I := fun s => ∫ x, (U s x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ
  have hPc : Continuous P := (upperLevelPart_lipschitz k).continuous_compLp (upperLevelPart_zero hk)
  have hUc : Continuous U := hPc.comp (heatAt_continuous μ hQ f)
  have hNNc : Continuous (fun s => N (N (U s))) := N.continuous.comp (N.continuous.comp hUc)
  have hDc : ContinuousOn D (Icc a b) := by
    intro s hst
    exact ((hNNc.continuousAt.inner
      (heatGeneratorAt_continuousAt μ hQ f s (ha.trans_le hst.1))).const_mul (-2)).continuousWithinAt
  have hgm : MemLp (fun x => (SobolevSpace.minimalSlope μ hQ η x)^2) ∞ μ := by
    apply memLp_top_of_bound ((Lp.aestronglyMeasurable _).pow 2) ((A:ℝ)^2)
    filter_upwards [hgrad] with x hx
    change ‖(SobolevSpace.minimalSlope μ hQ η x)^2‖ ≤ (A:ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) A.coe_nonneg).mpr hx
  have hIc : Continuous I := by
    have hh := continuous_weighted_square_path μ hUc hgm
    convert hh using 1
    funext s
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
  have hDform (s : ℝ) (hst : s ∈ Icc a b) :
      D s = -2*energyForm μ hQ ((heatSobolev μ hQ s (ha.trans_le hst.1) f).upperPositivePart μ hQ hk)
        (M (M ((heatSobolev μ hQ s (ha.trans_le hst.1) f).upperPositivePart μ hQ hk))) := by
    dsimp only [D]
    rw [real_inner_comm,heatGeneratorAt_of_pos μ hQ s (ha.trans_le hst.1)]
    have he := heatGenerator_form μ hQ s (ha.trans_le hst.1) f
      (M (M ((heatSobolev μ hQ s (ha.trans_le hst.1) f).upperPositivePart μ hQ hk)))
    change -2*inner ℝ (heatGenerator μ hQ s (ha.trans_le hst.1) f)
      (SobolevSpace.toLp μ hQ (M (M ((heatSobolev μ hQ s (ha.trans_le hst.1) f).upperPositivePart μ hQ hk)))) = _
    rw [← he,← upper_level_cutoff_energy_eq μ hQ _ hk hχ hs hb hn]
  have hFd (s : ℝ) (hst : s ∈ uIcc a b) : HasDerivAt F (D s) s := by
    have hst' : s ∈ Icc a b := (uIcc_of_le hab) ▸ hst
    rw [hDform s hst']
    exact heat_level_cutoff_norm_hasDerivAt μ hQ f hχ hs hb hn hk s (ha.trans_le hst'.1)
  have hdiff (s : ℝ) (hst : s ∈ Icc a b) : D s+(1/2:ℝ)*E s ≤ 5*I s := by
    have hd := heat_level_cutoff_energy_differential μ hQ f η hχ hs hb hn hrep hgrad hk
      s (ha.trans_le hst.1)
    change deriv F s+(1/2:ℝ)*energyForm μ hQ
      (M ((heatSobolev μ hQ s (ha.trans_le hst.1) f).upperPositivePart μ hQ hk))
      (M ((heatSobolev μ hQ s (ha.trans_le hst.1) f).upperPositivePart μ hQ hk)) ≤ 5*I s at hd
    rw [(hFd s ((uIcc_of_le hab).symm ▸ hst)).deriv,energyForm_self] at hd
    exact hd
  have hh := measurable_energy_integral hab hDc hIc.continuousOn
    (heat_level_cutoff_energy_measurable μ hQ f hχ hb hk)
    (fun _ => mul_nonneg (by norm_num) ENNReal.toReal_nonneg) hFd hdiff
  refine ⟨?_,?_⟩
  · have hi := hh.1.const_mul (1/2:ℝ)
    have heq : (fun s => (1/2:ℝ)*E s) =
        fun s => (energyLp μ (N (P (heatAt μ hQ s f)))).toReal := by
      funext s
      dsimp only [E,U]
      ring
    rwa [heq] at hi
  have hbound := hh.2
  simp only [F,intervalIntegral.integral_const_mul] at hbound
  change F b+(∫ s in a..b, (energyLp μ (N (U s))).toReal) ≤ F a+5*(∫ s in a..b, I s)
  linarith only [hbound]

end RegularPointCoordinates

end

end OAI
