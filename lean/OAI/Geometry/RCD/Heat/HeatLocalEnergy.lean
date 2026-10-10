import OAI.Geometry.RCD.Heat.HeatLevelIntegral
import OAI.Geometry.RCD.Sobolev.LocalizedCutoffNorms
import OAI.Geometry.RCD.Sobolev.NestedBallCutoff

namespace OAI

/-! # Local space-time energy of heat upper levels

Cutoff locality restricts the error to its outer support. A plateau on
the inner set gives the local L² mass at the final time.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem continuous_setIntegral_sq_path {u : ℝ → Lp ℝ 2 μ} (hu : Continuous u)
    {S : Set X} (hS : MeasurableSet S) :
    Continuous (fun t => ∫ x in S, (u t x)^2 ∂μ) := by
  let w : X → ℝ := S.indicator (fun _ => 1)
  have hw : MemLp w ∞ μ := by
    apply memLp_top_of_bound ((measurable_const.indicator hS).aestronglyMeasurable) 1
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ S <;> simp [hx]
  have he : (fun t => ∫ x in S, (u t x)^2 ∂μ) =
      fun t => ∫ x, w x*(u t x)^2 ∂μ := by
    funext t
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ S <;> simp [w,hx]
  rw [he]
  exact continuous_weighted_square_path μ hu hw

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] [μ.Regular] in
theorem cutoff_L2_norm_sq_le_setIntegral (f : Lp ℝ 2 μ)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hb : ∀ x, |χ x| ≤ B) {Ω : Set X} (hΩ : MeasurableSet Ω)
    (hsupp : tsupport χ ⊆ Ω) :
    ‖lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb) f‖^2 ≤
      (B:ℝ)^2*∫ x in Ω, (f x)^2 ∂μ := by
  let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb)
  have hi : Integrable (fun x => χ x^2*(f x)^2) μ := by
    apply (Lp.memLp (N f)).integrable_sq.congr
    filter_upwards [lpMultiplier_coe μ
      (boundedMultiplier μ χ hχ.continuous.measurable B hb) f,
      boundedMultiplier_coe μ χ hχ.continuous.measurable B hb] with x hx hv
    rw [hx,hv,mul_pow]
  rw [cutoff_L2_norm_sq μ f hχ hb,← integral_const_mul,← integral_indicator hΩ]
  apply integral_mono_ae hi (((Lp.memLp f).integrable_sq.const_mul ((B:ℝ)^2)).indicator hΩ)
  apply Eventually.of_forall
  intro x
  change χ x^2*(f x)^2 ≤ Ω.indicator (fun x => (B:ℝ)^2*(f x)^2) x
  by_cases hx : x ∈ Ω
  · rw [indicator_of_mem hx]
    have hc : χ x^2 ≤ (B:ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) B.coe_nonneg).mpr (hb x)
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))]
    simp only [zero_pow (by decide : (2:ℕ)≠0),zero_mul,le_refl]

theorem heat_level_error_continuous (f : Lp ℝ 2 μ) (η : SobolevSpace μ hQ)
    {k : ℝ} (hk : 0 ≤ k) {A : ℝ≥0}
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A) :
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    Continuous (fun s => ∫ x, (P (heatAt μ hQ s f) x)^2*
      (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ) := by
  intro P
  have hgm : MemLp (fun x => (SobolevSpace.minimalSlope μ hQ η x)^2) ∞ μ := by
    apply memLp_top_of_bound ((Lp.aestronglyMeasurable _).pow 2) ((A:ℝ)^2)
    filter_upwards [hgrad] with x hx
    change ‖(SobolevSpace.minimalSlope μ hQ η x)^2‖ ≤ (A:ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) A.coe_nonneg).mpr hx
  have hPc : Continuous P := (upperLevelPart_lipschitz k).continuous_compLp (upperLevelPart_zero hk)
  have hh := continuous_weighted_square_path μ (hPc.comp (heatAt_continuous μ hQ f)) hgm
  convert hh using 1
  funext s
  apply integral_congr_ae
  exact Eventually.of_forall fun x => mul_comm _ _

theorem heat_level_local_energy (f : Lp ℝ 2 μ)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ (1:ℝ≥0)) (hn : ∀ x, 0 ≤ χ x)
    {S Ω : Set X} (hS : MeasurableSet S) (hΩ : MeasurableSet Ω)
    (hplateau : ∀ x ∈ S, χ x = 1) (hsupp : tsupport χ ⊆ Ω)
    {k : ℝ} (hk : 0 ≤ k) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable 1 hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    IntervalIntegrable (fun s => (energyLp μ (N (P (heatAt μ hQ s f)))).toReal) volume a b ∧
      (∫ x in S, (P (heatAt μ hQ b f) x)^2 ∂μ)+
          ∫ s in a..b, (energyLp μ (N (P (heatAt μ hQ s f)))).toReal ≤
        (∫ x in Ω, (P (heatAt μ hQ a f) x)^2 ∂μ)+
          5*(L:ℝ)^2*(∫ s in a..b, ∫ x in Ω, (P (heatAt μ hQ s f) x)^2 ∂μ) := by
  intro N P
  let η := SobolevSpace.ofLipschitzCompact μ hQ hχ hs
  have hη := SobolevSpace.ofLipschitzCompact_coe μ hQ hχ hs
  have hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ L := by
    filter_upwards [SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip μ hQ hχ hs,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x hx hn
    rwa [abs_of_nonneg hn]
  have hh := heat_level_cutoff_energy_integral μ hQ f η hχ hs hb hn hη hgrad hk ha hab
  refine ⟨hh.1,?_⟩
  let U := fun s => P (heatAt μ hQ s f)
  let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
  have hPc : Continuous P := (upperLevelPart_lipschitz k).continuous_compLp (upperLevelPart_zero hk)
  have hUc : Continuous U := hPc.comp (heatAt_continuous μ hQ f)
  have hinit : ‖N (U a)‖^2 ≤ ∫ x in Ω, (U a x)^2 ∂μ := by
    simpa only [NNReal.coe_one,one_pow,one_mul] using
      cutoff_L2_norm_sq_le_setIntegral μ (U a) hχ hb hΩ hsupp
  have hfinal : (∫ x in S, (U b x)^2 ∂μ) ≤ ‖N (U b)‖^2 := by
    rw [cutoff_L2_norm_sq μ (U b) hχ hb]
    have hi : Integrable (fun x => χ x^2*(U b x)^2) μ := by
      apply (Lp.memLp (N (U b))).integrable_sq.congr
      filter_upwards [lpMultiplier_coe μ
        (boundedMultiplier μ χ hχ.continuous.measurable 1 hb) (U b),
        boundedMultiplier_coe μ χ hχ.continuous.measurable 1 hb] with x hx hv
      rw [hx,hv,mul_pow]
    calc
      _ = ∫ x in S, χ x^2*(U b x)^2 ∂μ := by
        apply setIntegral_congr_fun hS
        intro x hx
        change (U b x)^2 = χ x^2*(U b x)^2
        rw [hplateau x hx,one_pow,one_mul]
      _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall fun x => by positivity)
  let I := fun s => ∫ x, (U s x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ
  let J := fun s => ∫ x in Ω, (U s x)^2 ∂μ
  have hIc : Continuous I := heat_level_error_continuous μ hQ f η hk hgrad
  have hJc : Continuous J := continuous_setIntegral_sq_path μ hUc hΩ
  have hIJ (s : ℝ) (hst : s ∈ Icc a b) : I s ≤ (L:ℝ)^2*J s := by
    exact cutoff_gradient_weight_le_setIntegral μ hQ
      ((heatSobolev μ hQ s (ha.trans_le hst.1) f).upperPositivePart μ hQ hk) η hη hgrad hΩ hsupp
  have htime := intervalIntegral.integral_mono_on hab
    (hIc.intervalIntegrable (μ := volume) a b)
    ((hJc.const_mul ((L:ℝ)^2)).intervalIntegrable (μ := volume) a b) hIJ
  rw [intervalIntegral.integral_const_mul] at htime
  have hmass := hh.2
  change ‖N (U b)‖^2+_ ≤ ‖N (U a)‖^2+5*(∫ s in a..b, I s) at hmass
  have hmul := mul_le_mul_of_nonneg_left htime (by norm_num : (0:ℝ)≤5)
  change (∫ x in S, (U b x)^2 ∂μ)+_ ≤ J a+5*(L:ℝ)^2*(∫ s in a..b, J s)
  linarith only [hmass,hinit,hfinal,hmul]

end RegularPointCoordinates

end

end OAI
