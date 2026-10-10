import OAI.Geometry.RCD.Heat.HeatLocalEnergy

namespace OAI

/-! # A time-cutoff Caccioppoli bound for the actual heat flow

Choosing the initial slice in an earlier time interval replaces its
mass by the space-time mass. The same bound controls every later slice
and the cutoff energy integrated over the later cylinder.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

theorem exists_time_le_integral_mean {J : ℝ → ℝ} (hJ : Continuous J)
    (hJn : ∀ t, 0 ≤ J t) {a c b : ℝ} (hac : a < c) (hcb : c ≤ b) :
    ∃ s ∈ Icc a c, J s ≤ (∫ t in a..b, J t)/(c-a) := by
  obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc a c).Nonempty from ⟨a,le_rfl,hac.le⟩) hJ.continuousOn
  have hconst : (c-a)*J s ≤ ∫ t in a..c, J t := by
    have hh := intervalIntegral.integral_mono_on hac.le
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => J s) volume a c)
      (hJ.intervalIntegrable (μ := volume) a c) (fun t ht => hmin ht)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have hlarge : (∫ t in a..c, J t) ≤ ∫ t in a..b, J t :=
    intervalIntegral.integral_mono_interval le_rfl hac.le hcb
      (Eventually.of_forall hJn) (hJ.intervalIntegrable (μ := volume) a b)
  refine ⟨s,hs,(le_div_iff₀ (sub_pos.mpr hac)).mpr ?_⟩
  simpa only [mul_comm] using hconst.trans hlarge

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

theorem heat_level_cylinder_energy (f : Lp ℝ 2 μ)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ (1:ℝ≥0)) (hn : ∀ x, 0 ≤ χ x)
    {S Ω : Set X} (hS : MeasurableSet S) (hΩ : MeasurableSet Ω)
    (hplateau : ∀ x ∈ S, χ x = 1) (hsupp : tsupport χ ⊆ Ω)
    {k : ℝ} (hk : 0 ≤ k) {a c b : ℝ} (ha : 0 < a) (hac : a < c) (hcb : c ≤ b) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable 1 hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    let Y := ∫ s in a..b, ∫ x in Ω, (P (heatAt μ hQ s f) x)^2 ∂μ
    let Q := (c-a)⁻¹+5*(L:ℝ)^2
    (∫ s in c..b, (energyLp μ (N (P (heatAt μ hQ s f)))).toReal) ≤ Q*Y ∧
      ∀ t ∈ Icc c b, (∫ x in S, (P (heatAt μ hQ t f) x)^2 ∂μ) ≤ Q*Y := by
  intro N P Y Q
  let U := fun s => P (heatAt μ hQ s f)
  let J := fun s => ∫ x in Ω, (U s x)^2 ∂μ
  let E := fun s => (energyLp μ (N (U s))).toReal
  have hPc : Continuous P := (upperLevelPart_lipschitz k).continuous_compLp (upperLevelPart_zero hk)
  have hJc : Continuous J :=
    continuous_setIntegral_sq_path μ (hPc.comp (heatAt_continuous μ hQ f)) hΩ
  have hJn (s : ℝ) : 0 ≤ J s := integral_nonneg fun x => sq_nonneg (U s x)
  obtain ⟨s,hsa,hJs⟩ := exists_time_le_integral_mean hJc hJn hac hcb
  have hslice (t : ℝ) (ht : t ∈ Icc c b) :
      (∫ x in S, (U t x)^2 ∂μ)+(∫ r in c..t, E r) ≤ Q*Y := by
    have hst : s ≤ t := hsa.2.trans ht.1
    have hlocal := heat_level_local_energy μ hQ f hχ hs hb hn hS hΩ hplateau hsupp hk
      (ha.trans_le hsa.1) hst
    have hEsub : (∫ r in c..t, E r) ≤ ∫ r in s..t, E r :=
      intervalIntegral.integral_mono_interval hsa.2 ht.1 le_rfl
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hlocal.1
    have hJsub : (∫ r in s..t, J r) ≤ Y :=
      intervalIntegral.integral_mono_interval hsa.1 hst ht.2
        (Eventually.of_forall hJn) (hJc.intervalIntegrable (μ := volume) a b)
    have hbound := hlocal.2
    change (∫ x in S, (U t x)^2 ∂μ)+(∫ r in s..t, E r) ≤
      J s+5*(L:ℝ)^2*(∫ r in s..t, J r) at hbound
    have hmul := mul_le_mul_of_nonneg_left hJsub (by positivity : 0 ≤ 5*(L:ℝ)^2)
    have hJs' : J s ≤ (c-a)⁻¹*Y := by simpa only [div_eq_mul_inv,mul_comm] using hJs
    dsimp only [Q]
    nlinarith only [hbound,hEsub,hmul,hJs']
  constructor
  · have hh := hslice b ⟨hcb,le_rfl⟩
    have hn : 0 ≤ ∫ x in S, (U b x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    linarith only [hh,hn]
  · intro t ht
    have hh := hslice t ht
    have hn : 0 ≤ ∫ r in c..t, E r :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => ENNReal.toReal_nonneg)
    linarith only [hh,hn]

end RegularPointCoordinates

end

end OAI
