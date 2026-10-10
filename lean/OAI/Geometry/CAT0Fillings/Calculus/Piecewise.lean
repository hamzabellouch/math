import Mathlib
import OAI.Geometry.CAT0Fillings.Calculus.ClosedLevel
import OAI.Geometry.CAT0Fillings.Calculus.VectorLimit
import OAI.Geometry.CAT0Fillings.Swept.Current

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def scalarAverage (F : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  ((∫ z in (0:ℝ)..(t+ε), F z)-(∫ z in (0:ℝ)..(t-ε), F z))/(2*ε)
noncomputable def scalarAverageDeriv (F : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  (F (t+ε)-F (t-ε))/(2*ε)

lemma scalarAverage_hasDerivAt {F : ℝ → ℝ} (hF : Continuous F) (ε t : ℝ) :
    HasDerivAt (scalarAverage F ε) (scalarAverageDeriv F ε t) t := by
  have hd (s : ℝ) : HasDerivAt (fun y : ℝ => ∫ z in (0:ℝ)..y, F z) (F s) s :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 s)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hh := (((hd (t+ε)).comp t ((hasDerivAt_id t).add_const ε)).sub
    ((hd (t-ε)).comp t ((hasDerivAt_id t).sub_const ε))).div_const (2*ε)
  simp only [Function.comp_def,id_eq,mul_one,Pi.sub_apply] at hh
  convert hh using 1 <;> rfl

lemma continuous_scalarAverageDeriv {F : ℝ → ℝ} (hF : Continuous F) (ε : ℝ) :
    Continuous (scalarAverageDeriv F ε) :=
  ((hF.comp (continuous_id.add continuous_const)).sub
    (hF.comp (continuous_id.sub continuous_const))).div_const _

lemma scalarAverageDeriv_bound {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |scalarAverageDeriv F ε t| ≤ K := by
  have hh := hF.dist_le_mul (t+ε) (t-ε)
  rw [Real.dist_eq,Real.dist_eq,show t+ε-(t-ε) = 2*ε by ring,
    abs_of_pos (show 0 < 2*ε by positivity)] at hh
  dsimp [scalarAverageDeriv]
  rw [abs_div,abs_of_pos (show 0 < 2*ε by positivity)]
  exact (div_le_iff₀ (mul_pos (by norm_num) hε)).mpr hh

lemma scalarAverage_lipschitz {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {ε : ℝ} (hε : 0 < ε) : LipschitzWith K (scalarAverage F ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (scalarAverage_hasDerivAt hF.continuous ε t).differentiableAt)
  intro t
  rw [←NNReal.coe_le_coe,coe_nnnorm,(scalarAverage_hasDerivAt hF.continuous ε t).deriv,Real.norm_eq_abs]
  exact scalarAverageDeriv_bound hF hε t

lemma scalarAverage_integral {F : ℝ → ℝ} (hF : Continuous F) (ε t : ℝ) :
    scalarAverage F ε t = (∫ z in (t-ε)..(t+ε), F z)/(2*ε) := by
  dsimp [scalarAverage]
  congr 1
  exact intervalIntegral.integral_interval_sub_left (hF.intervalIntegrable 0 (t+ε))
    (hF.intervalIntegrable 0 (t-ε))

lemma scalarAverage_error {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |scalarAverage F ε t-F t| ≤ K*ε := by
  have hab : t-ε ≤ t+ε := by linarith
  have hh : |∫ z in (t-ε)..(t+ε), (F z-F t)| ≤ (K*ε)*(2*ε) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := t-ε) (b := t+ε)
      (f := fun z => F z-F t) (C := K*ε) (fun z hz => by
        rw [uIoc_of_le hab] at hz
        have hd : |z-t| ≤ ε := abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
        have hf := hF.dist_le_mul z t
        rw [Real.dist_eq,Real.dist_eq] at hf
        rw [Real.norm_eq_abs]
        exact hf.trans (mul_le_mul_of_nonneg_left hd K.coe_nonneg))
    simpa only [Real.norm_eq_abs,show t+ε-(t-ε) = 2*ε by ring,
      abs_of_pos (show 0 < 2*ε by positivity)] using hb
  have he : scalarAverage F ε t-F t = (∫ z in (t-ε)..(t+ε), (F z-F t))/(2*ε) := by
    rw [scalarAverage_integral hF.continuous,intervalIntegral.integral_sub
      (hF.continuous.intervalIntegrable _ _) intervalIntegrable_const,intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [he,abs_div,abs_of_pos (show 0 < 2*ε by positivity)]
  exact (div_le_iff₀ (mul_pos (by norm_num) hε)).mpr hh

lemma scalarAverageDeriv_tendsto {F : ℝ → ℝ} {D t : ℝ} (hd : HasDerivAt F D t)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (hep : ∀ j, 0 < e j) :
    Tendsto (fun j => scalarAverageDeriv F (e j) t) atTop (𝓝 D) := by
  have he' : Tendsto e atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨he,Eventually.of_forall fun j => (hep j).ne'⟩
  have hen : Tendsto (fun j => -e j) atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [neg_zero] using he.neg,Eventually.of_forall fun j => neg_ne_zero.mpr (hep j).ne'⟩
  have hh := ((hd.tendsto_slope_zero.comp he').add (hd.tendsto_slope_zero.comp hen)).div_const (2:ℝ)
  have heq (j : ℕ) : scalarAverageDeriv F (e j) t =
      ((e j)⁻¹ • (F (t+e j)-F t) + (-e j)⁻¹ • (F (t+-e j)-F t))/2 := by
    dsimp [scalarAverageDeriv]
    simp only [←sub_eq_add_neg]
    field_simp
    ring
  simp only [Function.comp_def] at hh
  convert hh using 1
  · funext j
    exact heq j
  · congr 1
    ring

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_countable {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {S : Set ℝ} (hS : S.Countable) (hd : ∀ t ∉ S, DifferentiableAt ℝ F t)
    (hz : IsCycle T) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => deriv F ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hep (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (t : ℝ) : |deriv F t| ≤ K := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hF (x₀ := t)
  have hlevel : ∀ᵐ w ∂q.atlasMeasure, ∀ a ∈ S,
      (q.inclusion P) (q.atlasParam w) = a → (q.closedGradient P) w = 0 := by
    exact (ae_ball_iff hS).mpr fun a _ => q.closedGradient_level_zero hz P a
  apply q.closed_chain_uniform_smul hF (measurable_deriv F) K.coe_nonneg hb
    (fun j => scalarAverage F (e j)) (fun j => scalarAverageDeriv F (e j)) (fun _ => K)
    (fun j => scalarAverage_lipschitz hF (hep j))
    (fun j => scalarAverage_hasDerivAt hF.continuous (e j))
    (fun j => continuous_scalarAverageDeriv hF.continuous (e j))
    (fun j => scalarAverageDeriv_bound hF (hep j)) (fun j => K*e j)
    (by simpa only [mul_zero] using he.const_mul (K:ℝ))
    (fun j => scalarAverage_error hF (hep j)) P
  filter_upwards [hlevel] with w hw
  by_cases hs : (q.inclusion P) (q.atlasParam w) ∈ S
  · rw [hw _ hs rfl]
    simp only [smul_zero]
    exact tendsto_const_nhds
  · exact (scalarAverageDeriv_tendsto (hd _ hs).hasDerivAt he hep).smul_const _

end CAT0Fillings.ChartGeometry
end

end OAI
