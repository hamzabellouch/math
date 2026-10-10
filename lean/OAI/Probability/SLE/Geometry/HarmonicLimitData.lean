import OAI.Probability.SLE.Geometry.HarmonicPathMaximum

namespace OAI

/-! A bounded measurable terminal variable for each localized harmonic
test, with the L1 error required in the full-path maximal estimate. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target
namespace SmoothDomainExhaustion
variable {U : Set (ℝ×ℝ)} (e : SmoothDomainExhaustion U 0)

theorem harmonic_limit_data
    (W : WienerLaw) (hW : IsWiener W) (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (C : ℝ≥0) (huC : ∀ z∈U, |u z|≤C) :
    ∃ Y : Driver×Driver → ℝ, Measurable Y ∧ (∀ b, |Y b|≤C) ∧
      (∀ᵐ b ∂W.prod W, Tendsto (fun n => u (planarWiener (e.stop T n b) b)) atTop (𝓝 (Y b))) ∧
      Tendsto (fun n => ∫ b, |u (planarWiener (e.stop T n b) b)-Y b| ∂W.prod W) atTop (𝓝 0) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let X (n : ℕ) (b : Driver×Driver) := u (planarWiener (e.stop T n b) b)
  have hM := e.harmonic_stopped_martingale W hW T hU u hu hhar C huC
  have hXb (n b) : |X n b|≤C := huC _ (e.stop_mem_domain T n b _ le_rfl)
  have hXm (n) : Measurable (X n) := ((hM.1 n).mono ((e.stopFiltration T).le n)).measurable
  have hLp (n) : eLpNorm (X n) 1 (W.prod W) ≤ C := by
    have hb : ∀ᵐ b ∂W.prod W, ‖X n b‖≤C :=
      Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hXb n b
    simpa using eLpNorm_le_of_ae_bound (p := 1) (hXm n).aestronglyMeasurable hb
  let L := (e.stopFiltration T).limitProcess X (W.prod W)
  have hLm : Measurable L := Filtration.stronglyMeasurable_limit_process'.measurable
  have hlim : ∀ᵐ b ∂W.prod W, Tendsto (fun n => X n b) atTop (𝓝 (L b)) :=
    hM.submartingale.ae_tendsto_limitProcess hLp
  let clip (v : ℝ) := max (-(C:ℝ)) (min (C:ℝ) v)
  have hclip (n b) : clip (X n b)=X n b := by
    dsimp only [clip]
    rw [min_eq_right (abs_le.mp (hXb n b)).2,max_eq_right (abs_le.mp (hXb n b)).1]
  let Y (b : Driver×Driver) := clip (L b)
  have hYm : Measurable Y := measurable_const.max (measurable_const.min hLm)
  have hYb (b) : |Y b|≤C := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _,max_le (by linarith [C.coe_nonneg]) (min_le_left _ _)⟩
  have hconv : ∀ᵐ b ∂W.prod W, Tendsto (fun n => X n b) atTop (𝓝 (Y b)) := by
    filter_upwards [hlim] with b hb
    have hclipcont : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
    have hh := hclipcont.continuousAt.tendsto.comp hb
    change Tendsto (fun n => clip (X n b)) atTop (𝓝 (Y b)) at hh
    simpa only [hclip] using hh
  refine ⟨Y,hYm,hYb,hconv,?_⟩
  have hh : Tendsto (fun n => ∫ b, |X n b-Y b| ∂W.prod W) atTop
      (𝓝 (∫ _b : Driver×Driver, (0:ℝ) ∂W.prod W)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2:ℝ)*C)
      (fun n => ((hXm n).sub hYm).abs.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs,abs_abs]
        exact (abs_sub _ _).trans (by linarith [hXb n b,hYb b])
    · filter_upwards [hconv] with b hb
      simpa only [Pi.sub_apply,sub_self,abs_zero] using (hb.sub_const (Y b)).abs
  simpa only [integral_zero] using hh

end SmoothDomainExhaustion
end SLEExactGauge

end

end OAI
