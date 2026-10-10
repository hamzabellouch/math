import OAI.MeasureTheory.Falconer.Measures.FrequencyMeasure
import OAI.MeasureTheory.Falconer.Slicing.GaussianLocalization

namespace OAI

/-! # Gaussian localization for the actual frequency-shell law -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurableSet_radialFrequencyAnnulus (B : ℝ) : MeasurableSet (radialFrequencyAnnulus B) :=
  (isClosed_le continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

instance radialFrequencyMeasure_finite (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (B : ℝ) :
    IsFiniteMeasure (radialFrequencyMeasure ν B) := by
  have hsub : radialFrequencyAnnulus B ⊆ Icc (-2*|B|) (2*|B|) := by
    intro t ht
    have hab : |t| ≤ 2*|B| := ht.2.trans (by nlinarith [le_abs_self B])
    simpa only [mem_Icc,neg_mul] using abs_le.mp hab
  have : IsFiniteMeasure (volume.restrict (radialFrequencyAnnulus B)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      apply (measure_mono hsub).trans_lt
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top⟩
  unfold radialFrequencyMeasure
  infer_instance

theorem radial_frequency_support (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (B : ℝ) :
    ∀ᵐ v ∂radialFrequencyMeasure ν B, B ≤ ‖v‖ ∧ ‖v‖ ≤ 2*B := by
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  rw [radialFrequencyMeasure,ae_map_iff (p := fun v : Space d => B ≤ ‖v‖ ∧ ‖v‖ ≤ 2*B) hm.aemeasurable
    ((isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isClosed_le continuous_norm continuous_const).measurableSet)]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [self_mem_ae_restrict (measurableSet_radialFrequencyAnnulus B)] with t ht
  change B ≤ |t| ∧ |t| ≤ 2*B at ht
  exact Filter.Eventually.of_forall (fun w => by
    simpa only [radialFrequencyMap,norm_smul,Real.norm_eq_abs,sphere_norm,mul_one] using ht)

theorem radial_frequency_polynomial_balls (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {B R L s : ℝ} (hB : 1 ≤ B) (hBR : B ≤ R) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s)) :
    ∀ x : Space d, ∀ r : ℝ, 1 ≤ r →
      radialFrequencyMeasure ν B (ball x r) ≤
        ENNReal.ofReal ((8*(2:ℝ)^s*L/B^s)*r^(s+1)) := by
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have hR₀ : 0 < R := hB₀.trans_le hBR
  intro x r hr
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hscale : 1/R ≤ 2*r/B := by
    have h₁ : 1/R ≤ 1/B := one_div_le_one_div_of_le hB₀ hBR
    exact h₁.trans ((div_le_div_iff_of_pos_right hB₀).mpr (by linarith))
  have h := radial_frequency_ball_bound ν hB₀ hr₀ hL hs hmass hscale hball x
  have he : 8*r*L*(2*r/B)^s = (8*(2:ℝ)^s*L/B^s)*r^(s+1) := by
    rw [Real.div_rpow (by positivity) hB₀.le,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr₀.le,
      Real.rpow_add hr₀,Real.rpow_one]
    ring
  simpa only [he] using h

theorem radial_frequency_gaussian (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {B R L s : ℝ} {k : ℕ} (hB : 1 ≤ B) (hBR : B ≤ R) (hL : 1 ≤ L)
    (hs : 0 ≤ s) (hsk : s+1 ≤ k) (hmass : ν univ ≤ 1)
    (hball : ∀ x : Space d, ∀ r : ℝ, 1/R ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s))
    (u : Space d) :
    (∫ v, Real.exp (-2*(dist u v)^2) ∂radialFrequencyMeasure ν B) ≤
      Real.exp 1*(8*(2:ℝ)^s*L/B^s)*gaussianBallConstant k*
        Real.exp (-‖u‖^2/(16*B^2)) := by
  exact gaussian_localized_mass (radialFrequencyMeasure ν B) hB
    (by have : 0 < B := zero_lt_one.trans_le hB; positivity) hsk
    ((radial_frequency_support ν B).mono (fun _ h => h.2))
    (radial_frequency_polynomial_balls ν hB hBR hL hs hmass hball) u

end Falconer

end OAI
