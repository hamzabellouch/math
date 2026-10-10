import OAI.Probability.SLE.Gauge.SerpentineActualGuide
import OAI.Probability.SLE.Gauge.SerpentineMarkedReflection
import OAI.Probability.SLE.Gauge.ExperimentClearance
import OAI.Probability.SLE.Geometry.MarkedSurvivingBall

namespace OAI

/-! Successful physical prefixes leave a definite ball around the marked
point in the actual surviving domain, hence finish before a fixed radius level. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma good_physicalFit_ball_survives {s : ℝ} (hs : 0 < s) (w : ℂ)
    (hwy : s ≤ w.im) (hwr : 0 ≤ w.re) {m : ℕ} (hm : 0 < m)
    (γ : ℝ≥0 → ℂ) (τ : WithTop ℝ≥0) (ε : ℝ)
    (hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => γ) (fun _ => τ)
      (physicalFitChart s w m) ε) :
    ball w (s / 20) ⊆ survivingDomain γ (τ.untopD 0) := by
  apply marked_ball_survives γ (τ.untopD 0) w (by positivity) (by linarith)
  rintro q ⟨t, ht, rfl⟩
  obtain ⟨z, ⟨hz, _⟩, he⟩ := hpref.2.1 ht
  change physicalFitChart s w m z = γ t at he
  rw [← he]
  rcases physicalFitChart_low_or_right hs w hwy hm hz.2 with hlo | hright
  · left
    linarith
  · right
    rw [abs_of_nonneg hwr] at hright
    linarith

theorem good_physicalExperiment_ball_survives {s : ℝ} (hs : 0 < s) (w : ℂ)
    (hwy : s ≤ w.im) {m : ℕ} (hm : 0 < m)
    (γ : ℝ≥0 → ℂ) (τ : WithTop ℝ≥0) (ε : ℝ)
    (hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => γ) (fun _ => τ)
      (physicalExperimentChart s w m) ε) :
    ball w (s / 20) ⊆ survivingDomain γ (τ.untopD 0) := by
  by_cases hwr : 0 ≤ w.re
  · have hchart : physicalExperimentChart s w m = physicalFitChart s w m := by
      funext z
      simp only [physicalExperimentChart, ite_eq_left hwr]
    apply good_physicalFit_ball_survives hs w hwy hwr hm γ τ ε
    simpa only [hchart] using hpref
  · have hneg : w.re < 0 := lt_of_not_ge hwr
    have hp : () ∈ GoodRibbonPrefix (fun _ : Unit => (loewnerMirror ∘ γ)) (fun _ => τ)
        (physicalFitChart s (loewnerMirror w) m) ε := by
      rw [goodRibbonPrefix_physical_negative _ _ hneg m ε] at hpref
      simpa only [Function.comp_def] using hpref
    have hb := good_physicalFit_ball_survives hs (loewnerMirror w)
      (by simpa only [loewnerMirror_im] using hwy)
      (by simp only [loewnerMirror_re]; linarith) hm (loewnerMirror ∘ γ) τ ε hp
    intro z hz
    apply (loewnerMirror_surviving γ (τ.untopD 0) z).mp
    apply hb
    simpa only [mem_ball, loewnerMirror_dist] using hz

def experimentRadiusLevel (s : ℝ) : ℝ := -Real.log (s / 80)

lemma experimentRadiusLevel_nonneg {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ experimentRadiusLevel s := by
  unfold experimentRadiusLevel
  exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (by linarith))

lemma experimentRadiusLevel_cutoff {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    (2 * w.im) * Real.exp (-experimentRadiusLevel s) < s / 20 := by
  have hy := (Complex.im_le_norm w).trans hw
  rw [experimentRadiusLevel, neg_neg, Real.exp_log (by positivity : 0 < s / 80)]
  nlinarith

theorem good_physicalExperiment_before_radius
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    {s : ℝ} (hs : 0 < s) (w : ℂ) (hwn : ‖w‖ ≤ 1) (hwy : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (τ : WithTop ℝ≥0) (ε : ℝ)
    (hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => γ) (fun _ => τ)
      (physicalExperimentChart s w m) ε) :
    τ < radiusLevelTime γ G w (experimentRadiusLevel s) ∧
      w ∈ survivingDomain γ (τ.untopD 0) := by
  have hb := good_physicalExperiment_ball_survives hs w hwy hm γ τ ε hpref
  have hlive := hb (mem_ball_self (by positivity : 0 < s / 20))
  refine ⟨?_, hlive⟩
  have hh := completion_before_radiusLevelTime_of_prefix_lower hU hw (τ.untopD 0) w
    (experimentRadiusLevel s) (s / 20) (fun t ht => by
      have hbt := hb.trans (survivingDomain_antitone γ ht)
      exact ⟨hbt (mem_ball_self (by positivity)),
        fullRadius_lower_of_surviving_ball hU hw t w (by positivity) hbt⟩)
    (experimentRadiusLevel_cutoff hs w hwn)
  cases he : τ with
  | top => exact (hpref.1 he).elim
  | coe T =>
    have hh' : (T : ℝ≥0∞) < radiusLevelTime γ G w (experimentRadiusLevel s) := by
      simpa only [he, WithTop.untopD_coe] using hh
    exact_mod_cast hh'

end SLEExactGauge.Serpentine

end

end OAI
