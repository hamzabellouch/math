import OAI.MeasureTheory.Falconer.Geometry.CubeBallBound
import OAI.MeasureTheory.Falconer.Measures.FrostmanWeakLimit

namespace OAI

/-! # The application-level Frostman input proved in every ambient dimension

Finite dyadic capacities give probability approximants carried by the compact
set. The finite cube count gives uniform ball bounds; a compact weak limit
preserves them. Only exponents strictly above half the dimension are selected
in the published-input discharge.
-/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem frostman_probability {d : ℕ} (hd : 1 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E) {s : ℝ≥0}
    (hs : 0 < s) (hDim : (s : ℝ≥0∞) < dimH E) :
    ∃ μ : ProbabilityMeasure (Space d), (μ : Measure (Space d)) Eᶜ = 0 ∧
      ∃ C : ℝ, 0 < C ∧ FrostmanBallBound (μ : Measure (Space d)) (s:ℝ) C := by
  obtain ⟨Q,hQ,hEQ⟩ := exists_containing_cube E hE
  obtain ⟨c,hc,μ,hμ⟩ := cube_probability_sequence hd E hE hs hDim Q hQ hEQ
  have hcarry : ∀ K, (μ K : Measure (Space d)) Q.carrierᶜ = 0 := fun K =>
    measure_mono_null (compl_subset_compl.mpr hEQ) (hμ K).1
  obtain ⟨C,hC,hball⟩ := eventual_cube_ball_bounds Q hQ
    (by exact_mod_cast hs) hc μ hcarry (fun K => (hμ K).2)
  obtain ⟨ν,hν,hfrost⟩ := frostman_of_eventual_ball_bounds E hE μ
    (fun K => (hμ K).1) (s:ℝ) C hball
  exact ⟨ν,hν,C,hC,hfrost⟩

theorem published_frostman_above_half : PublishedFrostmanAboveHalf := by
  intro d hd E hE hDim
  have hhalf : (d : ℝ≥0∞)/2 = ENNReal.ofReal ((d:ℝ)/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_natCast]
    norm_num
  have hu : (d : ℝ≥0∞)/2 < ENNReal.ofReal ((d:ℝ)/2+1) := by
    rw [hhalf]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  obtain ⟨a,ha0,ha⟩ := exists_between (lt_min hDim hu)
  have hatop : a ≠ ∞ := (ha.trans_le (min_le_right _ _)).ne_top
  have halow : (d:ℝ)/2 < a.toReal := by
    rw [hhalf] at ha0
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hatop).mpr ha0
    simpa only [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (d:ℝ)/2)] using hh
  have hahigh : a.toReal < (d:ℝ)/2+1 := by
    have hh := (ENNReal.toReal_lt_toReal hatop ENNReal.ofReal_ne_top).mpr
      (ha.trans_le (min_le_right _ _))
    simpa only [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (d:ℝ)/2+1)] using hh
  have has : 0 < a.toNNReal := ENNReal.toNNReal_pos (bot_le.trans_lt ha0).ne' hatop
  obtain ⟨μ,hμ,C,hC,hball⟩ := frostman_probability (by omega : 1 ≤ d) E hE has
    (by rw [ENNReal.coe_toNNReal hatop]; exact ha.trans_le (min_le_left _ _))
  refine ⟨a.toReal,halow,hahigh,μ,hμ,C,hC,?_⟩
  simpa only [ENNReal.toReal] using hball

end Falconer

end OAI
