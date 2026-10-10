import OAI.MeasureTheory.Falconer.Angular.AngularTubes
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! # The mean and exceptional mass of a finite original tube count -/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

def angularTubeEvent {d : ℕ} (v : Space d) (W : ℝ) : Set (Sphere d) :=
  {w | ‖perpendicularPart (w:Space d) v‖ ≤ W}

theorem angularTubeEvent_measurable {d : ℕ} (v : Space d) (W : ℝ) :
    MeasurableSet (angularTubeEvent v W) := by
  have hc : Continuous (fun w : Sphere d => v-inner ℝ (w:Space d) v • (w:Space d)) :=
    continuous_const.sub ((continuous_subtype_val.inner (𝕜 := ℝ) continuous_const).smul continuous_subtype_val)
  exact measurableSet_le hc.norm.measurable measurable_const

noncomputable def finiteTubeCount {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) : ℕ := by
  classical
  exact (S.filter (fun i => w ∈ angularTubeEvent (v i) W)).card

theorem finiteTubeCount_eq_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    (finiteTubeCount S v W w : ℝ≥0∞) =
      ∑ i ∈ S, (angularTubeEvent (v i) W).indicator (fun _ => (1:ℝ≥0∞)) w := by
  classical
  simp only [finiteTubeCount,Finset.natCast_card_filter,Set.indicator_apply]

theorem finiteTubeCount_measurable {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) :
    Measurable (fun w : Sphere d => (finiteTubeCount S v W w : ℝ≥0∞)) := by
  simp_rw [finiteTubeCount_eq_sum]
  exact Finset.measurable_sum S (fun i _ =>
    measurable_const.indicator (angularTubeEvent_measurable (v i) W))

theorem finiteTubeCount_mean {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (ν : Measure (Sphere d)) :
    (∫⁻ w, (finiteTubeCount S v W w : ℝ≥0∞) ∂ν) =
      ∑ i ∈ S, ν (angularTubeEvent (v i) W) := by
  simp_rw [finiteTubeCount_eq_sum]
  rw [lintegral_finsetSum S (fun i _ =>
    measurable_const.indicator (angularTubeEvent_measurable (v i) W))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator_const (angularTubeEvent_measurable (v i) W),one_mul]

theorem finiteTubeCount_exceptional {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (ν : Measure (Sphere d))
    {T : ℝ≥0∞} (hT : T ≠ 0) (hTfin : T ≠ ⊤) :
    ν {w | T < (finiteTubeCount S v W w : ℝ≥0∞)} ≤
      (∑ i ∈ S, ν (angularTubeEvent (v i) W))/T := by
  have hsub : {w | T < (finiteTubeCount S v W w : ℝ≥0∞)} ⊆
      {w | T ≤ (finiteTubeCount S v W w : ℝ≥0∞)} := by
    intro w hw
    exact (show T < (finiteTubeCount S v W w : ℝ≥0∞) from hw).le
  apply (measure_mono hsub).trans
  rw [← finiteTubeCount_mean S v W ν]
  exact meas_ge_le_lintegral_div (finiteTubeCount_measurable S v W).aemeasurable hT hTfin

theorem finiteTubeCount_mean_bound {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (ν : Measure (Sphere d)) {W L s : ℝ} (hW : 0 < W)
    (hv : ∀ i ∈ S, v i ≠ 0)
    (hball : ∀ i ∈ S, ∀ x : Space d,
      ν {w : Sphere d | dist (w:Space d) x < 3*W/‖v i‖} ≤
        ENNReal.ofReal (L*(3*W/‖v i‖)^s)) :
    (∫⁻ w, (finiteTubeCount S v W w : ℝ≥0∞) ∂ν) ≤
      ∑ i ∈ S, 2*ENNReal.ofReal (L*(3*W/‖v i‖)^s) := by
  rw [finiteTubeCount_mean]
  exact Finset.sum_le_sum (fun i hi => perpendicular_direction_measure ν (hv i hi) hW (hball i hi))

end Falconer

end OAI
