import OAI.Probability.SLE.Gauge.RibbonAccessGuide
import OAI.Probability.SLE.Gauge.RibbonRouteLifting
import OAI.Probability.SLE.Gauge.RibbonLimitPassageGeometry

namespace OAI

/-! A fixed compact coordinate patch for the actual one-step ribbon. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

/-- The length-four patch used for one step and its two-sided waypoint routes. -/
def ribbonStepPatch (k : ℝ) : Set ℂ :=
  {z | k - 1 ≤ z.re ∧ z.re ≤ k + 3 ∧ |z.im| ≤ 1}

/-- A padded compact patch in coordinates relative to the current front. -/
def ribbonStepCompact : Set ℂ :=
  {z | -(1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 5 / 2 ∧ |z.im| ≤ 1 / 2}

theorem ribbonStepCompact_isCompact : IsCompact ribbonStepCompact := by
  have hc : IsClosed ribbonStepCompact :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le Complex.continuous_im.abs continuous_const))
  apply (isCompact_closedBall (0 : ℂ) 4).of_isClosed_subset hc
  intro z hz
  have hre : |z.re| ≤ 5 / 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.1⟩
  have hn := Complex.norm_le_abs_re_add_abs_im z
  simpa only [mem_closedBall, dist_zero_right] using
    (show ‖z‖ ≤ 4 by linarith [hz.2.2])

theorem ribbonStepCompact_interior
    {z : ℂ} (hre : -(1 / 2 : ℝ) < z.re ∧ z.re < 5 / 2)
    (him : |z.im| < 1 / 2) : z ∈ interior ribbonStepCompact := by
  let V : Set ℂ := {z | -(1 / 2 : ℝ) < z.re ∧ z.re < 5 / 2 ∧ |z.im| < 1 / 2}
  have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const))
  have hVK : V ⊆ ribbonStepCompact := by
    intro w hw
    exact ⟨hw.1.le, hw.2.1.le, hw.2.2.le⟩
  exact interior_maximal hVK hV ⟨hre.1, hre.2, him⟩

theorem ribbonStepCompact_zero : (0 : ℂ) ∈ ribbonStepCompact := by
  change -(1 / 2 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 5 / 2 ∧ |(0 : ℝ)| ≤ 1 / 2
  norm_num

theorem ribbonStepCompact_core {ε : ℝ} (hε : ε ≤ 1 / 8) :
    {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ ε / 4} ⊆
      interior ribbonStepCompact := by
  intro z hz
  apply ribbonStepCompact_interior
  · constructor <;> linarith [hz.1, hz.2.1]
  · linarith [hz.2.2]

theorem ribbonStepCompact_passage {ε : ℝ} (hε : ε ≤ 1 / 8)
    (C : ℝ≥0) (η : ℝ) :
    ribbonStepCompact ∩ passageCoordinateRegion C ε η ⊆ interior ribbonStepCompact := by
  intro z hz
  apply ribbonStepCompact_interior
  · constructor <;> linarith [hz.2.1, hz.2.2.1]
  · linarith [hz.2.2.2.1]

theorem guidePatch_subset_ribbonStepPatch (k : ℝ) :
    guidePatch k ⊆ ribbonStepPatch k := by
  intro z hz
  exact ⟨by linarith [hz.1], hz.2.1, hz.2.2⟩

theorem crossingPatch_subset_ribbonStepPatch (k : ℝ) :
    crossingPatch k ⊆ ribbonStepPatch k := by
  intro z hz
  exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩

theorem translate_ribbonStepCompact {k : ℝ} {z : ℂ} (hz : z ∈ ribbonStepCompact) :
    (k : ℂ) + z ∈ ribbonStepPatch k := by
  change k - 1 ≤ k + z.re ∧ k + z.re ≤ k + 3 ∧ |0 + z.im| ≤ 1
  exact ⟨by linarith [hz.1], by linarith [hz.2.1], by simpa using hz.2.2.trans (by norm_num)⟩

theorem guideCoordinate_translate (k x t : ℝ) :
    (k : ℂ) + guideCoordinate 0 x t = guideCoordinate k x t := by
  apply Complex.ext <;> simp [guideCoordinate]

end SLEExactGauge.RibbonCoordinates

end

end OAI
