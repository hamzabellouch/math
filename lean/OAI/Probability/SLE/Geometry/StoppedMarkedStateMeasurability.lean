import OAI.Probability.SLE.ChartMeasurability
import OAI.Probability.SLE.Geometry.NormalizedMarkedState

namespace OAI

/-! Actual finite-stop marked states are measurable in the stopped past.
The scale is positive on every outcome and agrees with the true centered
modulus on the live event. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def positiveMarkedScale (q : ℂ) : ℝ≥0 := if 0 < ‖q‖ then ‖q‖₊ else 1

lemma positiveMarkedScale_pos (q : ℂ) : 0 < positiveMarkedScale q := by
  unfold positiveMarkedScale
  split_ifs with hq
  · exact_mod_cast hq
  · exact zero_lt_one

lemma positiveMarkedScale_eq {q : ℂ} (hq : q ≠ 0) : positiveMarkedScale q = ‖q‖₊ := by
  exact ite_eq_left (norm_pos_iff.mpr hq)

lemma positiveMarkedScale_measurable : Measurable positiveMarkedScale :=
  Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    measurable_nnnorm measurable_const

lemma unitMarkedState_measurable : Measurable unitMarkedState := by
  unfold unitMarkedState
  fun_prop

def stoppedMarkedCenter {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (τ : Ω → ℝ≥0)
    (z : ℂ) (ω : Ω) : ℂ :=
  (if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0) -
    (Real.sqrt κ * B (τ ω) ω : ℝ)

def stoppedMarkedScale {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (τ : Ω → ℝ≥0)
    (z : ℂ) (ω : Ω) : ℝ≥0 := positiveMarkedScale (stoppedMarkedCenter κ B γ G τ z ω)

def stoppedMarkedUnit {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (τ : Ω → ℝ≥0)
    (z : ℂ) (ω : Ω) : ℂ := unitMarkedState (stoppedMarkedCenter κ B γ G τ z ω)

def stoppedMarkedGood {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (τ : Ω → ℝ≥0)
    (z : ℂ) (s : ℝ) : Set Ω :=
  {ω | z ∈ survivingDomain (γ ω) (τ ω) ∧ s ≤ (stoppedMarkedUnit κ B γ G τ z ω).im}

lemma stoppedMarkedScale_pos {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (τ : Ω → ℝ≥0)
    (z : ℂ) (ω : Ω) : 0 < stoppedMarkedScale κ B γ G τ z ω :=
  positiveMarkedScale_pos _

lemma stoppedMarkedCenter_eq {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (τ : Ω → ℝ≥0)
    (z : ℂ) (ω : Ω) (hz : z ∈ survivingDomain (γ ω) (τ ω)) :
    stoppedMarkedCenter κ B γ G τ z ω = G ω (τ ω) z - (Real.sqrt κ * B (τ ω) ω : ℝ) := by
  rw [stoppedMarkedCenter, ite_eq_left hz]

section Source
variable {Ω : Type*} [MeasurableSpace Ω]
  (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
  (hc : ∀ ω, Continuous (fun t => B t ω))
  (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
  (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0)))

include hc in
lemma source_stoppedDriver_measurable :
    Measurable[hτ.measurableSpace] (fun ω => Real.sqrt κ * B (τ ω) ω) := by
  have hb := measurable_stoppedValue
    ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hc) hτ
  exact measurable_const.mul hb

include hc hw in
lemma source_stoppedMarkedCenter_measurable (z : ℂ) :
    Measurable[hτ.measurableSpace] (stoppedMarkedCenter κ B γ G τ z) := by
  exact (source_killedChart_stopped_measurable hm hc κ γ G F hw z τ hτ).sub
    (Complex.measurable_ofReal.comp (source_stoppedDriver_measurable B hm hc κ τ hτ))

include hc hw in
lemma source_stoppedMarkedScale_measurable (z : ℂ) :
    Measurable[hτ.measurableSpace] (stoppedMarkedScale κ B γ G τ z) :=
  positiveMarkedScale_measurable.comp
    (source_stoppedMarkedCenter_measurable B hm hc κ γ G F hw τ hτ z)

include hc hw in
lemma source_stoppedMarkedUnit_measurable (z : ℂ) :
    Measurable[hτ.measurableSpace] (stoppedMarkedUnit κ B γ G τ z) :=
  unitMarkedState_measurable.comp
    (source_stoppedMarkedCenter_measurable B hm hc κ γ G F hw τ hτ z)

omit [MeasurableSpace Ω] in
include hw in
lemma source_stopped_live_iff_killedChart_im_pos (z : ℂ) (ω : Ω) :
    z ∈ survivingDomain (γ ω) (τ ω) ↔
      0 < (if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0).im := by
  by_cases hz : z ∈ survivingDomain (γ ω) (τ ω)
  · simp only [ite_eq_left hz]
    exact iff_of_true hz ((hw ω).imag_positive (τ ω) z hz)
  · simp only [ite_eq_right hz, Complex.zero_im, lt_self_iff_false, iff_false]
    exact hz

include hc hw in
lemma source_stopped_live_measurable (z : ℂ) :
    MeasurableSet[hτ.measurableSpace] {ω | z ∈ survivingDomain (γ ω) (τ ω)} := by
  have he : {ω | z ∈ survivingDomain (γ ω) (τ ω)} =
      {ω | 0 < (if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0).im} := by
    ext ω
    exact source_stopped_live_iff_killedChart_im_pos B κ γ G F hw τ z ω
  rw [he]
  exact measurableSet_lt measurable_const (Complex.measurable_im.comp
    (source_killedChart_stopped_measurable hm hc κ γ G F hw z τ hτ))

include hc hw in
lemma source_stoppedMarkedGood_measurable (z : ℂ) (s : ℝ) :
    MeasurableSet[hτ.measurableSpace] (stoppedMarkedGood κ B γ G τ z s) :=
  (source_stopped_live_measurable B hm hc κ γ G F hw τ hτ z).inter
    (measurableSet_le measurable_const (Complex.measurable_im.comp
      (source_stoppedMarkedUnit_measurable B hm hc κ γ G F hw τ hτ z)))

omit [MeasurableSpace Ω] in
include hw in
lemma stoppedMarkedScale_eq_on_live (z : ℂ) (ω : Ω)
    (hz : z ∈ survivingDomain (γ ω) (τ ω)) :
    stoppedMarkedScale κ B γ G τ z ω =
      ‖G ω (τ ω) z - (Real.sqrt κ * B (τ ω) ω : ℝ)‖₊ := by
  unfold stoppedMarkedScale
  rw [stoppedMarkedCenter_eq κ B γ G τ z ω hz]
  exact positiveMarkedScale_eq ((hw ω).centered_ne_zero _ z hz)

omit [MeasurableSpace Ω] in
lemma stoppedMarkedUnit_im_on_live (z : ℂ) (ω : Ω)
    (hz : z ∈ survivingDomain (γ ω) (τ ω)) :
    (stoppedMarkedUnit κ B γ G τ z ω).im =
      Real.sin (Complex.arg (G ω (τ ω) z - (Real.sqrt κ * B (τ ω) ω : ℝ))) := by
  unfold stoppedMarkedUnit
  rw [stoppedMarkedCenter_eq κ B γ G τ z ω hz, unitMarkedState_im]

omit [MeasurableSpace Ω] in
include hc hw in
/-- Exact geometric data required by the conformal dense estimate. -/
theorem source_stoppedMarkedState_geometry (z : ℂ) (ω : Ω)
    (hz : z ∈ survivingDomain (γ ω) (τ ω)) :
    let w := stoppedMarkedUnit κ B γ G τ z ω
    let f := normalizedInverse (F ω (τ ω)) (Real.sqrt κ * B (τ ω) ω)
      (stoppedMarkedScale κ B γ G τ z ω : ℝ)
    ‖w‖ = 1 ∧ 0 < w.im ∧ f w = z ∧
      DifferentiableOn ℂ f upperHalfPlane ∧ InjOn f upperHalfPlane ∧
      deriv f w ≠ 0 ∧ 2 * w.im * ‖deriv f w‖ = fullRadius (G ω) (τ ω) z := by
  dsimp only
  rw [stoppedMarkedScale_eq_on_live B κ γ G F hw τ z ω hz]
  simp only [coe_nnnorm]
  unfold stoppedMarkedUnit
  rw [stoppedMarkedCenter_eq κ B γ G τ z ω hz]
  exact (hw ω).normalized_marked_state ((hc ω).const_mul _) (τ ω) z hz

end Source
end SLEExactGauge

end

end OAI
