import OAI.Analysis.IrrationalRotation.Model.CircleTruncationEvent
import OAI.Analysis.IrrationalRotation.Rotation.CircleCurrentBlockEvent
import OAI.Analysis.IrrationalRotation.Rotation.CircleFutureEndpointLoss
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitMarginalLaws
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitEndpointLoss

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Invariant233.CircleCoupling

def centralBadEvent (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) : Set Sample :=
  {ω | r (point p hr false ω) < 1 / (j : ℝ)} ∪
    {ω | 1 - r (point p hr true ω) < 1 / (j : ℝ)}

lemma truncationEvent_eq_current_sdiff (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    truncationEvent p j hr r = rawCurrentBlockEvent p j \
      (futureBadEvent p j ∪ centralBadEvent p j hr r) := by
  ext ω
  simp only [truncationEvent, rawCurrentBlockEvent, centralBadEvent, tagEvent,
    Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, not_or, not_lt,
    not_mem_futureBadEvent_iff]
  tauto

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem truncationEvent_mass_lower_sub_losses (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    Real.exp (-90) - (law p j).real (futureBadEvent p j) -
      (law p j).real (centralBadEvent p j hr r) ≤
        (law p j).real (truncationEvent p j hr r) := by
  let := law_isProbabilityMeasure hp j
  rw [truncationEvent_eq_current_sdiff]
  have hcurrent := rawCurrentBlockEvent_mass_lower hp j hj
  have hunion := measureReal_union_le (μ := law p j)
    (futureBadEvent p j) (centralBadEvent p j hr r)
  have hdiff := le_measureReal_sdiff (μ := law p j)
    (s₁ := rawCurrentBlockEvent p j)
    (s₂ := futureBadEvent p j ∪ centralBadEvent p j hr r)
  linarith

theorem tendsto_centralBadEvent_mass
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ}
    (hrm : Measurable r) (hri : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    Tendsto (fun j : ℕ => (law p j).real (centralBadEvent p j hr r))
      atTop (𝓝 0) :=
  (digitMarginalLaws hp hr).tendsto_endpoint_bad_union_zero hp hrm hri

theorem eventually_truncationEvent_mass
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ}
    (hrm : Measurable r) (hri : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    ∀ᶠ j : ℕ in atTop,
      Real.exp (-90) / 2 ≤ (law p j).real (truncationEvent p j hr r) := by
  have hfuture : Tendsto (fun j : ℕ => (law p j).real (futureBadEvent p j))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp (tendsto_futureBadEvent_mass hp)
  have hloss : Tendsto (fun j : ℕ => (law p j).real (futureBadEvent p j) +
      (law p j).real (centralBadEvent p j hr r)) atTop (𝓝 0) := by
    simpa only [zero_add] using hfuture.add (tendsto_centralBadEvent_mass hp hr hrm hri)
  have hsmall := hloss.eventually_lt_const
    (show (0 : ℝ) < Real.exp (-90) / 2 by positivity)
  filter_upwards [hsmall, eventually_ge_atTop 1] with j hj hjpos
  have hbound := truncationEvent_mass_lower_sub_losses hp j hjpos hr r
  linarith

theorem exists_truncationEvent_mass_threshold
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ}
    (hrm : Measurable r) (hri : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
      Real.exp (-90) / 2 ≤ (law p j).real (truncationEvent p j hr r) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (eventually_truncationEvent_mass hp hr hrm hri)
  exact ⟨max J 1, le_max_right _ _, fun j hj => hJ j ((le_max_left _ _).trans hj)⟩

end Invariant233.CircleCoupling

end

end OAI
