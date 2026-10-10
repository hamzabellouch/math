import OAI.NumberTheory.DukePrimeDegree.Geometry.ControlledDistanceCuts
import OAI.NumberTheory.DukePrimeDegree.Entropy.ContractingCutItineraries

namespace OAI

/-! # Finite observations from controlled distance cuts

The observation records the membership bits of the selected distance
balls. Equality of observations gives small relative lifts, while the
dyadic estimates imply almost-sure avoidance of all finite cut boundaries.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

def distanceCutObservation {n N : ℕ} (z : Fin N → X n) (c : Fin N → ℝ)
    (x : X n) (i : Fin N) : Bool := decide (quotientLogDistance (z i) x < c i)

lemma distanceCutObservation_measurable {n N : ℕ}
    (z : Fin N → X n) (c : Fin N → ℝ) : Measurable (distanceCutObservation z c) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_to_bool
  have he : (fun x => distanceCutObservation z c x i) ⁻¹' {true} =
      {x | quotientLogDistance (z i) x < c i} := by
    ext x
    simp [distanceCutObservation]
  rw [he]
  exact measurableSet_lt (continuous_quotientLogDistance n _).measurable measurable_const

lemma distanceCutObservation_small_lifts {n N : ℕ}
    (z : Fin N → X n) (c : Fin N → ℝ) {r : ℝ}
    (hsmall : ∀ i, ∀ x, quotientLogDistance (z i) x < c i →
      ∀ y, quotientLogDistance (z i) y < c i →
      ∃ g ∈ matrixBall n r, rightAction x g=y)
    {x y : X n} (hx : ∃ i, quotientLogDistance (z i) x < c i)
    (hxy : distanceCutObservation z c y=distanceCutObservation z c x) :
    ∃ g ∈ matrixBall n r, rightAction x g=y := by
  obtain ⟨i,hi⟩ := hx
  apply hsmall i x hi y
  have H := congrFun hxy i
  simpa only [distanceCutObservation,hi,decide_true,decide_eq_true_eq] using H

theorem ae_eventually_avoid_finite_dyadic_boundaries
    {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (f : Fin N → Y → ℝ) (hf : ∀ i, Measurable (f i)) (c C : Fin N → ℝ)
    (hbound : ∀ i k, μ (realBoundaryStrip (f i) (c i) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (C i*(1/2:ℝ)^k)) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, ∀ i,
      (1/4:ℝ)^k < |f i (T^[k] x)-c i| := by
  have hall (i : Fin N) : ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop,
      (1/4:ℝ)^k < |f i (T^[k] x)-c i| := by
    apply ae_eventually_avoid_realBoundaryStrip μ hT (hf i)
    have hs := ENNReal.tsum_le_tsum (hbound i)
    exact (lt_of_le_of_lt hs
      (summable_geometric_two.mul_left (C i)).tsum_ofReal_lt_top).ne
  filter_upwards [ae_all_iff.mpr hall] with x hx
  exact Filter.eventually_all.mpr hx

end DukePrimeDegree

end

end OAI
