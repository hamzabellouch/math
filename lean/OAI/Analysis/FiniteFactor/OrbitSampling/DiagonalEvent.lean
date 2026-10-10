import OAI.Analysis.FiniteFactor.OrbitSampling.DiagonalContribution
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Tonelli converts summable expectations of nonnegative functions into
pointwise summability on a conull event. -/
theorem sampling_ae_summable_of_integrals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (f n))
    (hi : ∀ n, Integrable (f n) μ) (hn : ∀ n x, 0 ≤ f n x)
    (hs : Summable (fun n => ∫ x, f n x ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun n => f n x) := by
  have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f n x) ∂μ) = ENNReal.ofReal (∫ x, f n x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (hn n))).symm
  have hfin : (∫⁻ x, ∑' n, ENNReal.ofReal (f n x) ∂μ) ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).ennreal_ofReal.aemeasurable)]
    simp_rw [he]
    exact hs.tsum_ofReal_ne_top
  have hm' : Measurable (fun x => ∑' n, ENNReal.ofReal (f n x)) :=
    Measurable.tsum (fun n => (hm n).ennreal_ofReal)
  filter_upwards [ae_lt_top hm' hfin] with x hx
  exact (ENNReal.summable_toReal hx.ne).congr (fun n => ENNReal.toReal_ofReal (hn n x))

theorem sourceSamplingDiagonalContribution_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Measurable (sourceSamplingDiagonalContribution stage r b E G) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro n _
  exact ((sourceSamplingProduct_measurable stage r b E G hE hG n).pow_const 2).stronglyMeasurable.integral_prod_right.measurable

/-- A genuine conull conclusion for the actual diagonal contribution.
This does not assert convergence of the full empirical sampling error. -/
theorem sourceSamplingDiagonalContribution_ae (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    ∀ᵐ θ ∂sourceAngleLaw,
      Summable (fun stage => sourceSamplingDiagonalContribution stage r b E G θ) ∧
      Tendsto (fun stage => sourceSamplingDiagonalContribution stage r b E G θ) atTop (𝓝 0) := by
  have ha := sampling_ae_summable_of_integrals sourceAngleLaw
    (fun stage θ => sourceSamplingDiagonalContribution stage r b E G θ)
    (fun stage => sourceSamplingDiagonalContribution_measurable stage r b E G hE hG)
    (fun stage => sourceSamplingDiagonalContribution_integrable stage r b E G hE hG)
    (fun stage θ => sourceSamplingDiagonalContribution_nonneg stage r b E G θ)
    (sourceSamplingDiagonalContribution_summable_integral r b E G hE hG)
  exact ha.mono (fun θ hθ => ⟨hθ,hθ.tendsto_atTop_zero⟩)

/-- One conull event handles every member of any countable family of source
tests, orientations and triangular-coordinate choices for the diagonal term. -/
theorem sourceSamplingDiagonalContribution_countable_event {ι : Type*} [Countable ι]
    (r : ι → Bool) (b : ι → SourceCoordinate → Bool) (E G : ι → SourceCoordinate → Set ℝ)
    (hE : ∀ j i, MeasurableSet (E j i)) (hG : ∀ j i, MeasurableSet (G j i)) :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ j,
      Summable (fun stage => sourceSamplingDiagonalContribution stage (r j) (b j) (E j) (G j) θ) ∧
      Tendsto (fun stage => sourceSamplingDiagonalContribution stage (r j) (b j) (E j) (G j) θ) atTop (𝓝 0) :=
  (ae_all_iff).mpr (fun j => sourceSamplingDiagonalContribution_ae (r j) (b j) (E j) (G j) (hE j) (hG j))

end
end FiniteFactor

end OAI
