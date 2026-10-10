import OAI.Geometry.RCD.Sobolev.SobolevAverageRepresentative
import OAI.Geometry.RCD.Coordinates.IntervalVectorExtension
import OAI.Geometry.RCD.Sobolev.RadialLocalSobolev

namespace OAI

/-! # Pointwise identification of the averaged local heat representative -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem radial_time_average_representative
    {a b : ℝ} (v : Ioo a b → SobolevSpace μ Q)
    (hv : AEStronglyMeasurable v (volume.comap Subtype.val))
    {C : ℝ} (hb : ∀ q, ‖v q‖ ≤ C)
    (z : X) {r : ℝ} (hr : 0 < r) (H : ℝ → X → ℝ)
    (hH : Measurable (Function.uncurry H)) (N : Set ℝ) (hN : N.Countable)
    (hrep : ∀ q : Ioo a b, (q:ℝ) ∉ N → SobolevSpace.toLp μ Q (v q) =ᵐ[μ]
      fun x => radialCutoff z r x*H q x)
    {h t M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hsub : Icc (t-h) (t+h) ⊆ Ioo a b)
    (hbound : ∀ q ∈ Icc (t-h) (t+h), ∀ x ∈ closedBall z (2*r), |H q x| ≤ M) :
    SobolevSpace.toLp μ Q (timeIntervalAverage (intervalVectorExtension v) h t) =ᵐ[μ]
      fun x => radialCutoff z r x*timeIntervalAverage (fun q => H q x) h t := by
  let f := fun q x => radialCutoff z r x*H q x
  have hf : StronglyMeasurable (Function.uncurry f) :=
    (((radialCutoff_lipschitz z hr).continuous.measurable.comp measurable_snd).mul hH).stronglyMeasurable
  have hz (q : ℝ) (x : X) (hx : x ∉ closedBall z (2*r)) : f q x = 0 := by
    dsimp only [f]
    rw [radialCutoff_eq_zero z hr (by
      have hxx : 2*r < dist x z := lt_of_not_ge hx
      rw [dist_comm]
      exact hxx.le),zero_mul]
  have hgood : ∀ᵐ q ∂volume.restrict (Icc (t-h) (t+h)),
      q ∈ Icc (t-h) (t+h) ∧ q ∉ N :=
    (ae_restrict_mem measurableSet_Icc).and (ae_restrict_of_ae (hN.ae_notMem volume))
  have hre : ∀ᵐ q ∂volume.restrict (Icc (t-h) (t+h)),
      SobolevSpace.toLp μ Q (intervalVectorExtension v q) =ᵐ[μ] f q := by
    filter_upwards [hgood] with q hq
    have he := intervalVectorExtension_eq v (⟨q,hsub hq.1⟩ : Ioo a b)
    rw [he]
    exact hrep ⟨q,hsub hq.1⟩ hq.2
  have hbf : ∀ᵐ q ∂volume.restrict (Icc (t-h) (t+h)), ∀ x, |f q x| ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    intro x
    by_cases hx : x ∈ closedBall z (2*r)
    · dsimp only [f]
      rw [abs_mul,abs_of_nonneg (radialCutoff_bounds z r x).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (radialCutoff_bounds z r x).2).trans
        (hbound q hq x hx)
    · rw [hz q x hx,abs_zero]
      exact hM
  have he := sobolev_time_average_representative μ Q (intervalVectorExtension v)
    (intervalVectorExtension_integrable v hv hb) f hf measurableSet_closedBall
    (isCompact_closedBall z (2*r)).measure_lt_top.ne hh hre hbf (Eventually.of_forall hz)
  have hscalar (x : X) : timeIntervalAverage (fun q => f q x) h t =
      radialCutoff z r x*timeIntervalAverage (fun q => H q x) h t := by
    simp only [f,timeIntervalAverage,smul_eq_mul,intervalIntegral.integral_const_mul]
    ring
  simpa only [hscalar] using he

end RegularPointCoordinates

end

end OAI
