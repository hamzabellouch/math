import OAI.Geometry.RCD.Metric.BoundedSupportIntegralRepresentative
import OAI.Geometry.RCD.Coordinates.TimeAverageLinearMap

namespace OAI

/-! # The pointwise values of an actual Sobolev time average -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) [SigmaFinite μ] (Q : QuadraticCheegerEnergy μ)

theorem sobolev_time_average_representative
    (u : ℝ → SobolevSpace μ Q) (hu : Integrable u)
    (f : ℝ → X → ℝ) (hf : StronglyMeasurable (Function.uncurry f))
    {s : Set X} (hs : MeasurableSet s) (hfin : μ s ≠ ∞)
    {h t : ℝ} (hh : 0 < h)
    (hr : ∀ᵐ q ∂volume.restrict (Icc (t-h) (t+h)), SobolevSpace.toLp μ Q (u q) =ᵐ[μ] f q)
    {A : ℝ} (hb : ∀ᵐ q ∂volume.restrict (Icc (t-h) (t+h)), ∀ x, |f q x| ≤ A)
    (hz : ∀ᵐ q ∂volume.restrict (Icc (t-h) (t+h)), ∀ x, x ∉ s → f q x = 0) :
    SobolevSpace.toLp μ Q (timeIntervalAverage u h t) =ᵐ[μ]
      fun x => timeIntervalAverage (fun q => f q x) h t := by
  let T := SobolevSpace.toLpCLM μ Q
  have hi : Integrable (fun q => T (u q)) (volume.restrict (Icc (t-h) (t+h))) :=
    (T.integrable_comp hu).integrableOn
  obtain ⟨-,he⟩ := bounded_support_L2_integral μ (volume.restrict (Icc (t-h) (t+h)))
    hs hfin (fun q => T (u q)) hi f hf hr hb hz
  have ht : t-h ≤ t+h := by linarith
  have hmap : SobolevSpace.toLp μ Q (timeIntervalAverage u h t) =
      (2*h)⁻¹ • ∫ q in Icc (t-h) (t+h), T (u q) := by
    change T (timeIntervalAverage u h t) = _
    rw [timeIntervalAverage_map T u hu,timeIntervalAverage,
      intervalIntegral.integral_of_le ht,← integral_Icc_eq_integral_Ioc]
  rw [hmap]
  filter_upwards [Lp.coeFn_smul ((2*h)⁻¹) (∫ q in Icc (t-h) (t+h), T (u q)),he]
    with x hx hy
  rw [hx,Pi.smul_apply,hy]
  simp only [timeIntervalAverage,intervalIntegral.integral_of_le ht,
    ← integral_Icc_eq_integral_Ioc]

end RegularPointCoordinates

end

end OAI
