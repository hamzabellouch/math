import Mathlib
import OAI.Probability.SKGap.Localization.CoordinateDeriv

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKGap
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gaussianFinite_IBP_error (i : κ)
    {f d : (κ → ℝ) → ℝ} {L : ℝ≥0} {C D : ℝ} {s : Set (κ → ℝ)}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C)
    (hd : Measurable d) (hD : ∀ x, ‖d x‖ ≤ D) (hs : MeasurableSet s)
    (hder : ∀ x ∈ s, HasDerivAt (fun z => f (Function.update x i z)) (d x) (x i)) :
    |(∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1))-
      ∫ x, d x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)| ≤
      ((L:ℝ)+D)*(Measure.pi (fun _ : κ => gaussianReal 0 1)).real sᶜ := by
  let μ := Measure.pi (fun _ : κ => gaussianReal 0 1)
  have hi : Integrable (finiteCoordinateDeriv i f) μ :=
    Integrable.of_bound (measurable_finiteCoordinateDeriv i hf.continuous).aestronglyMeasurable
      (L:ℝ) (ae_of_all _ (norm_finiteCoordinateDeriv_le i hf))
  have hid : Integrable d μ := Integrable.of_bound hd.aestronglyMeasurable D (ae_of_all _ hD)
  rw [gaussianFinite_lipschitz_IBP i hf hC,← integral_sub hi hid]
  have he : (fun x => finiteCoordinateDeriv i f x-d x) =
      sᶜ.indicator (fun x => finiteCoordinateDeriv i f x-d x) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_notMem (show x ∉ sᶜ by simpa using hx),finiteCoordinateDeriv]
      rw [(hder x hx).deriv,sub_self]
    · rw [Set.indicator_of_mem hx]
  rw [he,integral_indicator hs.compl]
  exact norm_setIntegral_le_of_norm_le_const (measure_lt_top μ sᶜ) (fun x _ =>
    (norm_sub_le _ _).trans (add_le_add (norm_finiteCoordinateDeriv_le i hf x) (hD x)))

end SKGap

end

end OAI
