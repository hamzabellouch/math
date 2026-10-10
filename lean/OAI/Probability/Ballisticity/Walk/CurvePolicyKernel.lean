import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyPMF
import OAI.Probability.Ballisticity.Estimates.CurvePolicyLateral
import OAI.Probability.Ballisticity.Estimates.BindIntegral

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def curvePolicyKernel {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) (δ α : ℝ≥0∞) (dummy : Lattice d) :
    Kernel (Environment d) (Lattice d) where
  toFun := curvePolicy ℓ f x b B H E δ α dummy
  measurable' := (curvePolicy_rows ℓ f x b B hH E δ α dummy).mono (rowSigma_le _) le_rfl

lemma curvePolicyKernel_markov {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) :
    IsMarkovKernel (curvePolicyKernel ℓ f x b B hH E δ α dummy) :=
  ⟨curvePolicy_probability ℓ f x b B H E hδ hα dummy⟩

lemma curvePolicy_average_toMeasure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) :
    (curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure =
      (environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy) := by
  have := curvePolicy_average_probability ν ℓ f b B hH E hδ hα dummy
  exact Measure.toPMF_toMeasure _

lemma curvePolicy_average_square {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure) =
      ∫ ω, ∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy (realPosition (step e)) f 0 b B H E δ α dummy ω ∂environmentLaw ν := by
  rw [curvePolicy_average_toMeasure]
  exact integral_bind_nonneg_of_integrable _ _
    ((curvePolicy_rows _ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl)
    _ (measurable_of_countable _) (fun u => sq_nonneg _) (curvePolicy_square_integrable e f 0 b hB hH E hδ hα dummy hd)

lemma curvePolicy_square_outer_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (x : Lattice d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    {H : ℕ} (hH : 0 < H) (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    Integrable (fun ω => ∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω)
      (environmentLaw ν) := by
  let Q := curvePolicyKernel (realPosition (step e)) f x b B hH E δ α dummy
  have hm : Measurable (fun ω => ∫ u, (signedCoordinate f u-b H)^2 ∂Q ω) :=
    (measurable_of_countable _).stronglyMeasurable.integral_kernel.measurable
  apply Integrable.of_bound hm.aestronglyMeasurable (B^2)
  apply Eventually.of_forall
  intro ω
  have := curvePolicy_probability (realPosition (step e)) f x b B H E hδ hα dummy ω
  have hi := curvePolicy_square_integrable e f x b hB hH E hδ hα dummy hd ω
  have hh : (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω) ≤ B^2 := by
    have hb : ∀ᵐ u ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω,
        (signedCoordinate f u-b H)^2 ≤ B^2 := by
      filter_upwards [curvePolicy_lateral_bound e f x b hB hH E δ α dummy hd ω] with u hu
      nlinarith [sq_abs (signedCoordinate f u-b H),sq_nonneg (B-|signedCoordinate f u-b H|),abs_nonneg (signedCoordinate f u-b H)]
    simpa using integral_mono_ae hi (integrable_const (B^2)) hb
  have h0 : 0 ≤ ∫ u, (signedCoordinate f u-b H)^2 ∂Q ω := integral_nonneg (fun u => sq_nonneg (signedCoordinate f u-b H))
  rw [Real.norm_eq_abs,abs_of_nonneg h0]
  exact hh

end DirectionalTransience

end

end

end OAI
