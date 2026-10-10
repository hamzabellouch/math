import OAI.InformationTheory.Entanglement.NormalizedProbe
import OAI.InformationTheory.Entanglement.ConditionedLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal
namespace SecretKey
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma condExp_rescale {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) {f : Ω→ℝ} (hf : Integrable f μ)
    (c : ℝ≥0) : μ[f|F]=ᵐ[c•μ] (c•μ)[f|F] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq hF hf.smul_measure_nnreal
  · intro s hs hfin
    exact (integrable_condExp.smul_measure_nnreal (c := c)).integrableOn
  · intro s hs hfin
    rw [Measure.restrict_smul,integral_smul_nnreal_measure,integral_smul_nnreal_measure,
      setIntegral_condExp hF hf hs]
  · exact stronglyMeasurable_condExp.aestronglyMeasurable
lemma condIndep_rescale {μ : Measure Ω} [IsFiniteMeasure μ]
    [StandardBorelSpace Ω] {F A B : MeasurableSpace Ω}
    (hF : F ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hind : CondIndep F A B hF μ) (c : ℝ≥0) : CondIndep F A B hF (c•μ) := by
  rw [condIndep_iff _ _ _ hF hA hB] at hind ⊢
  intro s t hs ht
  have hi (u : Set Ω) (hu : MeasurableSet[mΩ] u) : Integrable (u.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hu
  have hst := condExp_rescale hF (hi (s∩t) ((hA s hs).inter (hB t ht))) c
  have hsa := condExp_rescale hF (hi s (hA s hs)) c
  have htb := condExp_rescale hF (hi t (hB t ht)) c
  filter_upwards [hst,hsa,htb,Measure.ae_smul_measure (hind s t hs ht) c] with x hx hy hz hc
  simp only [Pi.mul_apply] at hc ⊢
  rw [← hx,← hy,← hz]
  exact hc
namespace PositiveMatrixMeasure
open ChannelCompletion Matrix
variable {n : Type} [Fintype n]

lemma scale_traceMeasure (W : PositiveMatrixMeasure Ω n) (c : ℝ≥0) :
    (W.scale (c : ℝ) (NNReal.coe_nonneg c)).traceMeasure=c • W.traceMeasure := by
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (W.scale (c : ℝ) (NNReal.coe_nonneg c)).traceMeasure.real s=(c • W.traceMeasure).real s
  rw [traceMeasure_real _ hs,scale_value,Matrix.trace_smul,
    measureReal_nnreal_smul_apply,traceMeasure_real _ hs]
  simp [smul_eq_mul]
lemma scale_domination (W : PositiveMatrixMeasure Ω n) {μ : Measure Ω}
    (h : W.traceMeasure ≪ μ) (c : ℝ≥0) :
    (W.scale (c : ℝ) (NNReal.coe_nonneg c)).traceMeasure ≪ c • μ := by
  rw [scale_traceMeasure]
  exact h.smul c
lemma scale_born (W : PositiveMatrixMeasure Ω n) (E : Mat n) (s : Set Ω) (c : ℝ≥0) :
    (Matrix.trace (E*(W.scale (c : ℝ) (NNReal.coe_nonneg c)).value s)).re=
      c*(Matrix.trace (E*W.value s)).re := by
  rw [scale_value,Matrix.mul_smul,Matrix.trace_smul]
  simp [smul_eq_mul]
end PositiveMatrixMeasure

end SecretKey

end

end OAI
