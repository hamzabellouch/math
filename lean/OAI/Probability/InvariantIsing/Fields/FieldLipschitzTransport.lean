import OAI.Probability.InvariantIsing.Fields.FieldWasserstein
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! First-moment transport controls Lipschitz integrals and hence weak convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace InvariantIsing

lemma integrable_lipschitz_field {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : Integrable f μ := by
  refine ((hμ.abs.const_mul (K : ℝ)).add (integrable_const |f 0|)).mono'
    hf.continuous.measurable.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  change |f x| ≤ (K : ℝ)* |x|+|f 0|
  have hh := abs_add_le (f x-f 0) (f 0)
  rw [sub_add_cancel] at hh
  have hl := hf.dist_le_mul x 0
  simp only [Real.dist_eq,sub_zero] at hl
  exact hh.trans (add_le_add hl le_rfl)

lemma fieldCoupling_integral_lipschitz {μ ξ : ProbabilityMeasure ℝ} (p : FieldLawCoupling μ ξ)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ)) {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) :
    |(∫ x, f x ∂(μ : Measure ℝ))-(∫ x, f x ∂(ξ : Measure ℝ))| ≤
      (K : ℝ)*(∫ xy, |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ))) := by
  have hif := integrable_lipschitz_field hμ hf
  have hjf := integrable_lipschitz_field hξ hf
  have h1 : (∫ x, f x ∂(μ : Measure ℝ))=∫ xy, f xy.1 ∂(p.law : Measure (ℝ × ℝ)) := by
    rw [← p.fst,integral_map measurable_fst.aemeasurable hf.continuous.measurable.aestronglyMeasurable]
  have h2 : (∫ x, f x ∂(ξ : Measure ℝ))=∫ xy, f xy.2 ∂(p.law : Measure (ℝ × ℝ)) := by
    rw [← p.snd,integral_map measurable_snd.aemeasurable hf.continuous.measurable.aestronglyMeasurable]
  have hi : Integrable (fun xy : ℝ × ℝ => f xy.1) (p.law : Measure (ℝ × ℝ)) := by
    rw [← p.fst] at hif
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable measurable_fst.aemeasurable).mp hif
  have hj : Integrable (fun xy : ℝ × ℝ => f xy.2) (p.law : Measure (ℝ × ℝ)) := by
    rw [← p.snd] at hjf
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable measurable_snd.aemeasurable).mp hjf
  rw [h1,h2,← integral_sub hi hj,← integral_const_mul]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono (hi.sub hj).abs
    (((p.integrable_fst hμ).sub (p.integrable_snd hξ)).abs.const_mul (K : ℝ))
  intro xy
  exact hf.dist_le_mul xy.1 xy.2

lemma integral_tendsto_of_fieldWasserstein
    (μ : ProbabilityMeasure ℝ) (μs : ℕ → ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hμs : ∀ n, Integrable (fun x : ℝ => x) (μs n : Measure ℝ))
    (hw : Tendsto (fun n => fieldWassersteinOne (μs n) μ) atTop (𝓝 0))
    {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure ℝ)) atTop (𝓝 (∫ x, f x ∂(μ : Measure ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε/((K : ℝ)+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : (K : ℝ)*δ<ε := by
    have he : ((K : ℝ)+1)*δ=ε := mul_div_cancel₀ ε (by positivity : (K : ℝ)+1≠0)
    nlinarith
  filter_upwards [hw.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hδ))] with n hn
  obtain ⟨p,hp⟩ := exists_fieldLawCoupling_cost_lt hn
  rw [p.cost_eq_ofReal (hμs n) hμ] at hp
  have hcost := (ENNReal.ofReal_lt_ofReal_iff hδ).mp hp
  rw [Real.dist_eq]
  exact (fieldCoupling_integral_lipschitz p (hμs n) hμ hf).trans_lt
    ((mul_le_mul_of_nonneg_left hcost.le K.coe_nonneg).trans_lt hsmall)

lemma weak_tendsto_of_fieldWasserstein
    (μ : ProbabilityMeasure ℝ) (μs : ℕ → ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hμs : ∀ n, Integrable (fun x : ℝ => x) (μs n : Measure ℝ))
    (hw : Tendsto (fun n => fieldWassersteinOne (μs n) μ) atTop (𝓝 0)) :
    Tendsto μs atTop (𝓝 μ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f _ hl
  obtain ⟨K,hK⟩ := hl
  exact integral_tendsto_of_fieldWasserstein μ μs hμ hμs hw hK

end InvariantIsing

end

end OAI
