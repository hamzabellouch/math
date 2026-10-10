import OAI.Probability.InvariantIsing.Fields.SimpleFieldComparison

namespace OAI

/-! Canonical finite field approximations in first absolute moment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

def fieldSimpleApproximation (n : ℕ) : SimpleFunc ℝ ℝ :=
  SimpleFunc.approxOn id measurable_id (range (id : ℝ → ℝ) ∪ {0}) 0 (by simp) n

lemma fieldSimpleApproximation_tendsto (μ : Measure ℝ)
    (hi : Integrable (fun x : ℝ => x) μ) :
    Tendsto (fun n => ∫ x, |fieldSimpleApproximation n x-x| ∂μ) atTop (𝓝 0) := by
  simpa only [fieldSimpleApproximation,Real.norm_eq_abs,id_eq] using
    tendsto_integral_norm_approxOn_sub measurable_id hi

lemma simpleFieldValue_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ → SimpleFunc Ω ℝ)
    (f : Ω → ℝ) (hf : Integrable f P)
    (hs : Tendsto (fun n => ∫ x, |s n x-f x| ∂P) atTop (𝓝 0))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) :
    CauchySeq (fun n => simpleFieldValue P (s n) (measureR (ν : Measure ℝ) b)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.eventually (Iio_mem_nhds (half_pos hε)))
  refine ⟨N,fun m hm n hn => ?_⟩
  have hm' := hN m hm
  have hn' := hN n hn
  have ht : (∫ x, |s m x-s n x| ∂P) ≤ (∫ x, |s m x-f x| ∂P)+(∫ x, |s n x-f x| ∂P) := by
    have he := integral_add ((simpleField_integrable P (s m)).sub hf).abs
      ((simpleField_integrable P (s n)).sub hf).abs
    dsimp only [Pi.add_apply,Pi.sub_apply] at he
    rw [← he]
    apply integral_mono ((simpleField_integrable P (s m)).sub (simpleField_integrable P (s n))).abs
      (((simpleField_integrable P (s m)).sub hf).abs.add ((simpleField_integrable P (s n)).sub hf).abs)
    intro x
    change |s m x-s n x| ≤ |s m x-f x|+|s n x-f x|
    simpa only [abs_sub_comm (f x) (s n x)] using abs_sub_le (s m x) (f x) (s n x)
  rw [Real.dist_eq]
  exact (simpleFieldValue_abs_sub_le ν a b hcompact hbound ha hb P (s m) (s n)).trans_lt
    (ht.trans_lt (by linarith))

end InvariantIsing

end

end OAI
