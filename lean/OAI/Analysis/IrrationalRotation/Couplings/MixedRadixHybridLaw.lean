import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixCircle
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixTransport
import OAI.Analysis.IrrationalRotation.Analysis.CountableGraphTransfer
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.HybridLaw

theorem tendsto_finiteMeasure_map_of_ae_tendsto
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : FiniteMeasure Ω) {f : ℕ → Ω → X} {g : Ω → X}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ ω ∂(P : Measure Ω),
      Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => P.map (f n)) atTop (𝓝 (P.map g)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  simp only [FiniteMeasure.toMeasure_map]
  simp_rw [integral_map (hf _).aemeasurable φ.continuous.aestronglyMeasurable,
    integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro n
    exact (φ.continuous.measurable.comp (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun ω => φ.norm_coe_le_norm (f n ω)
  · filter_upwards [hlim] with ω hω
    exact (φ.continuous.tendsto (g ω)).comp hω

end Invariant233.HybridLaw

namespace Invariant233.MixedRadix

theorem measurable_hybrid {r : ℕ → ℕ} (N : ℕ) :
    Measurable (fun z : Digits r × Digits r => hybrid z.1 z.2 N) := by
  apply Measurable.of_eval
  intro n
  by_cases hn : n < N
  · simpa only [hybrid, ite_eq_left hn, Function.comp_def] using (measurable_pi_apply n).comp measurable_snd
  · simpa only [hybrid, ite_eq_right hn, Function.comp_def] using (measurable_pi_apply n).comp measurable_fst

theorem tendsto_circleValue_hybrid {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (d e : Digits r) :
    Tendsto (fun N => circleValue (hybrid d e N)) atTop (𝓝 (circleValue e)) := by
  exact (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp
    (tendsto_ofDigits_hybrid hr d e)

theorem tendsto_circle_hybrid_pair_law {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (P : FiniteMeasure (Digits r × Digits r)) :
    Tendsto (fun N => P.map (fun z => (circleValue z.1,
      circleValue (hybrid z.1 z.2 N)))) atTop
      (𝓝 (P.map (fun z => (circleValue z.1, circleValue z.2)))) := by
  apply HybridLaw.tendsto_finiteMeasure_map_of_ae_tendsto
  · intro N
    exact ((measurable_circleValue hr).comp measurable_fst).prodMk
      ((measurable_circleValue hr).comp (measurable_hybrid N))
  · exact ((measurable_circleValue hr).comp measurable_fst).prodMk
      ((measurable_circleValue hr).comp measurable_snd)
  · exact Eventually.of_forall fun z => tendsto_const_nhds.prodMk_nhds
      (tendsto_circleValue_hybrid hr z.1 z.2)

theorem circleValue_hybrid_eq_add_int_div {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d e : Digits r) (N : ℕ) :
    ∃ z : ℤ, circleValue (hybrid d e N) = circleValue d +
      (((z : ℝ) / (denominator r N : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨z, hz⟩ := hybrid_sub_eq_int_div hr d e N
  refine ⟨z, ?_⟩
  have hreal : ofDigits (hybrid d e N) = ofDigits d +
      (z : ℝ) / (denominator r N : ℝ) := by linarith
  simpa only [circleValue, AddCircle.coe_add] using
    congrArg (fun x : ℝ => (x : AddCircle (1 : ℝ))) hreal

theorem ae_circle_hybrid_pair_graph {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (P : Measure (Digits r × Digits r)) (N : ℕ) :
    ∀ᵐ t ∂P.map (fun z => (circleValue z.1, circleValue (hybrid z.1 z.2 N))),
      ∃ z : ℤ, t.2 = t.1 +
        (((z : ℝ) / (denominator r N : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  have hmeas : Measurable (fun z : Digits r × Digits r =>
      (circleValue z.1, circleValue (hybrid z.1 z.2 N))) :=
    ((measurable_circleValue hr).comp measurable_fst).prodMk
      ((measurable_circleValue hr).comp (measurable_hybrid N))
  have hset : MeasurableSet {t : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) |
      ∃ z : ℤ, t.2 = t.1 +
        (((z : ℝ) / (denominator r N : ℝ) : ℝ) : AddCircle (1 : ℝ))} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun z =>
      measurableSet_eq_fun measurable_snd (measurable_fst.add measurable_const)
  apply (ae_map_iff hmeas.aemeasurable hset).mpr
  exact Eventually.of_forall fun t => circleValue_hybrid_eq_add_int_div
    (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)) t.1 t.2 N

theorem ae_relation_circle_hybrid_pair_law {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (P : Measure (Digits r × Digits r)) (μ : Measure (AddCircle (1 : ℝ)))
    (R : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) → Prop) (N : ℕ)
    (hfirst : P.map (fun z => circleValue z.1) ≪ μ)
    (hgraph : ∀ z : ℤ, ∀ᵐ x ∂μ,
      R x (x + (((z : ℝ) / (denominator r N : ℝ) : ℝ) : AddCircle (1 : ℝ)))) :
    ∀ᵐ t ∂P.map (fun z => (circleValue z.1, circleValue (hybrid z.1 z.2 N))),
      R t.1 t.2 := by
  have hmeas : Measurable (fun z : Digits r × Digits r =>
      (circleValue z.1, circleValue (hybrid z.1 z.2 N))) :=
    ((measurable_circleValue hr).comp measurable_fst).prodMk
      ((measurable_circleValue hr).comp (measurable_hybrid N))
  apply Fields.ae_pair_relation_of_countable_graphs R
    (fun (z : ℤ) x => x + (((z : ℝ) / (denominator r N : ℝ) : ℝ) : AddCircle (1 : ℝ)))
  · simpa only [Measure.map_map measurable_fst hmeas, Function.comp_def] using hfirst
  · exact hgraph
  · exact ae_circle_hybrid_pair_graph hr P N

end Invariant233.MixedRadix

end

end OAI
