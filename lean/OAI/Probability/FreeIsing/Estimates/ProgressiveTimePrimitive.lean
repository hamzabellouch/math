import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitive

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem isStronglyProgressive_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {a : ℝ≥0 → Ω → ℝ} (ha : IsStronglyProgressive F a) :
    IsStronglyProgressive F (nnrealTimePrimitive a) := by
  intro T
  have hi : StronglyMeasurable[Subtype.instMeasurableSpace.prod (F T)]
      (fun p : Iic T × Ω => ∫ r : ℝ,
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0) := by
    have hc := stronglyMeasurable_clipped_nnreal_process ha T
    let : MeasurableSpace Ω := F T
    have hf : StronglyMeasurable (fun q : (Iic T × Ω) × ℝ =>
        a (min q.2.toNNReal T) q.1.2) :=
      hc.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have hs : MeasurableSet {q : (Iic T × Ω) × ℝ |
        0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd
          (measurable_subtype_coe.comp (measurable_subtype_coe.comp
            (measurable_fst.comp measurable_fst))))
    have hu : StronglyMeasurable (Function.uncurry (fun p : Iic T × Ω => fun r : ℝ =>
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0)) := by
      exact hf.piecewise hs stronglyMeasurable_zero
    exact hu.integral_prod_right
  convert hi using 1
  funext p
  rw [nnrealTimePrimitive, intervalIntegral.integral_of_le (p.1 : ℝ≥0).coe_nonneg,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  by_cases hr : r ∈ Ioc (0 : ℝ) (p.1 : ℝ≥0)
  · have hrt : r.toNNReal ≤ T :=
      (by simpa using Real.toNNReal_mono hr.2 : r.toNNReal ≤ (p.1 : ℝ≥0)).trans p.1.2
    simp only [Set.indicator_of_mem hr, Set.mem_Ioc] at hr ⊢
    rw [ite_eq_left hr, min_eq_left hrt]
  · simp only [Set.indicator_of_notMem hr]
    exact (ite_eq_right hr).symm

end Problem367

end

end OAI
