import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- The independent triple is always an admissible coupling of a probability. -/
theorem isThreeCoupling_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    IsThreeCoupling mu (mu.prod (mu.prod mu)) := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · change Measure.map Prod.fst (mu.prod (mu.prod mu)) = mu
    simp
  · change Measure.map (Prod.fst ∘ Prod.snd) (mu.prod (mu.prod mu)) = mu
    rw [← Measure.map_map measurable_fst measurable_snd]
    simp
  · change Measure.map (Prod.snd ∘ Prod.snd) (mu.prod (mu.prod mu)) = mu
    rw [← Measure.map_map measurable_snd measurable_snd]
    simp

/-- The Coulomb pair interaction is measurable, including its infinite diagonal. -/
private theorem measurable_pairInteraction :
    Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  fun_prop

theorem map_pair_fst_snd_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    Measure.map (fun t : Triple => (t.1, t.2.1)) (mu.prod (mu.prod mu)) =
      mu.prod mu := by
  change Measure.map (Prod.map id Prod.fst) (mu.prod (mu.prod mu)) = mu.prod mu
  rw [← Measure.map_prod_map mu (mu.prod mu) measurable_id measurable_fst]
  simp

theorem map_pair_fst_thd_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    Measure.map (fun t : Triple => (t.1, t.2.2)) (mu.prod (mu.prod mu)) =
      mu.prod mu := by
  change Measure.map (Prod.map id Prod.snd) (mu.prod (mu.prod mu)) = mu.prod mu
  rw [← Measure.map_prod_map mu (mu.prod mu) measurable_id measurable_snd]
  simp

theorem lintegral_three_pairs_prod (mu : Measure E3) [IsProbabilityMeasure mu]
    (f : E3 × E3 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t : Triple, f (t.1, t.2.1) + f (t.1, t.2.2) + f t.2
      ∂(mu.prod (mu.prod mu))) = 3 * ∫⁻ p, f p ∂(mu.prod mu) := by
  have h12 : (∫⁻ t : Triple, f (t.1, t.2.1) ∂(mu.prod (mu.prod mu))) =
      ∫⁻ p, f p ∂(mu.prod mu) := by
    rw [← lintegral_map (g := fun t : Triple => (t.1, t.2.1)) hf (by fun_prop),
      map_pair_fst_snd_prod]
  have h13 : (∫⁻ t : Triple, f (t.1, t.2.2) ∂(mu.prod (mu.prod mu))) =
      ∫⁻ p, f p ∂(mu.prod mu) := by
    rw [← lintegral_map (g := fun t : Triple => (t.1, t.2.2)) hf (by fun_prop),
      map_pair_fst_thd_prod]
  have h23 : (∫⁻ t : Triple, f t.2 ∂(mu.prod (mu.prod mu))) =
      ∫⁻ p, f p ∂(mu.prod mu) := by
    rw [← lintegral_map hf measurable_snd]
    simp
  rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop), h12, h13, h23]
  ring

/-- The pair interaction energy of an independently sampled pair. -/
def coulombPairEnergy (mu : Measure E3) : ℝ≥0∞ :=
  ∫⁻ p : E3 × E3, invDistance p.1 p.2 ∂(mu.prod mu)

theorem lintegral_coulombCost_prod (mu : Measure E3) [IsProbabilityMeasure mu] :
    (∫⁻ t, coulombCost t ∂(mu.prod (mu.prod mu))) = 3 * coulombPairEnergy mu := by
  exact lintegral_three_pairs_prod mu _ measurable_pairInteraction

theorem kantorovichValue_le_three_pairEnergy (mu : Measure E3)
    [IsProbabilityMeasure mu] :
    kantorovichValue mu ≤ 3 * coulombPairEnergy mu := by
  rw [← lintegral_coulombCost_prod]
  exact iInf_le_of_le (mu.prod (mu.prod mu))
    (iInf_le_of_le (isThreeCoupling_prod mu) le_rfl)

theorem kantorovichValue_lt_top_of_pairEnergy_lt_top (mu : Measure E3)
    [IsProbabilityMeasure mu] (h : coulombPairEnergy mu < ⊤) :
    kantorovichValue mu < ⊤ := by
  apply lt_of_le_of_lt (kantorovichValue_le_three_pairEnergy mu)
  exact ENNReal.mul_lt_top (by norm_num) h

end Problem356

end

end OAI
