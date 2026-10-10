import OAI.Analysis.FiniteFactor.OrbitSampling.CutoffMass

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal Topology
noncomputable section

/-- The actual triangular phase weight is precisely the order indicator
of the rotated endpoint, on the Haar representatives. -/
theorem samplingWeight_triangular_order (h α s t : ℝ)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingWeight true h α s t = if s < Int.fract (s+t) then 1 else 0 := by
  by_cases hst : s+t < 1
  · have hf : Int.fract (s+t) = s+t := Int.fract_eq_self.mpr ⟨by linarith [hs.1,ht.1],hst⟩
    simp only [samplingWeight,ite_true,hf]
    have he : (0 < t ∧ t < 1-s) ↔ s < s+t := by
      constructor
      · intro h; linarith [h.1]
      · intro h; constructor <;> linarith
    simp only [he]
  · have hf : ⌊s+t⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith [hs.2,ht.2]⟩
    have hn : ¬ (0 < t ∧ t < 1-s) := by intro h; linarith [h.2]
    have ho : ¬ s < Int.fract (s+t) := by rw [Int.fract,hf]; norm_num; linarith [ht.2]
    simp only [samplingWeight,ite_true,ite_eq_right hn,ite_eq_right ho]

/-- The first tested triangular density is its actual vertical section of
Lebesgue measure on 0≤x<y<1. No triangular marginal identity is assumed. -/
theorem samplingTestedFirstDensity_triangular_section (h α s : ℝ) (E G : Set ℝ)
    (hG : MeasurableSet G) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstDensity true h α E G s =
      ∫ y, (if s ∈ E ∧ y ∈ G ∧ s < y then (1 : ℝ) else 0) ∂unitIntervalMeasure := by
  let F := fun y : ℝ => if s ∈ E ∧ y ∈ G ∧ s < y then (1 : ℝ) else 0
  have hm : Measurable F := by
    apply Measurable.ite _ measurable_const measurable_const
    by_cases htest : s ∈ E
    · simp only [htest,true_and]
      change MeasurableSet (G ∩ {y : ℝ | s < y})
      exact hG.inter (measurableSet_lt measurable_const measurable_id)
    · simp [htest]
  have hp : MeasurePreserving (fun t : ℝ => Int.fract (s+t)) unitIntervalMeasure unitIntervalMeasure := by
    simpa only [add_comm] using unitInterval_rotate_preserving s
  have he : samplingTestedFirstWeight true h α E G s =ᵐ[unitIntervalMeasure]
      (fun t => F (Int.fract (s+t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rw [samplingTestedFirstWeight,samplingWeight_triangular_order h α s t hs ht]
    simp only [F]
    split_ifs <;> simp_all
  rw [samplingTestedFirstDensity,integral_congr_ae he]
  rw [← integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]

/-- The two-dimensional tested source integral equals the genuine triangular
restriction of product Lebesgue measure. -/
theorem samplingTestedFirstDensity_triangular_mass (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingTestedFirstDensity true h α E G s ∂unitIntervalMeasure) =
      ((unitIntervalMeasure.prod unitIntervalMeasure)
        {p : ℝ × ℝ | p.1 ∈ E ∧ p.2 ∈ G ∧ p.1 < p.2}).toReal := by
  let A := {p : ℝ × ℝ | p.1 ∈ E ∧ p.2 ∈ G ∧ p.1 < p.2}
  have hA : MeasurableSet A := (hE.preimage measurable_fst).inter
    ((hG.preimage measurable_snd).inter (measurableSet_lt measurable_fst measurable_snd))
  have hm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (integrable_const (1 : ℝ)).indicator hA
  calc
    _ = ∫ s, ∫ y, A.indicator (fun _ => (1 : ℝ)) (s,y) ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
      simpa only [A,Set.indicator_apply,Set.mem_ofPred_eq] using
        samplingTestedFirstDensity_triangular_section h α s E G hG hs
    _ = ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂unitIntervalMeasure.prod unitIntervalMeasure :=
      (integral_prod _ hi).symm
    _ = _ := by rw [integral_indicator hA]; simp [measureReal_def,A]

end
end FiniteFactor

end OAI
