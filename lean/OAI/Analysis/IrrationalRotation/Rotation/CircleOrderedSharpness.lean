import OAI.Analysis.IrrationalRotation.Rotation.CircleOrderedHaarRigidity
import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphTrimming

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.CircleOrderedRigidity

def rationalPeriodGraph (p : CircleParameterData) : Measure (Circle × Circle) :=
  circleMeasure.map (fun x : Circle =>
    (x, x + (((1 : ℝ) / p.q 1 : ℝ) : Circle)))

theorem measurable_rationalPeriodPair (p : CircleParameterData) :
    Measurable (fun x : Circle =>
      (x, x + (((1 : ℝ) / p.q 1 : ℝ) : Circle))) := by
  fun_prop

theorem rationalPeriodGraph_fst (p : CircleParameterData) :
    (rationalPeriodGraph p).map Prod.fst = circleMeasure := by
  rw [rationalPeriodGraph, Measure.map_map measurable_fst
    (measurable_rationalPeriodPair p)]
  exact Measure.map_id

theorem rationalPeriodGraph_snd (p : CircleParameterData) :
    (rationalPeriodGraph p).map Prod.snd = circleMeasure := by
  rw [rationalPeriodGraph, Measure.map_map measurable_snd
    (measurable_rationalPeriodPair p)]
  unfold circleMeasure
  exact map_add_right_eq_self volume _

theorem rationalPeriodGraph_probability (p : CircleParameterData) :
    IsProbabilityMeasure (rationalPeriodGraph p) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_rationalPeriodPair p).aemeasurable).2 circleMeasure_probability

theorem first_frequency_gt_one {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) : 1 < p.q 1 := by
  simpa only [hp.frequency_zero] using hp.frequency_increasing (by omega : 0 < 1)

theorem rationalPeriod_ne_zero {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) :
    (((1 : ℝ) / p.q 1 : ℝ) : Circle) ≠ 0 := by
  have hq : (1 : ℝ) < p.q 1 := by exact_mod_cast first_frequency_gt_one hp
  have ht : (1 : ℝ) / p.q 1 ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).2 hq
  intro he
  have hz := (AddCircle.coe_eq_zero_iff_of_mem_Ico ht).1 he
  have hpos : (0 : ℝ) < 1 / p.q 1 := by positivity
  exact hpos.ne' hz

theorem rationalPeriodGraph_ae_coordinate_eq {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) :
    ∀ᵐ xy ∂rationalPeriodGraph p, ∀ i : ℕ, 1 ≤ i →
      p.coordinate i xy.1 = p.coordinate i xy.2 := by
  apply ae_all_iff.2
  intro i
  by_cases hi : 1 ≤ i
  · have hmeas : MeasurableSet {xy : Circle × Circle |
        p.coordinate i xy.1 = p.coordinate i xy.2} :=
      measurableSet_eq_fun ((p.measurable_coordinate i).comp measurable_fst)
        ((p.measurable_coordinate i).comp measurable_snd)
    have he : ∀ᵐ xy ∂rationalPeriodGraph p,
        p.coordinate i xy.1 = p.coordinate i xy.2 := by
      apply (ae_map_iff (measurable_rationalPeriodPair p).aemeasurable hmeas).2
      exact Filter.Eventually.of_forall fun x => by
        simpa using (hp.coordinate_rational_translation hi (1 : ℤ) x).symm
    exact he.mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => (hi h).elim

theorem rationalPeriodGraph_ae_ne {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) :
    ∀ᵐ xy ∂rationalPeriodGraph p, xy.1 ≠ xy.2 := by
  apply (ae_map_iff (measurable_rationalPeriodPair p).aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
  exact Filter.Eventually.of_forall fun x h => by
    have he : (((1 : ℝ) / p.q 1 : ℝ) : Circle) = 0 := by
      exact (add_left_cancel (show x + (((1 : ℝ) / p.q 1 : ℝ) : Circle) = x + 0 by
        simpa using h.symm))
    exact rationalPeriod_ne_zero hp he

theorem exists_ordered_haar_law_off_diagonal {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) :
    ∃ η : Measure (Circle × Circle), IsProbabilityMeasure η ∧
      η.map Prod.fst = circleMeasure ∧ η.map Prod.snd = circleMeasure ∧
      (∀ᵐ xy ∂η, ∀ i : ℕ, 1 ≤ i →
        p.coordinate i xy.1 ≤ p.coordinate i xy.2) ∧
      (∀ᵐ xy ∂η, xy.1 ≠ xy.2) := by
  refine ⟨rationalPeriodGraph p, rationalPeriodGraph_probability p,
    rationalPeriodGraph_fst p, rationalPeriodGraph_snd p, ?_,
    rationalPeriodGraph_ae_ne hp⟩
  exact (rationalPeriodGraph_ae_coordinate_eq hp).mono fun _ h i hi => (h i hi).le

end Invariant233.CircleOrderedRigidity

end

end OAI
