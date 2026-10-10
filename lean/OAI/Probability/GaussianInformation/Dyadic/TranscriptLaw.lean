import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.RealizationStep

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FiniteChannel
variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

lemma coarsen_density_sum {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (p : FiniteChannel α ι) (g : ι → κ) (x : α) (F : κ → ℝ≥0∞) :
    ∑ j, ENNReal.ofReal ((p.coarsen g).prob j x) * F j =
      ∑ i, ENNReal.ofReal (p.prob i x) * F (g i) := by
  classical
  change (∑ j,ENNReal.ofReal (∑ i,if g i = j then p.prob i x else 0)*F j) = _
  have hs (j : κ) : ENNReal.ofReal (∑ i,if g i = j then p.prob i x else 0) =
      ∑ i,ENNReal.ofReal (if g i = j then p.prob i x else 0) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by split <;> first | exact p.nonneg i x | rfl)
  simp_rw [hs,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [apply_ite ENNReal.ofReal,ENNReal.ofReal_zero,ite_mul,zero_mul]
  simp

lemma law_coarsen (p : FiniteChannel α ι) (g : ι → κ) (μ : Measure α) [IsProbabilityMeasure μ] :
    (p.coarsen g).law μ = (p.law μ).map (Prod.map id g) := by
  classical
  have hg : Measurable (Prod.map (id : α → α) g) := measurable_id.prodMap (measurable_of_countable g)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hg,(p.coarsen g).lintegral_law μ _ hF]
  change (∑ i,∫⁻ x,ENNReal.ofReal ((p.coarsen g).prob i x)*F (x,i) ∂μ) =
    ∫⁻ x,F (x.1,g x.2) ∂p.law μ
  rw [p.lintegral_law μ (fun x => F (x.1,g x.2)) (hF.comp hg)]
  rw [← lintegral_finsetSum Finset.univ (f := fun j x => ENNReal.ofReal ((p.coarsen g).prob j x)*F (x,j))
    (fun j _ => ((p.coarsen g).measurable j).ennreal_ofReal.mul (hF.comp (measurable_id.prodMk measurable_const))),
    ← lintegral_finsetSum Finset.univ (f := fun i x => ENNReal.ofReal (p.prob i x)*F (x,g i))
    (fun i _ => (p.measurable i).ennreal_ofReal.mul (hF.comp (measurable_id.prodMk measurable_const)))]
  apply lintegral_congr
  intro x
  exact p.coarsen_density_sum g x (fun j => F (x,j))

lemma positive_ae_law (p : FiniteChannel α ι) (μ : Measure α) :
    ∀ᵐ x ∂p.law μ, 0 < p.prob x.2 x.1 := by
  rw [law,MeasureTheory.ae_withDensity_iff p.measurable_density]
  exact ae_of_all _ (fun x hx => ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx))

lemma integral_law_snd (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ι → ℝ) : (∫ x,F x.2 ∂p.law μ) = p.expectation μ F := by
  rw [← integral_map measurable_snd.aemeasurable (measurable_of_countable F).aestronglyMeasurable,p.law_snd μ,
    outputLaw,integral_withDensity_eq_integral_toReal_smul (measurable_of_countable _)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),integral_count]
  simp only [ENNReal.toReal_ofReal (scoreMass_nonneg μ _ (p.nonneg _)),smul_eq_mul]
  rfl
end FiniteChannel

lemma Realization.transcript_meas {n N t : ℕ} {s : AnalysisState n} {f : s.Index → History N t}
    (R : Realization s f) : Measurable (transcriptMap R.Q) := by
  apply measurable_fst.prodMk
  apply measurable_snd.prodMk
  apply Measurable.of_eval
  intro i
  exact (R.Qmeas i).comp (measurable_fst.prodMk ((measurable_of_countable (fun w => through w i)).comp measurable_snd))

lemma Realization.augmented_eq {n N t : ℕ} (hn : 0 < n) {s : AnalysisState n}
    {f : s.Index → History N t} (R : Realization s f) (rules : Rules n N t)
    (he : s.channel.coarsen f = historyChannel rules) :
    augmentedLaw rules R.Q = (s.channel.law (cubePrior n)).map (Prod.map id (fun j => (f j,R.trace j))) := by
  have := cubePrior_isProbabilityMeasure hn
  rw [augmentedLaw,experimentLaw_eq_law hn,← he,s.channel.law_coarsen,
    Measure.map_map R.transcript_meas (measurable_id.prodMap (measurable_of_countable f))]
  apply Measure.map_congr
  filter_upwards [s.channel.positive_ae_law (cubePrior n)] with x hx
  have hc := R.chosen x.2 x.1 hx
  change (x.1,(f x.2,fun i => R.Q i x.1 (through (f x.2) i))) = (x.1,(f x.2,R.trace x.2))
  congr 2
  funext i
  exact (R.trace_read x.1 (f x.2) i).symm.trans (by rw [hc])

lemma Realization.information_le {n N t : ℕ} (hn : 0 < n) {s : AnalysisState n}
    {f : s.Index → History N t} (R : Realization s f) (rules : Rules n N t)
    (he : s.channel.coarsen f = historyChannel rules) :
    mutualInformation (augmentedLaw rules R.Q) ≤ ENNReal.ofReal s.information := by
  have := cubePrior_isProbabilityMeasure hn
  rw [R.augmented_eq hn rules he]
  exact (mutualInformation_map_right _ _ (measurable_of_countable _)).trans_eq (s.channel.klDiv_law _)

lemma Realization.level_eq {n N t : ℕ} (hn : 0 < n) {s : AnalysisState n}
    {f : s.Index → History N t} (R : Realization s f) (rules : Rules n N t)
    (he : s.channel.coarsen f = historyChannel rules) :
    (∫ x,(finalLevel R.Q x : ℝ) ∂experimentLaw rules) = s.depth := by
  have := cubePrior_isProbabilityMeasure hn
  have hlev : Measurable (fun x : Coordinate n × History N t => (finalLevel R.Q x : ℝ)) := by
    have hm := ((measurable_of_countable (fun j : s.Index => ((s.cell j).1 : ℝ))).comp R.read_meas)
    have heq : (fun x : Coordinate n × History N t => (finalLevel R.Q x : ℝ)) =
        (fun x => ((s.cell (R.read x.1 x.2)).1 : ℝ)) := by
      funext x
      rw [show x = (x.1,x.2) from rfl,R.depth_read]
    rw [heq]
    exact hm
  rw [experimentLaw_eq_law hn,← he,s.channel.law_coarsen,
    integral_map (measurable_id.prodMap (measurable_of_countable f)).aemeasurable hlev.aestronglyMeasurable]
  have hc : (fun x : Coordinate n × s.Index => (finalLevel R.Q (x.1,f x.2) : ℝ)) =ᵐ[s.channel.law (cubePrior n)]
      (fun x => ((s.cell x.2).1 : ℝ)) := by
    filter_upwards [s.channel.positive_ae_law (cubePrior n)] with x hx
    rw [R.depth_read,R.chosen x.2 x.1 hx]
  change (∫ x : Coordinate n × s.Index,(finalLevel R.Q (x.1,f x.2) : ℝ) ∂s.channel.law (cubePrior n)) = s.depth
  rw [integral_congr_ae hc]
  exact s.channel.integral_law_snd (cubePrior n) (fun j => ((s.cell j).1 : ℝ))
end RepeatedLocalization

end OAI
