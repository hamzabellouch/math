import Mathlib
import OAI.Probability.Perceptron.Cascade.WeightedCDF
import OAI.Probability.Perceptron.Variational.FieldRounding
import OAI.Probability.Perceptron.Variational.UniformQuantileCells

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma unit_valued_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {q : Time→Time} (hq : Measurable q) : Integrable (fun u => (q u:ℝ)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (measurable_subtype_coe.comp hq).aestronglyMeasurable
  exact ae_of_all _ fun u => by
    change ‖(q u:ℝ)‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (q u).property.1]
    exact (q u).property.2

lemma quantile_stoploss_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {q : Time→Time} (hq : Measurable q) (r : ℝ) :
    Integrable (fun u => max ((q u:ℝ)-r) 0) μ :=
  ((unit_valued_integrable μ hq).sub (integrable_const r)).sup (integrable_const 0)

lemma time_tail_constant (t : Time) (r : ℝ) :
    (∫ _point : Time in Ici t, r)=(1-(t:ℝ))*r := by
  rw [integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,unitInterval.volume_Ici,smul_eq_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr t.property.2)]

lemma upper_tail_le_stoploss {q : Time→Time} (hq : Measurable q) (t : Time) (r : ℝ) :
    (∫ u : Time in Ici t, (q u:ℝ)) ≤
      (1-(t:ℝ))*r+∫ u : Time, max ((q u:ℝ)-r) 0 := by
  have hi := unit_valued_integrable volume hq
  have hs := quantile_stoploss_integrable volume hq r
  have he : (∫ u : Time, (Ici t).indicator (fun u => (q u:ℝ)-r) u)=
      (∫ u : Time in Ici t, (q u:ℝ))-(1-(t:ℝ))*r := by
    rw [integral_indicator measurableSet_Ici,integral_sub hi.integrableOn (integrable_const r),
      time_tail_constant]
  have hm := integral_mono ((hi.sub (integrable_const r)).indicator measurableSet_Ici) hs
    (show ∀ u : Time, (Ici t).indicator (fun u => (q u:ℝ)-r) u ≤ max ((q u:ℝ)-r) 0 from by
      intro u
      by_cases hu : u∈Ici t
      · rw [indicator_of_mem hu]; exact le_max_left _ _
      · rw [indicator_of_notMem hu]; exact le_max_right _ _)
  change (∫ u : Time, (Ici t).indicator (fun u => (q u:ℝ)-r) u) ≤ _ at hm
  rw [he] at hm
  linarith

lemma upper_tail_eq_stoploss {p : Time→Time} (hp : Monotone p) (t : Time) :
    (∫ u : Time in Ici t, (p u:ℝ))=
      (1-(t:ℝ))*(p t:ℝ)+∫ u : Time, max ((p u:ℝ)-(p t:ℝ)) 0 := by
  have hi := unit_valued_integrable volume hp.measurable
  have he : (fun u : Time => max ((p u:ℝ)-(p t:ℝ)) 0)=
      (Ici t).indicator (fun u => (p u:ℝ)-(p t:ℝ)) := by
    funext u
    by_cases hu : t≤u
    · rw [indicator_of_mem (show u∈Ici t from hu),max_eq_left (sub_nonneg.mpr (show (p t:ℝ)≤(p u:ℝ) from hp hu))]
    · rw [indicator_of_notMem (show u∉Ici t from hu),max_eq_right (sub_nonpos.mpr (show (p u:ℝ)≤(p t:ℝ) from hp (le_of_not_ge hu)))]
  rw [he,integral_indicator measurableSet_Ici,integral_sub hi.integrableOn (integrable_const _),
    time_tail_constant]
  ring

theorem upper_tail_order_of_stoploss {q p : Time→Time} (hq : Measurable q) (hp : Monotone p)
    (hstop : ∀ r : ℝ, (∫ u : Time, max ((q u:ℝ)-r) 0)≤
      ∫ u : Time, max ((p u:ℝ)-r) 0) (t : Time) :
    (∫ u : Time in Ici t, (q u:ℝ))≤∫ u : Time in Ici t, (p u:ℝ) := by
  rw [upper_tail_eq_stoploss hp t]
  exact (upper_tail_le_stoploss hq t (p t:ℝ)).trans (add_le_add le_rfl (hstop (p t:ℝ)))

lemma boundedQuantile_stoploss (μ : Measure Time) [IsProbabilityMeasure μ] (r : ℝ) :
    (∫ u : Time, max ((boundedQuantile μ u:ℝ)-r) 0)=∫ x : Time, max (x.val-r) 0 ∂μ := by
  conv_rhs => rw [← boundedQuantile_law μ]
  rw [integral_map (boundedQuantile_measurable μ).aemeasurable (by fun_prop)]

def uniformQuantileLower (n : ℕ) (q : Time→Time) (i : Fin (n+1)) : Time :=
  q (uniformQuantileGrid n i.castSucc)
def uniformQuantileUpper (n : ℕ) (q : Time→Time) (i : Fin (n+1)) : Time :=
  q (uniformQuantileGrid n i.succ)
def sampleQuantileLower (n : ℕ) (q : Time→Time) (u : Time) : Time :=
  uniformQuantileLower n q (uniformQuantileCell n u)
def sampleQuantileUpper (n : ℕ) (q : Time→Time) (u : Time) : Time :=
  uniformQuantileUpper n q (uniformQuantileCell n u)

lemma uniformQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileLower n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (show i.castSucc ≤ j.castSucc from hij))
lemma uniformQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileUpper n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (Fin.succ_le_succ_iff.mpr hij))
lemma sampleQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileLower n q) :=
  (uniformQuantileLower_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileUpper n q) :=
  (uniformQuantileUpper_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantile_bracket (n : ℕ) {q : Time→Time} (hq : Monotone q) (u : Time) :
    sampleQuantileLower n q u ≤ q u ∧ q u ≤ sampleQuantileUpper n q u :=
  ⟨hq (uniformQuantileCell_bounds n u).1,hq (uniformQuantileCell_bounds n u).2⟩

lemma sampleQuantile_gap_integral (n : ℕ) (q : Time→Time) :
    (∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw)=
      ((q 1:ℝ)-q 0)/(n+1:ℝ) := by
  change (∫ u, (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i)
    (uniformQuantileCell n u) ∂timeLaw)=_
  rw [uniformQuantileCell_integral n (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i),← Finset.mul_sum]
  unfold uniformQuantileUpper uniformQuantileLower
  rw [finite_sum_successive_differences (n+1) (fun i => (q (uniformQuantileGrid n i):ℝ)),
    uniformQuantileGrid_last,uniformQuantileGrid_zero]
  ring

lemma sampleQuantileLower_L1 (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    (∫ u, |(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw) ≤ 1/(n+1:ℝ) := by
  have hl := unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable
  have hu := unit_valued_integrable timeLaw (sampleQuantileUpper_mono n hq).measurable
  have hi := unit_valued_integrable timeLaw hq.measurable
  calc
    _  ≤  ∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw := by
      apply integral_mono (hl.sub hi).abs (hu.sub hl)
      intro u
      have hb := sampleQuantile_bracket n hq u
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonpos (sub_nonpos.mpr (show (sampleQuantileLower n q u:ℝ) ≤ q u from hb.1))]
      have ht : (q u:ℝ) ≤ sampleQuantileUpper n q u := hb.2
      linarith
    _ = ((q 1:ℝ)-q 0)/(n+1:ℝ) := sampleQuantile_gap_integral n q
    _  ≤  1/(n+1:ℝ) := div_le_div_of_nonneg_right (by have := (q 1).2.2; have := (q 0).2.1; linarith) (by positivity)

lemma sampleQuantileUpper_L1 (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    (∫ u, |(sampleQuantileUpper n q u:ℝ)-q u| ∂timeLaw) ≤ 1/(n+1:ℝ) := by
  have hl := unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable
  have hu := unit_valued_integrable timeLaw (sampleQuantileUpper_mono n hq).measurable
  have hi := unit_valued_integrable timeLaw hq.measurable
  calc
    _  ≤  ∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw := by
      apply integral_mono (hu.sub hi).abs (hu.sub hl)
      intro u
      have hb := sampleQuantile_bracket n hq u
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (show (q u:ℝ) ≤ sampleQuantileUpper n q u from hb.2))]
      exact sub_le_sub_left (show (sampleQuantileLower n q u:ℝ) ≤ q u from hb.1) _
    _ = ((q 1:ℝ)-q 0)/(n+1:ℝ) := sampleQuantile_gap_integral n q
    _  ≤  1/(n+1:ℝ) := div_le_div_of_nonneg_right (by have := (q 1).2.2; have := (q 0).2.1; linarith) (by positivity)

lemma uniformQuantileWeights_nonneg (n : ℕ) : ∀ _i : Fin (n+1), (0:ℝ) ≤ 1/(n+1:ℝ) := by
  intro i
  positivity
lemma uniformQuantileWeights_sum (n : ℕ) : (∑ _i : Fin (n+1), (1/(n+1:ℝ)))=1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  field_simp

lemma sampleQuantile_trial (n : ℕ) (q : Fin (n+1)→Time) :
    quantileTrial (fun u => q (uniformQuantileCell n u))=
      weightedStepTrial (fun _ => 1/(n+1:ℝ)) q (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n) := by
  apply Trial.ext_fun
  intro t
  have hm : Measurable (fun u => q (uniformQuantileCell n u)) :=
    (measurable_of_finite q).comp (uniformQuantileCell_measurable n)
  rw [quantileTrial_eq_integral _ hm]
  rw [uniformQuantileCell_integral n (fun i => if q i ≤ t then (1:ℝ) else 0)]
  change (∑ i, (1/(n+1:ℝ))*(if q i ≤ t then (1:ℝ) else 0))=∑ i, if q i ≤ t then 1/(n+1:ℝ) else 0
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end SphericalPerceptronFreeEnergy
end

end OAI
