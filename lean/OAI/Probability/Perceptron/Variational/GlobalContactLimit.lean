import Mathlib
import OAI.Probability.Perceptron.Variational.QuantileLimit
import OAI.Probability.Perceptron.Variational.GlobalContact
import OAI.Probability.Perceptron.Interpolation.FieldArray

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

section

lemma compactPositivePairLaw_field_integral
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n,
      Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hT : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n,
      Matrix.PosSemidef (fun i j : Fin n => (Q i j).2.val))
    (hn : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), 0≤(Q 0 1).1.val)
    {k : ℕ} (a : Fin (k+1)→ℝ) :
    (∫ Q, sourceFieldArrayTest a Q ∂ν)=
      ∫ x : Time×Time, (sourceFieldPolynomial a).eval x.2.val*x.1.val
        ∂compactPositivePairLaw ν := by
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) :=
    compactPositivePair_measurable.comp (by fun_prop)
  rw [compactPositivePairLaw, integral_map hm.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [hR,hT,hn] with Q hr ht hn
  dsimp [sourceFieldArrayTest,compactPositivePair]
  rw [max_eq_right hn, gram_array_symmetric (fun i j => (Q i j).1.val) hr 0 1,
    gram_array_symmetric (fun i j => (Q i j).2.val) ht 0 1]

lemma compactPositivePairLaw_field_quantile
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hq : (volume : Measure Time).map (fun u =>
      (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) u,
       boundedQuantile ((compactPositivePairLaw ν).map Prod.snd) u))=compactPositivePairLaw ν)
    {k : ℕ} (a : Fin (k+1)→ℝ) :
    (∫ x : Time×Time, (sourceFieldPolynomial a).eval x.2.val*x.1.val
      ∂compactPositivePairLaw ν)=
      ∫ u : Time, (sourceFieldPolynomial a).eval
        (boundedQuantile ((compactPositivePairLaw ν).map Prod.snd) u).val *
        (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) u).val := by
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  conv_lhs => rw [← hq]
  rw [integral_map ((boundedQuantile_measurable _).prodMk (boundedQuantile_measurable _)).aemeasurable
    (by fun_prop)]

variable (k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))
variable (hcap : ∀ n, (c n).2.1 (Fin.last k)<H)

include hc hmin hcap in

theorem source_global_contact_limit_field
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun i => p i.val) (fun i => d i.val)
      (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))
    {a : Fin (k+1)→ℝ} (ha0 : ∀ i, 0≤a i) (ha : Monotone a) :
    (∑ i, w i*(q i:ℝ)*a i) ≤ ∫ Q, sourceFieldArrayTest a Q ∂ν := by
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (sourceFieldArrayTest a)).continuousAt.tendsto.comp hlim
  apply ge_of_tendsto ht
  exact Eventually.of_forall fun n => by
    dsimp only [Function.comp_apply]
    rw [sourceGibbsArray_field_integral _ _ _ _ _ _ (hc (s n)).2.1.1.1 (hc (s n)).2.1.2]
    exact source_global_contact_field _ _ _ _ _ _ _ _ hw hw1 _ _ _ (hc (s n)) (hmin (s n))
      (hcap (s n)) ha0 ha

include hc hmin hcap in

theorem source_global_contact_limit_quantile_field
    (hH : 0≤H) (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun i => p i.val) (fun i => d i.val)
      (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))
    {a : Fin (k+1)→ℝ} (ha0 : ∀ i, 0≤a i) (ha : Monotone a) :
    (∑ i, w i*(q i:ℝ)*a i) ≤
      ∫ u : Time, (sourceFieldPolynomial a).eval (boundedQuantile (sourceLabelLaw k w) u).val *
        (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) u).val := by
  have hm n := source_global_contact_perturbation_min n k P f (fun i => p i.val) (fun i => d i.val)
    w q (fun i => (hw i).le) hw1 δ α H (hc n) (hmin n)
  obtain ⟨hn,hl,hq⟩ := source_contact_limit_quantile k f p d w hw hw1
    (fun n => (c n).1) (fun n => (c n).2.1) (fun n => (hc n).2.1.1.1)
    (fun n => (hc n).2.1.2) (fun n => (c n).2.2) (fun n => (hc n).2.2) hm hH
    (fun n => (hc n).2.1.1.2 0) (T := (α:ℝ)) (fun n => (hc n).1.2) hcover hs hlim
  obtain ⟨hr,ht⟩ := sourceGibbsArray_limit_gram k f (fun _ i => p i.val) (fun _ i => d i.val)
    (fun n => (c n).2.1) (fun n => (c n).2.2) (stepCumulative w) (fun n => (c n).1) s hlim
  have he := source_global_contact_limit_field k P f p d w q hw hw1 δ α H c hc hmin hcap hlim ha0 ha
  rw [compactPositivePairLaw_field_integral ν hr ht hn a,
    compactPositivePairLaw_field_quantile ν hq a, hl] at he
  exact he

end

lemma sourceLabelLaw_ae (k : ℕ) (w : Fin (k+1)→ℝ) {P : Time→Prop}
    (hP : ∀ i, P (sourceLabelLevel k i)) : ∀ᵐ x ∂sourceLabelLaw k w, P x := by
  rw [sourceLabelLaw,← Measure.sum_fintype,Measure.ae_sum_iff]
  intro i
  exact Measure.ae_smul_measure (by simpa only [ae_dirac_eq,Filter.eventually_pure] using hP i) _

def sourceThresholdDirection {k : ℕ} (q : Fin (k+1)→Time) (r : ℝ) : Fin (k+1)→ℝ :=
  fun i => if r≤(q i:ℝ) then 1 else 0

lemma sourceThresholdDirection_nonneg {k : ℕ} (q : Fin (k+1)→Time) (r : ℝ) (i : Fin (k+1)) :
    0 ≤ sourceThresholdDirection q r i := by unfold sourceThresholdDirection; split_ifs <;> norm_num

lemma sourceThresholdDirection_le_one {k : ℕ} (q : Fin (k+1)→Time) (r : ℝ) (i : Fin (k+1)) :
    sourceThresholdDirection q r i≤1 := by unfold sourceThresholdDirection; split_ifs <;> norm_num

lemma sourceThresholdDirection_monotone {k : ℕ} {q : Fin (k+1)→Time} (hq : Monotone q) (r : ℝ) :
    Monotone (sourceThresholdDirection q r) := by
  intro i j hij
  unfold sourceThresholdDirection
  split_ifs with hi hj hj <;> try norm_num
  exact False.elim (hj (hi.trans (hq hij)))

lemma sourceThresholdDirection_stoploss {k : ℕ} (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time) (r : ℝ) :
    (∑ i, w i*max ((q i:ℝ)-r) 0)=
      (∑ i, w i*(q i:ℝ)*sourceThresholdDirection q r i)-r*∑ i, w i*sourceThresholdDirection q r i := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [sourceThresholdDirection]
  split_ifs with hi
  · rw [max_eq_left (sub_nonneg.mpr hi)]; ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hi))]; ring

lemma stoploss_integrable (μ : Measure Time) [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x : Time => max (x.val-r) 0) μ :=
  (show Continuous (fun x : Time => max (x.val-r) 0) from by fun_prop).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma source_field_stoploss {k : ℕ} (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hq : Monotone q)
    (μ : Measure (Time×Time)) [IsProbabilityMeasure μ]
    (hlabel : μ.map Prod.snd=sourceLabelLaw k w)
    (hfield : ∀ a : Fin (k+1)→ℝ, (∀ i, 0≤a i) → Monotone a →
      (∑ i, w i*(q i:ℝ)*a i)≤∫ x, (sourceFieldPolynomial a).eval x.2.val*x.1.val ∂μ)
    (r : ℝ) :
    (∑ i, w i*max ((q i:ℝ)-r) 0)≤∫ x : Time, max (x.val-r) 0 ∂μ.map Prod.fst := by
  let a := sourceThresholdDirection q r
  let g : Time×Time→ℝ := fun x => (sourceFieldPolynomial a).eval x.2.val
  have hg : Continuous g := (sourceFieldPolynomial_continuous a).comp continuous_snd
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hprod : Integrable (fun x : Time×Time => g x*x.1.val) μ :=
    (hg.mul (continuous_subtype_val.comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : ∀ᵐ x ∂μ, g x∈Icc 0 1 := by
    have hb' : ∀ᵐ t ∂μ.map Prod.snd, (sourceFieldPolynomial a).eval t.val∈Icc 0 1 := by
      rw [hlabel]
      apply sourceLabelLaw_ae
      intro i
      change (sourceFieldPolynomial a).eval ((i.val:ℝ)/(k+1:ℕ))∈Icc 0 1
      rw [sourceFieldPolynomial_eval]
      exact ⟨sourceThresholdDirection_nonneg q r i,sourceThresholdDirection_le_one q r i⟩
    exact ae_of_ae_map measurable_snd.aemeasurable hb'
  have hint : (∫ x, g x ∂μ)=∑ i, w i*a i := by
    have he := sourceLabelLaw_integral k w hw (fun t => (sourceFieldPolynomial a).eval t.val)
      (sourceFieldPolynomial_continuous a).measurable
    rw [← hlabel,integral_map measurable_snd.aemeasurable
      (sourceFieldPolynomial_continuous a).measurable.aestronglyMeasurable] at he
    simpa only [sourceLabelLevel,sourceFieldPolynomial_eval] using he
  have hm : ∫ x, g x*x.1.val-r*g x ∂μ ≤ ∫ x : Time×Time, max (x.1.val-r) 0 ∂μ := by
    apply integral_mono_ae (hprod.sub (hgi.const_mul r))
      ((show Continuous (fun x : Time×Time => max (x.1.val-r) 0) from by fun_prop).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    filter_upwards [hb] with x hx
    change g x*x.1.val-r*g x ≤ max (x.1.val-r) 0
    by_cases hr : r≤x.1.val
    · rw [max_eq_left (sub_nonneg.mpr hr)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hx.2)]
    · rw [max_eq_right (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hr)) hx.1]
  rw [integral_sub hprod (hgi.const_mul r),integral_const_mul,hint] at hm
  rw [integral_map measurable_fst.aemeasurable (by fun_prop),sourceThresholdDirection_stoploss]
  exact (sub_le_sub_right (hfield a (sourceThresholdDirection_nonneg q r)
    (sourceThresholdDirection_monotone hq r)) _).trans hm

end SphericalPerceptronFreeEnergy
end

end OAI
