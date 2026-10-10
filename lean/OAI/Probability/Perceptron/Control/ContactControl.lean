import Mathlib
import OAI.Probability.Perceptron.Control.QuantileControlTail
import OAI.Probability.Perceptron.Variational.ContactTail

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

section

variable (k : ℕ) (P : Measure BrownianPath) (g : Jet3) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
variable (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P g.f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))
variable (hcap : ∀ n, (c n).2.1 (Fin.last k)<H)
variable (hH : 0≤H) (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
variable {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
variable (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k g.f (fun i => p i.val) (fun i => d i.val)
  (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))

include hc hmin hcap hH hcover hs hlim hq in
 theorem source_global_contact_control_order [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) ≤
      controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1) := by
  obtain ⟨he,ht⟩ := source_global_contact_limit_tail_order k P g.f p d w q hw hw1 hq δ α H c
    hc hmin hcap hH hcover hs hlim
  have := weightedTrialLaw_probability w q (fun i => (hw i).le) hw1
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    inferInstance
  rw [← he]
  apply sourceQuantile_control_tail_order P hB g _ _ (boundedQuantile_monotone _)
    (boundedQuantile_monotone _)
  simpa only [timeLaw_eq_volume] using ht

end

section Contact
variable (k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
variable (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))

include hc hmin in

theorem source_global_contact_limit_field_along
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun i => p i.val) (fun i => d i.val)
      (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))
    (hcap : ∀ᶠ n in atTop, (c (s n)).2.1 (Fin.last k)<H)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ i, 0≤a i) (ha : Monotone a) :
    (∑ i, w i*(q i:ℝ)*a i) ≤ ∫ Q, sourceFieldArrayTest a Q ∂ν := by
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (sourceFieldArrayTest a)).continuousAt.tendsto.comp hlim
  apply ge_of_tendsto ht
  filter_upwards [hcap] with n hn
  dsimp only [Function.comp_apply]
  rw [sourceGibbsArray_field_integral _ _ _ _ _ _ (hc (s n)).2.1.1.1 (hc (s n)).2.1.2]
  exact source_global_contact_field _ _ _ _ _ _ _ _ hw hw1 _ _ _ (hc (s n)) (hmin (s n))
    hn ha0 ha

variable (hH : 0≤H) (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
variable {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
variable (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun i => p i.val) (fun i => d i.val)
  (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))

variable (hcap : ∀ᶠ n in atTop, (c (s n)).2.1 (Fin.last k)<H)

include hc hmin hcap hH hcover hs hlim hq in
lemma source_global_contact_limit_stoploss_along (r : ℝ) :
    (∑ i, w i*max ((q i:ℝ)-r) 0)≤
      ∫ x : Time, max (x.val-r) 0 ∂(compactPositivePairLaw ν).map Prod.fst := by
  have hm n := source_global_contact_perturbation_min n k P f (fun i => p i.val) (fun i => d i.val)
    w q (fun i => (hw i).le) hw1 δ α H (hc n) (hmin n)
  obtain ⟨hn,hl,-⟩ := source_contact_limit_quantile k f p d w hw hw1
    (fun n => (c n).1) (fun n => (c n).2.1) (fun n => (hc n).2.1.1.1)
    (fun n => (hc n).2.1.2) (fun n => (c n).2.2) (fun n => (hc n).2.2) hm hH
    (fun n => (hc n).2.1.1.2 0) (T := (α:ℝ)) (fun n => (hc n).1.2) hcover hs hlim
  obtain ⟨hr,ht⟩ := sourceGibbsArray_limit_gram k f (fun _ i => p i.val) (fun _ i => d i.val)
    (fun n => (c n).2.1) (fun n => (c n).2.2) (stepCumulative w) (fun n => (c n).1) s hlim
  apply source_field_stoploss w q (fun i => (hw i).le) hq (compactPositivePairLaw ν) hl
  intro a ha0 ha
  rw [← compactPositivePairLaw_field_integral ν hr ht hn a]
  exact source_global_contact_limit_field_along k P f p d w q hw hw1 δ α H c hc hmin hlim hcap ha0 ha

include hc hmin hcap hH hcover hs hlim hq in

theorem source_global_contact_limit_tail_order_along :
    quantileTrial (boundedQuantile (weightedTrialLaw w q))=
      weightedStepTrial w q (fun i => (hw i).le) hw1 ∧
    ∀ t : Time, (∫ u : Time in Ici t, (boundedQuantile (weightedTrialLaw w q) u:ℝ))≤
      ∫ u : Time in Ici t, (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst) u:ℝ) := by
  have := weightedTrialLaw_probability w q (fun i => (hw i).le) hw1
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    inferInstance
  refine ⟨quantileTrial_weightedTrialLaw w q (fun i => (hw i).le) hw1,?_⟩
  apply upper_tail_order_of_stoploss (boundedQuantile_measurable _)
    (boundedQuantile_monotone _)
  intro r
  rw [boundedQuantile_stoploss,boundedQuantile_stoploss,weightedTrialLaw_integral w q (fun i => (hw i).le)]
  exact source_global_contact_limit_stoploss_along k P f p d w q hw hw1 hq δ α H c hc hmin hH hcover hs hlim hcap r

end Contact

variable (k : ℕ) (P : Measure BrownianPath) (g : Jet3) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
variable (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P g.f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))
variable (hH : 0≤H) (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
variable {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
variable (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k g.f (fun i => p i.val) (fun i => d i.val)
  (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))

variable (hcap : ∀ᶠ n in atTop, (c (s n)).2.1 (Fin.last k)<H)

include hc hmin hH hcover hs hlim hcap hq in
 theorem source_global_contact_control_order_along [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) ≤
      controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1) := by
  obtain ⟨he,ht⟩ := source_global_contact_limit_tail_order_along k P g.f p d w q hw hw1 hq δ α H c
    hc hmin hH hcover hs hlim hcap
  have := weightedTrialLaw_probability w q (fun i => (hw i).le) hw1
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    inferInstance
  rw [← he]
  apply sourceQuantile_control_tail_order P hB g _ _ (boundedQuantile_monotone _)
    (boundedQuantile_monotone _)
  simpa only [timeLaw_eq_volume] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
