import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma bounded_first_moment_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→ℝ)
    (hmeas : Measurable f) {C a : ℝ} (hC : 0<C) (ha : 0≤a)
    (hbound : ∀ ω,0≤f ω ∧ f ω≤C)
    (hmean : C*a≤∫ ω,f ω ∂μ) :
    a/2≤μ.real {ω | C*a/2≤f ω} := by
  let E := {ω | C*a/2≤f ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hmeas
  have hf : Integrable f μ := Integrable.of_bound hmeas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hbound ω).1];exact (hbound ω).2)
  have he : Integrable (fun ω => C*a/2+C*E.indicator (fun _ => (1:ℝ)) ω) μ :=
    (integrable_const _).add (((integrable_const (1:ℝ)).indicator hE).const_mul C)
  have hb : ∫ ω,f ω ∂μ ≤ C*a/2+C*μ.real E := by
    calc
      _ ≤ ∫ ω,C*a/2+C*E.indicator (fun _ => (1:ℝ)) ω ∂μ := integral_mono hf he fun ω => by
        by_cases h : ω∈E
        · simp only [Set.indicator_of_mem h]
          linarith [(hbound ω).2,mul_nonneg hC.le ha]
        · have hn : f ω<C*a/2 := lt_of_not_ge h
          simp only [Set.indicator_of_notMem h,mul_zero,add_zero]
          exact hn.le
      _ = _ := by rw [integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator hE).const_mul C),
        integral_const_mul,integral_indicator_const (1:ℝ) hE];simp
  change a/2≤μ.real E
  nlinarith

variable {ι H : Type*} [Fintype ι]

noncomputable def allEmptyIndicator {R : ℕ} (s : Finset ι) (ω : Fin R→ι→ℕ) : ℝ :=
  ∏ r,emptyIndicator s (ω r)

omit [Fintype ι] in
lemma allEmptyIndicator_eq_if {R : ℕ} (s : Finset ι) (ω : Fin R→ι→ℕ) :
    allEmptyIndicator s ω=if (∀r,ω r∈emptyEvent s) then 1 else 0 := by
  by_cases h : ∀r,ω r∈emptyEvent s
  · simp [allEmptyIndicator,emptyIndicator,h]
  · rw [ite_eq_right h]
    obtain ⟨r,hr⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [emptyIndicator,hr])

omit [Fintype ι] in
lemma allEmptyIndicator_bounds {R : ℕ} (s : Finset ι) (ω : Fin R→ι→ℕ) :
    0≤allEmptyIndicator s ω ∧ allEmptyIndicator s ω≤1 := by
  rw [allEmptyIndicator_eq_if]
  split_ifs <;> norm_num

lemma integrable_allEmptyIndicator (rate : ι→ℝ≥0) {R : ℕ} (s : Finset ι) :
    Integrable (allEmptyIndicator (R:=R) s) (scheduleMeasure rate R) := by
  exact Integrable.fintype_prod (fun _ => integrable_emptyIndicator rate s)

lemma integral_allEmptyIndicator (rate : ι→ℝ≥0) {R : ℕ} (s : Finset ι) :
    (∫ ω,allEmptyIndicator s ω ∂scheduleMeasure rate R)=Real.exp (-(R:ℝ)*mass rate s) := by
  unfold allEmptyIndicator scheduleMeasure
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_emptyIndicator,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←Real.exp_nat_mul]
  congr 1
  ring

noncomputable def emptyTests {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (ω : Fin R→ι→ℕ) : Finset H := E.filter fun h => ∀r,ω r∈emptyEvent (lines h)

omit [Fintype ι] in
lemma emptyTests_card {R : ℕ} (E : Finset H) (lines : H→Finset ι) (ω : Fin R→ι→ℕ) :
    ((emptyTests E lines ω).card:ℝ)=∑h∈E,allEmptyIndicator (lines h) ω := by
  simp only [allEmptyIndicator_eq_if,emptyTests,Finset.sum_boole]

omit [Fintype ι] in
lemma emptyTests_subset {R : ℕ} (E : Finset H) (lines : H→Finset ι) (ω : Fin R→ι→ℕ) :
    emptyTests E lines ω⊆E := Finset.filter_subset ..

lemma integrable_emptyTests_card (rate : ι→ℝ≥0) {R : ℕ} (E : Finset H) (lines : H→Finset ι) :
    Integrable (fun ω : Fin R→ι→ℕ => ((emptyTests E lines ω).card:ℝ)) (scheduleMeasure rate R) := by
  simp_rw [emptyTests_card]
  exact integrable_finsetSum E fun h _ => integrable_allEmptyIndicator rate (lines h)

lemma integral_emptyTests_card (rate : ι→ℝ≥0) {R : ℕ} (E : Finset H) (lines : H→Finset ι) :
    (∫ ω,((emptyTests E lines ω).card:ℝ) ∂scheduleMeasure rate R)=
      ∑h∈E,Real.exp (-(R:ℝ)*mass rate (lines h)) := by
  simp_rw [emptyTests_card]
  rw [integral_finsetSum E (fun h _ => integrable_allEmptyIndicator rate (lines h))]
  simp only [integral_allEmptyIndicator]

theorem emptyTests_probability (rate : ι→ℝ≥0) {R : ℕ} (E T : Finset H)
    (hT : T.Nonempty) (hTE : T⊆E) (lines : H→Finset ι) {a : ℝ}
    (hm : ∀h∈T,mass rate (lines h)≤a) :
    Real.exp (-(R:ℝ)*a)/2≤(scheduleMeasure rate R).real
      {ω | (T.card:ℝ)*Real.exp (-(R:ℝ)*a)/2≤((emptyTests E lines ω).card:ℝ)} := by
  have hC : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  have hmean : (T.card:ℝ)*Real.exp (-(R:ℝ)*a)≤
      ∫ ω,((emptyTests T lines ω).card:ℝ) ∂scheduleMeasure rate R := by
    rw [integral_emptyTests_card]
    calc
      _ = ∑_h∈T,Real.exp (-(R:ℝ)*a) := by simp
      _ ≤ _ := Finset.sum_le_sum fun h hh => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hm h hh) (neg_nonpos.mpr (Nat.cast_nonneg _)))
  have h := bounded_first_moment_probability (scheduleMeasure rate R)
    (fun ω => ((emptyTests T lines ω).card:ℝ)) (measurable_of_countable _) hC
    (Real.exp_pos _).le
    (fun ω => ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (Finset.card_le_card (emptyTests_subset T lines ω))⟩) hmean
  apply h.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change (T.card:ℝ)*Real.exp (-(R:ℝ)*a)/2≤((emptyTests T lines ω).card:ℝ) at hω
  change (T.card:ℝ)*Real.exp (-(R:ℝ)*a)/2≤((emptyTests E lines ω).card:ℝ)
  apply hω.trans
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hTE))

end SharpRamseyFive.PoissonScore

end OAI
