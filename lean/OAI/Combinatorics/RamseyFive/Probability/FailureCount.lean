import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {Ω X : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]

theorem weighted_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω→ℝ) {M t B : ℝ} (hf : ∀ω,|f ω|≤M) (hg : ∀ω,g ω∈Set.Icc 0 1)
    {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,g ω*(f ω)^p ∂μ)≤B) :
    μ.real {ω | g ω=1 ∧ t < |f ω|}≤B/t^p := by
  have hi : Integrable (fun ω => g ω*(f ω)^p) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (M^p)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hg ω).1,abs_pow]
      exact (mul_le_mul (hg ω).2 (pow_le_pow_left₀ (abs_nonneg _) (hf ω) p)
        (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq (one_mul _)
  have hnn : ∀ω,0≤g ω*(f ω)^p := fun ω => mul_nonneg (hg ω).1 (hp.pow_nonneg _)
  have hsub : {ω | g ω=1 ∧ t < |f ω|}⊆{ω | t^p≤g ω*(f ω)^p} := by
    intro ω hω
    change t^p≤g ω*(f ω)^p
    rw [hω.1,one_mul,←hp.pow_abs (f ω)]
    exact pow_le_pow_left₀ ht.le hω.2.le p
  apply (le_div_iff₀ (pow_pos ht p)).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
    (pow_nonneg ht.le p)).trans ((mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall hnn) hi (t^p)).trans hB)

noncomputable def failureCount (U : Finset X) (P : X→Ω→Prop) (ω : Ω) : ℝ :=
  (U.filter fun x => P x ω).card

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma failureCount_bounds (U : Finset X) (P : X→Ω→Prop) (ω : Ω) :
    0≤failureCount U P ω ∧ failureCount U P ω≤U.card := by
  exact ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (Finset.card_filter_le _ _)⟩

lemma integrable_failureCount (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Finset X) (P : X→Ω→Prop) : Integrable (failureCount U P) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (U.card:ℝ)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (failureCount_bounds U P ω).1]
    exact (failureCount_bounds U P ω).2

lemma integral_failureCount (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Finset X) (P : X→Ω→Prop) :
    (∫ω,failureCount U P ω ∂μ)=∑x∈U,μ.real {ω | P x ω} := by
  have he : failureCount U P=fun ω =>∑x∈U,({ω | P x ω}).indicator (fun _ => (1:ℝ)) ω := by
    funext ω
    simp only [failureCount,Set.indicator_apply,Set.mem_ofPred_eq,Finset.sum_boole]
  rw [he,integral_finsetSum U (fun x _ => (integrable_const (1:ℝ)).indicator
    (Set.to_countable _ |>.measurableSet))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_indicator_const (1:ℝ) (Set.to_countable _ |>.measurableSet)]
  simp

theorem failureCount_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset X) (P : X→Ω→Prop) (a : X→ℝ) {ε : ℝ} (hε : 0<ε)
    (ha : ∀x∈U,μ.real {ω | P x ω}≤a x) :
    μ.real {ω | ε≤failureCount U P ω}≤(∑x∈U,a x)/ε := by
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]
  apply (mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall
    (fun ω => (failureCount_bounds U P ω).1)) (integrable_failureCount μ U P) ε).trans
  rw [integral_failureCount]
  exact Finset.sum_le_sum ha

theorem expected_failureCount_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U bad : Finset X) (P : X→Ω→Prop) (a : X→ℝ) {ε : ℝ}
    (hε : 0≤ε) (ha : ∀x∈U,0≤a x)
    (hprob : ∀x∈U\bad,μ.real {ω | P x ω}≤ε+a x) :
    (∫ω,failureCount U P ω ∂μ)≤bad.card+(U.card:ℝ)*ε+∑x∈U,a x := by
  rw [integral_failureCount]
  calc
    _ ≤ ∑x∈U,((if x∈bad then (1:ℝ) else 0)+ε+a x) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hb : x∈bad
      · simp only [hb,ite_true]
        exact measureReal_le_one.trans (by linarith only [hε,ha x hx])
      · simp only [hb,ite_false,zero_add]
        exact hprob x (Finset.mem_sdiff.mpr ⟨hx,hb⟩)
    _ = ((U.filter fun x => x∈bad).card:ℝ)+(U.card:ℝ)*ε+∑x∈U,a x := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp only [Finset.sum_boole,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hc : ((U.filter fun x => x∈bad).card:ℝ)≤bad.card := Nat.cast_le.mpr
        (Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2))
      linarith only [hc]

omit [Countable Ω] [MeasurableSingletonClass Ω] in
theorem intersect_three_success (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B C D : Set Ω) {a b c d : ℝ} (hA : a≤μ.real A)
    (hB : μ.real B≤b) (hC : μ.real C≤c) (hD : μ.real D≤d) :
    a-b-c-d≤μ.real (A\(B∪C∪D)) := by
  have hsub : A⊆(A\(B∪C∪D))∪(B∪C∪D) := by
    intro ω hω
    by_cases h : ω∈B∪C∪D
    · exact Or.inr h
    · exact Or.inl ⟨hω,h⟩
  have hh := (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le (μ:=μ) _ _)
  have hbc := measureReal_union_le (μ:=μ) B C
  have hbcd := measureReal_union_le (μ:=μ) (B∪C) D
  linarith only [hA,hB,hC,hD,hh,hbc,hbcd]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {Ω : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]

theorem truncated_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω→ℝ) {M t B : ℝ} (hf : ∀ω,|f ω|≤M) (hg : ∀ω,g ω=0 ∨ g ω=1)
    {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,g ω*(f ω)^p ∂μ)≤B) :
    μ.real {ω | t < |f ω|}≤B/t^p+(∫ω,1-g ω ∂μ) := by
  have hgr : ∀ω,g ω∈Set.Icc 0 1 := fun ω => by rcases hg ω with h|h <;> simp [h]
  have h1 := weighted_moment_tail μ f g hf hgr hp ht hB
  have hi : (∫ω,1-g ω ∂μ)=μ.real {ω | g ω=0} := by
    have he : (fun ω => 1-g ω)=({ω | g ω=0}).indicator (fun _ => (1:ℝ)) := by
      funext ω
      rcases hg ω with h|h <;> simp [h]
    rw [he,integral_indicator_const (1:ℝ) (Set.to_countable _ |>.measurableSet)]
    simp
  have hs : {ω | t < |f ω|}⊆{ω | g ω=1 ∧ t < |f ω|}∪{ω | g ω=0} := by
    intro ω hω
    rcases hg ω with h|h
    · exact Or.inr h
    · exact Or.inl ⟨h,hω⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_union_le _ _)).trans
    (by rw [hi];exact add_le_add h1 (le_refl _))

end SharpRamseyFive.PoissonScore

end OAI
