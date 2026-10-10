import Mathlib

namespace OAI

namespace SharpRamseyFive.MeasurePublicTable
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {α : Type*}

noncomputable def firstIndex (E : Set α) {N : ℕ} (t : Fin N→α) : Option (Fin N) :=
  if h : (Finset.univ.filter (fun i=>t i∈E)).Nonempty then
    some ((Finset.univ.filter (fun i=>t i∈E)).min' h) else none

lemma firstIndex_none_iff (E : Set α) {N : ℕ} (t : Fin N→α) :
    firstIndex E t=none ↔ ∀i,t i∉E := by
  unfold firstIndex
  split_ifs with h
  · simp only [false_iff]
    simpa only [Finset.nonempty_def,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using h
  · simp only [true_iff]
    simpa only [Finset.not_nonempty_iff_eq_empty,Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies] using h

lemma firstIndex_some_mem (E : Set α) {N : ℕ} (t : Fin N→α) {i : Fin N}
    (hi : firstIndex E t=some i) : t i∈E := by
  unfold firstIndex at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    have hm := Finset.min'_mem (Finset.univ.filter (fun i=>t i∈E)) h
    rw [he] at hm
    exact (Finset.mem_filter.mp hm).2

lemma firstIndex_minimal (E : Set α) {N : ℕ} (t : Fin N→α) {i : Fin N}
    (hi : firstIndex E t=some i) : ∀ j, j < i → t j∉E := by
  unfold firstIndex at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    intro j hj hE
    have hh := Finset.min'_le (Finset.univ.filter (fun i=>t i∈E)) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hE⟩)
    rw [he] at hh
    exact (not_le_of_gt hj) hh

variable [MeasurableSpace α]

lemma firstIndex_failure_mass (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}=(1-μ.real E)^N := by
  have he : {t : Fin N→α | firstIndex E t=none}=Set.univ.pi (fun _=>Eᶜ) := by
    ext t
    simp only [Set.mem_ofPred_eq,firstIndex_none_iff,Set.mem_univ_pi,Set.mem_compl_iff]
  rw [he,measureReal_def,Measure.pi_pi,ENNReal.toReal_prod]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←measureReal_def,measureReal_compl hE]
  simp

lemma firstIndex_failure_le (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ) {p : ℝ} (hp : p≤μ.real E) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}≤Real.exp (-p*N) := by
  rw [firstIndex_failure_mass μ E hE N]
  have hbase : 1-μ.real E≤Real.exp (-p) := by
    have hh := Real.add_one_le_exp (-p)
    linarith
  calc
    _ ≤ (Real.exp (-p))^N := pow_le_pow_left₀ (sub_nonneg.mpr (measureReal_le_one)) hbase N
    _ = _ := by rw [←Real.exp_nat_mul];congr 1;ring

theorem finite_cutoff_failure (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) {A q : ℝ} (_hq : 0≤q) (N : ℕ)
    (hp : Real.exp (-A)≤μ.real E) (hN : q*Real.exp A≤N) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}≤Real.exp (-q) := by
  apply (firstIndex_failure_le μ E hE N hp).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (-A))
  have he : Real.exp (-A)*(q*Real.exp A)=q := by
    rw [mul_left_comm,←Real.exp_add]
    simp
  rw [he] at hh
  linarith

end SharpRamseyFive.MeasurePublicTable

end OAI
