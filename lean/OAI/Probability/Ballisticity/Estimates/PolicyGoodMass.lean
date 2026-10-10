import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyPMF

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_pmf_dependent_event {Ω G : Type*} [MeasurableSpace Ω]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    (p : Ω → PMF G) (hp : ∀ w, Measurable (fun ω => p ω w))
    (S : Ω → Set G) (hS : ∀ w, MeasurableSet {ω | w ∈ S ω}) :
    Measurable (fun ω => (p ω).toMeasure (S ω)) := by
  simp only [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
  apply Measurable.tsum
  intro w
  change Measurable (fun ω => Set.indicator {ω | w ∈ S ω} (fun ω => p ω w) ω)
  exact (hp w).indicator (hS w)

lemma finitePolicy_length_mass {Ω G : Type*} [Add G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)] [Countable G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ) :
    ∀ᵐ w ∂(finitePolicyPMF Q ω i x n).toMeasure, w.length=n := by
  rw [ae_iff,PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
  apply ENNReal.tsum_eq_zero.mpr
  intro w
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  split_ifs with h
  · rfl
  · exact finitePolicyPMF_length Q ω i x n w h

lemma probability_three_cover {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [IsProbabilityMeasure μ] (A B C : Set G)
    (hc : ∀ᵐ w ∂μ, w ∈ A ∨ w ∈ B ∨ w ∈ C) :
    1 ≤ μ A + (μ B+μ C) := by
  calc
    1 = μ Set.univ := (measure_univ).symm
    _ ≤ μ (A ∪ (B ∪ C)) := measure_mono_ae (hc.mono (fun w hw _ => hw))
    _ ≤ μ A + μ (B ∪ C) := measure_union_le _ _
    _ ≤ μ A + (μ B+μ C) := add_le_add_right (measure_union_le _ _) _

lemma ennreal_half_good {a b : ℝ≥0∞} (hab : 1 ≤ a+b) (hb : b < (1:ℝ≥0∞)/2) :
    (1:ℝ≥0∞)/2 ≤ a := by
  by_contra h
  have ha : a < (1:ℝ≥0∞)/2 := lt_of_not_ge h
  have ht : a+b < (1:ℝ≥0∞)/2 + (1:ℝ≥0∞)/2 := ENNReal.add_lt_add ha hb
  rw [ENNReal.add_halves] at ht
  exact (not_lt_of_ge hab) ht

lemma policy_good_mass {Ω G : Type*} [AddMonoid G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)] [Countable G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ)
    (Good : G → Prop) (M : List G → ℝ) (r : ℝ)
    (hcost : (finitePolicyPMF Q ω i x n).toMeasure {w | ¬policySafe Good x w} +
      (finitePolicyPMF Q ω i x n).toMeasure {w | r ≤ M w} < (1:ℝ≥0∞)/2) :
    (1:ℝ≥0∞)/2 ≤ (finitePolicyPMF Q ω i x n).toMeasure
      {w | w.length=n ∧ policySafe Good x w ∧ M w ≤ r} := by
  apply ennreal_half_good (probability_three_cover _ _ _ _ ?_) hcost
  filter_upwards [finitePolicy_length_mass Q ω i x n] with w hw
  by_cases hgood : policySafe Good x w
  · by_cases hm : M w ≤ r
    · exact Or.inl ⟨hw,hgood,hm⟩
    · exact Or.inr (Or.inr (le_of_lt (lt_of_not_ge hm)))
  · exact Or.inr (Or.inl hgood)

lemma low_mass_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (cost mass : Ω → ℝ≥0∞) (hc : AEMeasurable cost μ) (c : ℝ≥0∞)
    (hgood : ∀ ω, cost ω < (1:ℝ≥0∞)/2 → c ≤ mass ω) :
    μ {ω | mass ω < c} ≤ 2*(∫⁻ ω, cost ω ∂μ) := by
  have hs : {ω | mass ω < c} ⊆ {ω | (1:ℝ≥0∞)/2 ≤ cost ω} := by
    intro ω hw
    by_contra h
    exact (not_lt_of_ge (hgood ω (lt_of_not_ge h))) hw
  calc
    μ {ω | mass ω < c} ≤ μ {ω | (1:ℝ≥0∞)/2 ≤ cost ω} := measure_mono hs
    _ ≤ (∫⁻ ω, cost ω ∂μ)/((1:ℝ≥0∞)/2) := meas_ge_le_lintegral_div hc (by norm_num) (by norm_num)
    _ = 2*(∫⁻ ω, cost ω ∂μ) := by simp [div_eq_mul_inv,mul_comm]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
local instance CurvePolicyMeasurableMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤
local instance CurvePolicyMeasurableSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma policySafe_measurable {Ω G : Type*} [MeasurableSpace Ω] [Add G]
    (Good : Ω → G → Prop) (hG : ∀ x, MeasurableSet {ω | Good ω x}) (x : G) (w : List G) :
    MeasurableSet {ω | policySafe (Good ω) x w} := by
  induction w generalizing x with
  | nil => exact MeasurableSet.univ
  | cons u w ih => exact (hG x).inter (ih (x+u))

lemma curvePolicy_atom_measurable {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (i : ℕ) (x : Lattice d) (n : ℕ) (w : List (Lattice d)) :
    Measurable (fun ω => finitePolicyPMF (fun _ ω x => curvePolicyPMF
      (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n w) := by
  apply finitePolicyPMF_measurable_atom
  intro _ x u
  exact (Measure.measurable_coe (measurableSet_singleton u)).comp
    ((curvePolicy_rows (realPosition (step e)) f x b B hH E δ α dummy).mono (rowSigma_le _) le_rfl)

lemma curvePolicy_failure_measurable {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (i : ℕ) (x : Lattice d) (n : ℕ) :
    Measurable (fun ω => (finitePolicyPMF (fun _ ω x => curvePolicyPMF
      (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n).toMeasure
        {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w}) := by
  apply measurable_pmf_dependent_event _ (curvePolicy_atom_measurable e f b B hH E hδ hα dummy i x n)
  intro w
  apply MeasurableSet.compl
  apply policySafe_measurable
  intro y
  apply measurableSet_le measurable_const
  exact (Measure.measurable_coe MeasurableSet.univ).comp
    ((curveIncrement_rows (realPosition (step e)) f y b B hH).mono (rowSigma_le _) le_rfl)

lemma curvePolicy_fixed_event_measurable {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (i : ℕ) (x : Lattice d) (n : ℕ) (S : Set (List (Lattice d))) :
    Measurable (fun ω => (finitePolicyPMF (fun _ ω x => curvePolicyPMF
      (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n).toMeasure S) :=
  measurable_pmf_dependent_event _ (curvePolicy_atom_measurable e f b B hH E hδ hα dummy i x n)
    (fun _ => S) (fun w => MeasurableSet.const (w ∈ S))

end DirectionalTransience

end

end

end OAI
