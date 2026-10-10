import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.AeEvalNe

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

lemma integral_sq_le_mass_mul (f : X → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real Set.univ * ∫ x, (f x)^2 ∂μ := by
  have hp (c : ℝ) : 0 ≤ μ.real Set.univ * (c*c) +
      (-2*(∫ x, f x ∂μ))*c + ∫ x, (f x)^2 ∂μ := by
    have hi : (∫ x, (f x-c)^2 ∂μ) =
        μ.real Set.univ * (c*c) + (-2*(∫ x, f x ∂μ))*c + ∫ x, (f x)^2 ∂μ := by
      calc
        (∫ x, (f x-c)^2 ∂μ) =
            ∫ x, ((f x)^2 - (2*c)*f x) + c*c ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by ring)
        _ = _ := by
          have ha := integral_add (hf2.sub (hf.const_mul (2*c))) (integrable_const (c*c))
          have hs := integral_sub hf2 (hf.const_mul (2*c))
          simp only [Pi.sub_apply] at ha
          rw [ha, hs, integral_const_mul, integral_const, smul_eq_mul]
          ring
    rw [← hi]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.Priority
open FiniteEntropy

variable {I : Type*} [Fintype I]

noncomputable def orderMass (o : Order I) : ℝ := ∫ _u in cell o, (1:ℝ) ∂law
noncomputable def orderWeight (o : Order I) (i : I) : ℝ :=
  ∫ u in cell o, endpointKernel (u i) ∂law
noncomputable def orderSquare (o : Order I) (i : I) : ℝ :=
  ∫ u in cell o, (endpointKernel (u i))^2 ∂law

lemma orderMass_nonneg (o : Order I) : 0 ≤ orderMass o := integral_nonneg (fun _ => zero_le_one)
lemma orderSquare_nonneg (o : Order I) (i : I) : 0 ≤ orderSquare o i :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma orderWeight_sq_le (o : Order I) (i : I) :
    (orderWeight o i)^2 ≤ orderSquare o i * orderMass o := by
  have h := integral_sq_le_mass_mul (μ := law.restrict (cell o))
    (fun u : I → ℝ => endpointKernel (u i))
    (integrable_eval_continuous _ continuous_endpointKernel i).restrict
    (integrable_eval_continuous (fun r => (endpointKernel r)^2) (continuous_endpointKernel.pow 2) i).restrict
  simpa only [orderWeight, orderSquare, orderMass, integral_const, smul_eq_mul,
    mul_one, mul_comm, one_mul] using h

lemma sum_orderMass : (∑ o : Order I, orderMass o) = 1 := by
  rw [show (∑ o : Order I, orderMass o) = ∑ o : Order I, ∫ _u in cell o, (1:ℝ) ∂law from rfl,
    sum_integral_cells _ (integrable_const 1)]
  simp

lemma sum_orderSquare (i : I) : (∑ o : Order I, orderSquare o i) = 16 := by
  rw [show (∑ o : Order I, orderSquare o i) =
      ∑ o : Order I, ∫ u in cell o, (endpointKernel (u i))^2 ∂law from rfl,
    sum_integral_cells _ (integrable_eval_continuous (fun r => (endpointKernel r)^2) (continuous_endpointKernel.pow 2) i)]
  exact square_weight_integral i

noncomputable def priorList (o : Order I) (i : I) : List I := (order_split o i).choose
noncomputable def suffix (o : Order I) (i : I) : List I := (order_split o i).choose_spec.choose

lemma priorList_suffix (o : Order I) (i : I) :
    o.val = priorList o i ++ i::suffix o i ∧ i ∉ priorList o i ∧ i ∉ suffix o i :=
  (order_split o i).choose_spec.choose_spec

lemma not_before_iff (u : I → ℝ) (o : Order I) (hu : u ∈ cell o) {i j : I}
    (hji : j ≠ i) : j ∉ priorList o i ↔ u i < u j := by
  have he := (priorList_suffix o i).1
  have hb := before_iff u o hu he hji
  constructor
  · intro hn
    have hp := hu
    rw [cell, Set.mem_ofPred_eq, he, List.pairwise_append, List.pairwise_cons] at hp
    have hm := mem_order o j
    rw [he, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact False.elim (hn hm)
    · exact False.elim (hji hm)
    · exact hp.2.1.1 j hm
  · intro h hj
    exact lt_asymm (hb.mp hj) h

def First (o : Order I) (i : I) (S : Finset {j : I // j ≠ i}) : Prop :=
  ∀ j ∈ S, j.val ∉ priorList o i

lemma first_iff_fresh (o : Order I) (i : I) (S : Finset {j : I // j ≠ i})
    (u : I → ℝ) (hu : u ∈ cell o) : First o i S ↔ u ∈ freshSet i S := by
  dsimp [First, freshSet]
  exact forall₂_congr (fun j _ => not_before_iff u o hu j.property)

lemma weighted_first_identity (i : I) (S : Finset {j : I // j ≠ i}) (hS : S.card ≤ 3) :
    (∑ o : Order I, if First o i S then orderWeight o i else 0) = 1 := by
  let F : (I → ℝ) → ℝ := (freshSet i S).indicator (fun u => endpointKernel (u i))
  have hf : Integrable F law :=
    (integrable_eval_continuous _ continuous_endpointKernel i).indicator (measurableSet_freshSet i S)
  have hi (o : Order I) : (∫ u in cell o, F u ∂law) =
      if First o i S then orderWeight o i else 0 := by
    by_cases h : First o i S
    · rw [ite_eq_left h]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_cell o)] with u hu
      exact Set.indicator_of_mem ((first_iff_fresh o i S u hu).mp h) _
    · rw [ite_eq_right h]
      trans ∫ u in cell o, (0:ℝ) ∂law
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_cell o)] with u hu
        exact Set.indicator_of_notMem (fun hm => h ((first_iff_fresh o i S u hu).mpr hm)) _
      · simp
  calc
    (∑ o : Order I, if First o i S then orderWeight o i else 0) =
        ∑ o : Order I, ∫ u in cell o, F u ∂law := by simp_rw [hi]
    _ = ∫ u, F u ∂law := sum_integral_cells F hf
    _ = 1 := by
      rw [show F = (freshSet i S).indicator (fun u => endpointKernel (u i)) from rfl,
        integral_indicator (measurableSet_freshSet i S)]
      exact weighted_fresh_identity i S hS

end CriticalPercolation.Priority

open scoped Classical

end
end

end OAI
