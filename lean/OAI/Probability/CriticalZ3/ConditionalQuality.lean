import OAI.Probability.CriticalZ3.Conditioning

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def conditionalProbability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (ξ : E → Bool) : ℝ :=
  (ProductCylinder.law (fixedParameter p J ξ)).real C

omit [Countable E] in
theorem conditionalProbability_determined (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) :
    ProductCylinder.DeterminedBy J (conditionalProbability p J C) := by
  intro ω ω' h
  unfold conditionalProbability
  rw [fixedParameter_congr p J h]

/-- Reveal-wise tower/Markov bound, valid also for histories of zero mass. -/
theorem conditional_failure_mass (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ : ℝ} (_hδ : 0 ≤ δ) :
    δ * (ProductCylinder.law p).real
      {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤
    (ProductCylinder.law p).real (H ∩ Cᶜ) := by
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let A (a : J → Bool) : Set (E → Bool) :=
    if ξ a ∈ H ∧ conditionalProbability p J C (ξ a) ≤ 1-δ then Set.univ else ∅
  let B (a : J → Bool) : Set (E → Bool) := if ξ a ∈ H then Cᶜ else ∅
  have hA (a) : MeasurableSet (A a) := by dsimp only [A]; split_ifs <;> measurability
  have hB (a) : MeasurableSet (B a) := by
    dsimp only [B]; split_ifs
    · exact hC.compl
    · exact MeasurableSet.empty
  have heA : {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} =
      {ω | ω ∈ A (J.restrict ω)} := by
    ext ω
    have hh := ProductCylinder.determinedBy_eq_extend hH ω
    have hc := ProductCylinder.determinedBy_eq_extend (conditionalProbability_determined p J C) ω
    change conditionalProbability p J C ω = conditionalProbability p J C (ξ (J.restrict ω)) at hc
    change (ω ∈ H) = (ξ (J.restrict ω) ∈ H) at hh
    simp only [Set.mem_ofPred_eq,A,hh,hc]
    split_ifs <;> simp_all
  have heB : H ∩ Cᶜ = {ω | ω ∈ B (J.restrict ω)} := by
    ext ω
    have hh := ProductCylinder.determinedBy_eq_extend hH ω
    change (ω ∈ H) = (ξ (J.restrict ω) ∈ H) at hh
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,B,hh]
    split_ifs <;> simp_all
  rw [heA,heB,measure_select p J A hA,measure_select p J B hB,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hcomp : (ProductCylinder.law (fixedParameter p J (ξ a))).real Cᶜ =
      1-conditionalProbability p J C (ξ a) := by
    simpa only [conditionalProbability,probReal_univ] using
      (measureReal_compl (μ := ProductCylinder.law (fixedParameter p J (ξ a))) hC)
  have hlocal : δ*(ProductCylinder.law (fixedParameter p J (ξ a))).real (A a) ≤
      (ProductCylinder.law (fixedParameter p J (ξ a))).real (B a) := by
    by_cases hha : ξ a ∈ H
    · simp only [A,B,hha,true_and,ite_true]
      split_ifs with hc
      · rw [probReal_univ,mul_one,hcomp]; linarith
      · rw [measureReal_empty,mul_zero]; exact measureReal_nonneg
    · simp only [A,B,hha,false_and,ite_false,measureReal_empty,mul_zero,le_refl]
  let hw := (ProductCylinder.law p).real (pattern J (ξ a))
  calc
    _ = hw*(δ*(ProductCylinder.law (fixedParameter p J (ξ a))).real (A a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlocal measureReal_nonneg

theorem conditional_failure_bound (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ ε : ℝ} (hδ : 0 < δ)
    (hfail : (ProductCylinder.law p).real (H ∩ Cᶜ) ≤ ε) :
    (ProductCylinder.law p).real {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤ ε/δ := by
  apply (le_div_iff₀ hδ).mpr
  simpa only [mul_comm] using (conditional_failure_mass p J H C hH hC hδ.le).trans hfail

end InfiniteConditioning

end OAI
