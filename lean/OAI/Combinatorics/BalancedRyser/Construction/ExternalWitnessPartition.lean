import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessModel

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def swapKey (w : WitnessKey F) : WitnessKey F :=
  ((w.1.1, (w.1.2.2, w.1.2.1)), (w.2.2, w.2.1))

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem swapKey_swapKey (w : WitnessKey F) : swapKey (swapKey w) = w := by
  rcases w with ⟨⟨T, i, j⟩, d, e⟩
  rfl

omit [Fintype F] in
@[simp] theorem witnessEvent_swapKey (g : Direction F) (w : WitnessKey F)
    (M : MergedPairs F) : M ∈ witnessEvent g (swapKey w) ↔ M ∈ witnessEvent g w := by
  simp only [witnessEvent, swapKey, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hs, hij, hde, he, hd, heT, hdT, x, hx, hex, hej, hdi⟩
    exact ⟨hs, hij.symm, hde.symm, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩
  · rintro ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩
    exact ⟨hs, hij.symm, hde.symm, he, hd, heT, hdT, x, hx, hex, hej, hdi⟩

@[simp] theorem swapKey_mem_witnesses (g : Direction F) (M : MergedPairs F)
    (w : WitnessKey F) : swapKey w ∈ witnesses g M ↔ w ∈ witnesses g M := by
  simp only [mem_witnesses, witnessEvent_swapKey]

theorem filter_card_swapKey (g : Direction F) (M : MergedPairs F)
    (P : WitnessKey F → Prop) :
    ((witnesses g M).filter (fun w => P (swapKey w))).card =
      ((witnesses g M).filter P).card := by
  apply Finset.card_bij (fun w _ => swapKey w)
  · intro w hw
    obtain ⟨hw, hP⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨(swapKey_mem_witnesses g M w).mpr hw, hP⟩
  · intro w hw v hv h
    have h' := congrArg swapKey h
    simpa only [swapKey_swapKey] using h'
  · intro w hw
    obtain ⟨hw, hP⟩ := Finset.mem_filter.mp hw
    exact ⟨swapKey w, Finset.mem_filter.mpr
      ⟨(swapKey_mem_witnesses g M w).mpr hw, by simpa using hP⟩, by simp⟩

theorem card_le_bothFresh_add_twice_firstOld (g : Direction F)
    (M : MergedPairs F) (D : Finset (Direction F)) :
    (witnesses g M).card ≤
      ((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card +
      2 * ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card := by
  have hswap : ((witnesses g M).filter (fun w => w.2.2 ∈ D)).card =
      ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card := by
    convert filter_card_swapKey g M (fun w => w.2.1 ∈ D) using 1 <;>
      congr 1 <;> symm <;> apply Finset.filter_congr_decidable
  have h : (witnesses g M).card ≤
      ((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card +
      ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card +
      ((witnesses g M).filter (fun w => w.2.2 ∈ D)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w hw
    by_cases hd : w.2.1 ∈ D <;> by_cases he : w.2.2 ∈ D <;> simp [hd, he]
  omega

theorem firstOld_card_eq_three_cases (g : Direction F)
    (M : MergedPairs F) (D : Finset (Direction F)) (P : FourTuple F → Prop) :
    ((witnesses g M).filter (fun w => w.2.1 ∈ D)).card =
      ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card +
      ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card +
      ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hd : w.2.1 ∈ D <;> by_cases he : w.2.2 ∈ D <;>
    by_cases hP : P w.1.1 <;> simp [hd, he, hP]

theorem card_le_four_cases (g : Direction F) (M : MergedPairs F)
    (D : Finset (Direction F)) (P : FourTuple F → Prop) :
    (witnesses g M).card ≤
      ((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card + 2 *
      (((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card +
       ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card +
       ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card) := by
  rw [← firstOld_card_eq_three_cases]
  exact card_le_bothFresh_add_twice_firstOld g M D

open MeasureTheory
local instance : MeasurableSpace F := ⊤

theorem integral_card_le_four_cases (g : Direction F)
    (D : Finset (Direction F)) (P : FourTuple F → Prop)
    (law : PMF (MergedPairs F)) :
    (∫ M, ((witnesses g M).card : ℝ) ∂law.toMeasure) ≤
      (∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card : ℝ) ∂law.toMeasure) + 2 *
      ((∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card : ℝ) ∂law.toMeasure) +
       (∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card : ℝ) ∂law.toMeasure) +
       (∫ M, (((witnesses g M).filter
        (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card : ℝ) ∂law.toMeasure)) := by
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  calc
    _ ≤ ∑ M : MergedPairs F, (law M).toReal *
        ((((witnesses g M).filter (fun w => w.2.1 ∉ D ∧ w.2.2 ∉ D)).card : ℝ) +
          2 * (((((witnesses g M).filter
            (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧ P w.1.1)).card : ℝ)) +
            (((witnesses g M).filter
            (fun w => w.2.1 ∈ D ∧ w.2.2 ∉ D ∧ P w.1.1)).card : ℝ) +
            (((witnesses g M).filter
            (fun w => w.2.1 ∈ D ∧ ¬ P w.1.1)).card : ℝ))) := by
      apply Finset.sum_le_sum
      intro M hM
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast card_le_four_cases g M D P
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      simp only [mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]

end
end Balanced.ExternalAssembly

end OAI
