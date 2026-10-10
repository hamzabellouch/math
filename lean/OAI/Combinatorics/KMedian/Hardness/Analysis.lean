import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Coverage
import OAI.Combinatorics.KMedian.Main

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Input
open Finset

def selectedMask (C : Input) (output : List Bool) : Finset (Fin C.n) :=
  univ.filter (fun i => (output[(C.facility i).val]?).getD false = true)

theorem selectedMask_eq_selected (C : Input) (T : Finset (Fin (C.m + C.n))) :
    C.selectedMask (List.ofFn (fun x : Fin (C.m + C.n) => decide (x ∈ T))) =
      C.selected T := by
  ext i
  simp [selectedMask, selected]

def comparisonCost (C : Input) (output : List Bool) : ℚ :=
  3 * (C.m : ℚ) - 2 * ((C.covered (C.selectedMask output)).card : ℚ)

def accepts (C : Input) (q : ℚ) (output : List Bool) : Bool :=
  decide (C.comparisonCost output < q * C.m)

theorem comparisonCost_eq_cost (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty)
    {output : List Bool} (hmask : output = List.ofFn (fun x => decide (x ∈ T))) :
    (C.comparisonCost output : ℝ) = cost C.toMedian T := by
  rw [C.cost_selected hT hne, hmask]
  simp [comparisonCost, C.selectedMask_eq_selected]

theorem accepts_of_perfect (C : Input) {α : ℝ} {q : ℚ} {output : List Bool}
    (hαq : α < (q : ℝ)) (h : C.Perfect)
    (hcorrect : FactorCorrect α C.toMedian output) : C.accepts q output = true := by
  obtain ⟨T, hT, hne, hk, hmask, hcost⟩ := hcorrect
  have hpos : (0 : ℝ) < C.m := by exact_mod_cast C.m_pos
  rw [C.optimum_of_perfect h] at hcost
  have hcmp : (C.comparisonCost output : ℝ) < (q : ℝ) * C.m := by
    rw [C.comparisonCost_eq_cost hT hne hmask]
    exact hcost.trans_lt (mul_lt_mul_of_pos_right hαq hpos)
  simp only [accepts, decide_eq_true_eq]
  exact_mod_cast hcmp

theorem rejects_of_sound (C : Input) {α δ : ℝ} {q : ℚ} {output : List Bool}
    (hq : (q : ℝ) ≤ 1 + 2 / Real.exp 1 - 2 * δ) (h : C.Sound δ)
    (hcorrect : FactorCorrect α C.toMedian output) : C.accepts q output = false := by
  obtain ⟨T, hT, hne, hk, hmask, _⟩ := hcorrect
  have hcost := C.cost_of_sound δ h hT hne hk
  have hcmp : (q : ℝ) * C.m ≤ (C.comparisonCost output : ℝ) := by
    rw [C.comparisonCost_eq_cost hT hne hmask]
    exact (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)).trans hcost
  simp only [accepts, decide_eq_false_iff_not]
  intro hlt
  have hlt' : (C.comparisonCost output : ℝ) < (q : ℝ) * C.m := by exact_mod_cast hlt
  exact (not_lt_of_ge hcmp) hlt'

end MetricKMedian.Coverage.Input

namespace MetricKMedian

theorem exists_coverage_margin {α : ℝ} (hα : α < 1 + 2 / Real.exp 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q : ℚ,
      α < (q : ℝ) ∧ (q : ℝ) < 1 + 2 / Real.exp 1 - 2 * δ := by
  let δ := (1 + 2 / Real.exp 1 - α) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hg : α < 1 + 2 / Real.exp 1 - 2 * δ := by dsimp [δ]; linarith
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hg
  exact ⟨δ, hδ, q, hq₁, hq₂⟩

theorem factor_above_threshold (ε : ℝ) (hε : 0 < ε) :
    1 + 2 / Real.exp 1 + ε ∈ approximationFactors := by
  obtain ⟨algorithm, p, hp, hcorrect⟩ := main_finite_work ε hε
  exact ⟨algorithm, ⟨p, hp⟩, hcorrect⟩

theorem approximationFactors_nonempty : approximationFactors.Nonempty :=
  ⟨1 + 2 / Real.exp 1 + 1, factor_above_threshold 1 zero_lt_one⟩

private def unitCoverage : Coverage.Input where
  m := 1
  n := 1
  incident _ _ := true
  k := 1
  m_pos := Nat.zero_lt_one
  k_pos := le_rfl
  k_le := le_rfl

private theorem unitCoverage_perfect : unitCoverage.Perfect := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · change (Finset.univ : Finset (Fin 1)).card ≤ 1
    simp
  · ext j
    rw [Coverage.Input.mem_covered]
    constructor
    · intro _; exact Finset.mem_univ j
    · intro _
      exact ⟨⟨0, Nat.zero_lt_one⟩, Finset.mem_univ _, rfl⟩

theorem factor_ge_one {α : ℝ} (hα : α ∈ approximationFactors) : 1 ≤ α := by
  obtain ⟨algorithm, _, hcorrect⟩ := hα
  obtain ⟨T, hT, hne, _, _, hcost⟩ := hcorrect unitCoverage.toMedian
  rw [unitCoverage.optimum_of_perfect unitCoverage_perfect] at hcost
  have hm : (unitCoverage.m : ℝ) = 1 := by norm_num [unitCoverage]
  rw [hm, mul_one] at hcost
  have hlow : (1 : ℝ) ≤ cost unitCoverage.toMedian T :=
    hm ▸ unitCoverage.cost_ge_universe hT hne
  exact hlow.trans hcost

theorem approximationFactors_bddBelow : BddBelow approximationFactors :=
  ⟨1, fun _ h => factor_ge_one h⟩

theorem approximationFactors_upward {α β : ℝ}
    (hα : α ∈ approximationFactors) (h : α ≤ β) : β ∈ approximationFactors := by
  obtain ⟨algorithm, p, hcorrect⟩ := hα
  refine ⟨algorithm, p, ?_⟩
  intro I
  obtain ⟨T, hT, hne, hk, hmask, hcost⟩ := hcorrect I
  exact ⟨T, hT, hne, hk, hmask,
    hcost.trans (mul_le_mul_of_nonneg_right h I.optimum_nonneg)⟩

theorem infimum_le_threshold :
    sInf approximationFactors ≤ 1 + 2 / Real.exp 1 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact csInf_le approximationFactors_bddBelow (factor_above_threshold ε hε)

theorem one_le_infimum : 1 ≤ sInf approximationFactors :=
  le_csInf approximationFactors_nonempty (fun _ h => factor_ge_one h)

end MetricKMedian

end Inline_PCPInherited

end OAI
