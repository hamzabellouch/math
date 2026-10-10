import OAI.Combinatorics.Ryser.Construction.AmbientDeletionShapes
import OAI.Combinatorics.Ryser.Construction.AmbientDeletionGeometry
import OAI.Combinatorics.Ryser.Construction.GroupBounds
import OAI.Combinatorics.Ryser.Probability.ProductMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientTrialOutcome (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : Point F) :
    LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K) :=
  ambientLineOutcome (deletedLines σ M b a) (by
    rw [card_deletedLines σ M b a ha]
    exact ambientDeletionConstant_lines_le _ _)

def ambientTrialLaw (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) :
    FiniteLaw (LineCover.Outcome (ambientShapes F)
      (ambientDeletionConstant (Fintype.card k) K)) :=
  (FiniteLaw.uniform (Point F)).map (ambientTrialOutcome σ M a ha K)

def ambientPointRate (σ : k →+* F) (M : PlaneLinearMap F) (a : GadgetOutcome k) : ℝ :=
  ((ambientLineUnion (deletedLines σ M 0 a)).card : ℝ) / (Fintype.card F : ℝ) ^ 2

theorem ambientTrialLaw_point_probability (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (x : Point F) :
    (ambientTrialLaw σ M a ha K).prob (fun A => x ∈ LineCover.deleted ∅ A) =
      ambientPointRate σ M a := by
  rw [ambientTrialLaw, FiniteLaw.prob_map]
  simp only [ambientTrialOutcome, deleted_empty_ambientLineOutcome]
  exact uniform_prob_mem_deletedLines_union σ M a x

theorem ambientPointRate_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) :
    ambientPointRate σ M a ≤ ((Fintype.card k - 1 : ℕ) : ℝ) ^ 2 / Fintype.card F := by
  have h := uniform_prob_mem_deletedLines_union_le σ M a (0 : Point F)
  rw [uniform_prob_mem_deletedLines_union, card_deletedLines σ M 0 a ha,
    Nat.cast_pow] at h
  exact h

theorem ambientTrialLaw_line_probability_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (l : AffineLine F) :
    (ambientTrialLaw σ M a ha K).prob (fun A => ∃ S ∈ A.val, S.val = linePoints l) ≤
      if l.1 ∈ alteredDirections σ M then
        ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F else 0 := by
  rw [ambientTrialLaw, FiniteLaw.prob_map]
  simp only [ambientTrialOutcome, ambientLineOutcome_lists_line]
  have h := uniform_prob_mem_deletedLines_le σ M a l
  by_cases hd : l.1 ∈ alteredDirections σ M
  · rw [ite_eq_left hd]
    rw [card_deletedLines_of_mem_alteredDirections σ M 0 a ha l.1 hd] at h
    exact h
  · rw [ite_eq_right hd]
    have hempty : ((deletedLines σ M 0 a).filter (fun e => e.1 = l.1)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he, hdir⟩ := Finset.mem_filter.mp he
      have hedir := ((mem_deletedLines σ M 0 a e).mp he).1
      exact hd (hdir ▸ hedir)
    simpa only [hempty, Finset.card_empty, Nat.cast_zero, zero_div] using h

abbrev AmbientPosition (σ : k →+* F) (K : ℕ) := ConfigurationGroup σ × Fin K

def ambientTrialCount (σ : k →+* F) (K : ℕ) : ℕ := Fintype.card (AmbientPosition σ K)

def ambientPosition (σ : k →+* F) (K : ℕ) (t : Fin (ambientTrialCount σ K)) :
    AmbientPosition σ K := (Fintype.equivFin (AmbientPosition σ K)).symm t

def ambientTrials (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (t : Fin (ambientTrialCount σ K)) :
    FiniteLaw (LineCover.Outcome (ambientShapes F)
      (ambientDeletionConstant (Fintype.card k) K)) :=
  ambientTrialLaw σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K

theorem ambientTrialCount_mul_sub_one_le (σ : k →+* F) (K : ℕ) :
    ambientTrialCount σ K * (Fintype.card k - 1) ≤ 2 * K * Fintype.card F := by
  unfold ambientTrialCount AmbientPosition
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    Fintype.card (ConfigurationGroup σ) * K * (Fintype.card k - 1) =
        K * (Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1)) := by ring
    _ ≤ K * (2 * Fintype.card F) :=
      Nat.mul_le_mul_left K (card_groups_mul_sub_one_le σ)
    _ = 2 * K * Fintype.card F := by ring

theorem ambientTrialCount_le (σ : k →+* F) (K : ℕ) (hs : 2 ≤ Fintype.card k) :
    ambientTrialCount σ K ≤ ambientDeletionConstant (Fintype.card k) K * Fintype.card F := by
  have hs' : 1 ≤ Fintype.card k - 1 := by omega
  calc
    ambientTrialCount σ K = ambientTrialCount σ K * 1 := by rw [Nat.mul_one]
    _ ≤ ambientTrialCount σ K * (Fintype.card k - 1) := Nat.mul_le_mul_left _ hs'
    _ ≤ 2 * K * Fintype.card F := ambientTrialCount_mul_sub_one_le σ K
    _ ≤ ambientDeletionConstant (Fintype.card k) K * Fintype.card F :=
      Nat.mul_le_mul_right _ (ambientDeletionConstant_trials_le _ _)

theorem ambientTrials_line_probability_sum_le (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (l : AffineLine F) :
    (∑ t, (ambientTrials σ u v huv a ha K t).prob
      (fun A => ∃ S ∈ A.val, S.val = linePoints l)) ≤
      (2 : ℝ) * K * ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F := by
  let rate : ℝ := ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F
  have hrate : 0 ≤ rate := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum : (∑ i : ConfigurationGroup σ,
      if l.1 ∈ groupAltered σ u v huv i then rate else 0) ≤ 2 * rate := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hmult : ((Finset.univ.filter
        (fun i => l.1 ∈ groupAltered σ u v huv i)).card : ℝ) ≤ 2 := by
      exact_mod_cast groupAltered_multiplicity_le_two σ u v huv l.1
    exact mul_le_mul_of_nonneg_right hmult hrate
  calc
    _ = ∑ p : AmbientPosition σ K,
        (ambientTrialLaw σ (groupPlacement σ u v huv p.1) a ha K).prob
          (fun A => ∃ S ∈ A.val, S.val = linePoints l) :=
      Equiv.sum_comp (Fintype.equivFin (AmbientPosition σ K)).symm _
    _ ≤ ∑ i : ConfigurationGroup σ, ∑ _j : Fin K,
        if l.1 ∈ groupAltered σ u v huv i then rate else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact ambientTrialLaw_line_probability_le σ (groupPlacement σ u v huv i) a ha K l
    _ = (K : ℝ) * ∑ i : ConfigurationGroup σ,
        if l.1 ∈ groupAltered σ u v huv i then rate else 0 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (2 * rate) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (2 : ℝ) * K * ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F := by
      dsimp only [rate]
      ring

end RyserCoveringCounterexample.Construction

end

end OAI
