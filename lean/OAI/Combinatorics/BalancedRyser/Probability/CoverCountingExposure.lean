import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Probability.AtypicalLines
import OAI.Combinatorics.BalancedRyser.Probability.PermutationHistoryLaw

namespace OAI

namespace Balanced.CoverCountingExposure

noncomputable section
open Finset PermutationHistoryLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def Marked (U : Finset (Point F)) (ε : ℝ) (l : Line F) : Prop :=
  ε < |(affineIntersectionCount U l : ℝ) / (Fintype.card F : ℝ) -
    (U.card : ℝ) / (Fintype.card F : ℝ) ^ 2|

omit [Field F] in

theorem order_sq_le_card_unused (I : Finset (Line F))
    (hI : I.card ≤ Fintype.card F) (σ : Equiv.Perm (Line F)) :
    (Fintype.card F : ℝ) ^ 2 ≤ ((unused I σ).card : ℝ) := by
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (I.map σ.toEmbedding))
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcard
  have hIR : (I.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hI
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_prod,
    Fintype.card_option, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hcast
  change (Fintype.card F : ℝ) ^ 2 ≤
    ((Finset.univ \ I.map σ.toEmbedding).card : ℝ)
  nlinarith

theorem conditional_mark_le (I : Finset (Line F))
    (hI : I.card ≤ Fintype.card F) (σ : Equiv.Perm (Line F))
    (U : Finset (Point F)) {ε : ℝ} (hε : 0 < ε) :
    (𝔼 l ∈ unused I σ, if Marked U ε l then (1 : ℝ) else 0) ≤
      1 / (4 * ε ^ 2 * (Fintype.card F : ℝ)) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hden := order_sq_le_card_unused I hI σ
  have hdenpos : (0 : ℝ) < (unused I σ).card :=
    (sq_pos_of_pos hq).trans_le hden
  have hcount : (((unused I σ).filter (Marked U ε)).card : ℝ) ≤
      (Fintype.card F : ℝ) / (4 * ε ^ 2) := by
    apply le_trans _ (AtypicalLines.affine_card_marked_lines_le U ε hε)
    exact Nat.cast_le.mpr (Finset.card_le_card
      (Finset.filter_subset_filter (Marked U ε) (Finset.subset_univ (unused I σ))))
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.sum_boole]
  calc
    (((unused I σ).filter (Marked U ε)).card : ℝ) / ((unused I σ).card : ℝ) ≤
        ((Fintype.card F : ℝ) / (4 * ε ^ 2)) / ((unused I σ).card : ℝ) :=
      div_le_div_of_nonneg_right hcount hdenpos.le
    _ ≤ ((Fintype.card F : ℝ) / (4 * ε ^ 2)) / (Fintype.card F : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hq) hden
    _ = _ := by field_simp

theorem past_event_and_mark_le
    (I : Finset (Line F)) (hI : I.card ≤ Fintype.card F)
    (i : Line F) (hi : i ∉ I)
    (A : Equiv.Perm (Line F) → Prop)
    (U : Equiv.Perm (Line F) → Finset (Point F))
    (hA : ∀ σ τ, σ ∈ histories I τ → (A σ ↔ A τ))
    (hU : ∀ σ τ, σ ∈ histories I τ → U σ = U τ)
    {ε : ℝ} (hε : 0 < ε) :
    (𝔼 σ : Equiv.Perm (Line F),
      if A σ ∧ Marked (U σ) ε (σ i) then (1 : ℝ) else 0) ≤
      (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (𝔼 σ : Equiv.Perm (Line F), if A σ then (1 : ℝ) else 0) := by
  rw [expect_past_next I i hi
    (fun σ l => if A σ ∧ Marked (U σ) ε l then (1 : ℝ) else 0) (by
      intro σ τ hστ
      funext l
      simp only [hA σ τ hστ, hU σ τ hστ])]
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro σ _
  by_cases h : A σ
  · simp only [h, true_and, ite_true, mul_one]
    exact conditional_mark_le I hI σ (U σ) hε
  · simp only [h, false_and, ite_false, Finset.expect_const_zero, mul_zero, le_refl]

def pastUncovered (D : Finset (Line F)) (I : Finset (Line F))
    (σ : Equiv.Perm (Line F)) : Finset (Point F) :=
  uncoveredBy (D ∪ I.map σ.toEmbedding)

theorem pastUncovered_eq_of_history (D I : Finset (Line F))
    (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) :
    pastUncovered D I σ = pastUncovered D I τ := by
  simp only [pastUncovered, map_eq_of_history I σ τ h]

theorem pastUncovered_eq_of_larger_history (D J I : Finset (Line F))
    (hJI : J ⊆ I) (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) :
    pastUncovered D J σ = pastUncovered D J τ := by
  apply pastUncovered_eq_of_history D J σ τ
  apply (mem_histories J τ σ).mpr
  intro j hj
  exact (mem_histories I τ σ).mp h j (hJI hj)

theorem earlier_cover_mark_iff (D J I : Finset (Line F))
    (hJI : J ⊆ I) (j : Line F) (hj : j ∈ I)
    (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) (ε : ℝ) :
    Marked (pastUncovered D J σ) ε (σ j) ↔
      Marked (pastUncovered D J τ) ε (τ j) := by
  rw [pastUncovered_eq_of_larger_history D J I hJI σ τ h,
    (mem_histories I τ σ).mp h j hj]

theorem earlier_deletion_mark_iff (D J I : Finset (Line F))
    (hJI : J ⊆ I) (l : Line F)
    (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) (ε : ℝ) :
    Marked (pastUncovered D J σ) ε l ↔
      Marked (pastUncovered D J τ) ε l := by
  rw [pastUncovered_eq_of_larger_history D J I hJI σ τ h]

def priorMixedMarks {δ κ : Type*} (sD : Finset δ) (sC : Finset κ)
    (pastD₁ : δ → Finset (Line F)) (pastC₁ : δ → Finset (Line F))
    (targetD : δ → Line F)
    (pastD₂ : κ → Finset (Line F)) (pastC₂ : κ → Finset (Line F))
    (positionC : κ → Line F) (ε : ℝ) (σ : Equiv.Perm (Line F)) : Prop :=
  (∀ j ∈ sD, Marked (pastUncovered (pastD₁ j) (pastC₁ j) σ) ε (targetD j)) ∧
    ∀ j ∈ sC, Marked (pastUncovered (pastD₂ j) (pastC₂ j) σ) ε (σ (positionC j))

theorem priorMixedMarks_iff_of_history {δ κ : Type*}
    (sD : Finset δ) (sC : Finset κ)
    (pastD₁ : δ → Finset (Line F)) (pastC₁ : δ → Finset (Line F))
    (targetD : δ → Line F)
    (pastD₂ : κ → Finset (Line F)) (pastC₂ : κ → Finset (Line F))
    (positionC : κ → Line F) (I : Finset (Line F))
    (hD : ∀ j ∈ sD, pastC₁ j ⊆ I)
    (hC : ∀ j ∈ sC, pastC₂ j ⊆ I ∧ positionC j ∈ I)
    (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) (ε : ℝ) :
    priorMixedMarks sD sC pastD₁ pastC₁ targetD pastD₂ pastC₂ positionC ε σ ↔
      priorMixedMarks sD sC pastD₁ pastC₁ targetD pastD₂ pastC₂ positionC ε τ := by
  unfold priorMixedMarks
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · intro j hj
      exact (earlier_deletion_mark_iff _ _ I (hD j hj) _ σ τ h ε).mp (h₁ j hj)
    · intro j hj
      exact (earlier_cover_mark_iff _ _ I (hC j hj).1 _ (hC j hj).2 σ τ h ε).mp (h₂ j hj)
  · rintro ⟨h₁, h₂⟩
    constructor
    · intro j hj
      exact (earlier_deletion_mark_iff _ _ I (hD j hj) _ σ τ h ε).mpr (h₁ j hj)
    · intro j hj
      exact (earlier_cover_mark_iff _ _ I (hC j hj).1 _ (hC j hj).2 σ τ h ε).mpr (h₂ j hj)

theorem past_event_and_actual_mark_le
    (D I : Finset (Line F)) (hI : I.card ≤ Fintype.card F)
    (i : Line F) (hi : i ∉ I)
    (A : Equiv.Perm (Line F) → Prop)
    (hA : ∀ σ τ, σ ∈ histories I τ → (A σ ↔ A τ))
    {ε : ℝ} (hε : 0 < ε) :
    (𝔼 σ : Equiv.Perm (Line F),
      if A σ ∧ Marked (pastUncovered D I σ) ε (σ i) then (1 : ℝ) else 0) ≤
      (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (𝔼 σ : Equiv.Perm (Line F), if A σ then (1 : ℝ) else 0) :=
  past_event_and_mark_le I hI i hi A (pastUncovered D I) hA
    (pastUncovered_eq_of_history D I) hε

theorem prior_mixed_marks_and_actual_mark_le {δ κ : Type*}
    (sD : Finset δ) (sC : Finset κ)
    (pastD₁ : δ → Finset (Line F)) (pastC₁ : δ → Finset (Line F))
    (targetD : δ → Line F)
    (pastD₂ : κ → Finset (Line F)) (pastC₂ : κ → Finset (Line F))
    (positionC : κ → Line F)
    (D I : Finset (Line F)) (hI : I.card ≤ Fintype.card F)
    (i : Line F) (hi : i ∉ I)
    (hD : ∀ j ∈ sD, pastC₁ j ⊆ I)
    (hC : ∀ j ∈ sC, pastC₂ j ⊆ I ∧ positionC j ∈ I)
    {ε : ℝ} (hε : 0 < ε) :
    let A := priorMixedMarks sD sC pastD₁ pastC₁ targetD pastD₂ pastC₂ positionC ε
    (𝔼 σ : Equiv.Perm (Line F),
      if A σ ∧ Marked (pastUncovered D I σ) ε (σ i) then (1 : ℝ) else 0) ≤
      (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (𝔼 σ : Equiv.Perm (Line F), if A σ then (1 : ℝ) else 0) := by
  apply past_event_and_actual_mark_le D I hI i hi _ _ hε
  intro σ τ hστ
  exact priorMixedMarks_iff_of_history sD sC pastD₁ pastC₁ targetD pastD₂ pastC₂
    positionC I hD hC σ τ hστ ε

theorem measureReal_past_event_and_actual_mark_le
    [MeasurableSpace (Equiv.Perm (Line F))]
    [MeasurableSingletonClass (Equiv.Perm (Line F))]
    (D I : Finset (Line F)) (hI : I.card ≤ Fintype.card F)
    (i : Line F) (hi : i ∉ I)
    (A : Equiv.Perm (Line F) → Prop)
    (hA : ∀ σ τ, σ ∈ histories I τ → (A σ ↔ A τ))
    {ε : ℝ} (hε : 0 < ε) :
    (PMF.uniformOfFintype (Equiv.Perm (Line F))).toMeasure.real
      {σ | A σ ∧ Marked (pastUncovered D I σ) ε (σ i)} ≤
      (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (PMF.uniformOfFintype (Equiv.Perm (Line F))).toMeasure.real {σ | A σ} := by
  simpa only [uniform_measureReal_eq_expect] using
    past_event_and_actual_mark_le D I hI i hi A hA hε

theorem measure_actual_mark_inter_past_le
    [MeasurableSpace (Equiv.Perm (Line F))]
    [MeasurableSingletonClass (Equiv.Perm (Line F))]
    (D I : Finset (Line F)) (hI : I.card ≤ Fintype.card F)
    (i : Line F) (hi : i ∉ I)
    (A : Equiv.Perm (Line F) → Prop)
    (hA : ∀ σ τ, σ ∈ histories I τ → (A σ ↔ A τ))
    {ε : ℝ} (hε : 0 < ε) :
    (PMF.uniformOfFintype (Equiv.Perm (Line F))).toMeasure
      ({σ | Marked (pastUncovered D I σ) ε (σ i)} ∩ {σ | A σ}) ≤
      ENNReal.ofReal (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (PMF.uniformOfFintype (Equiv.Perm (Line F))).toMeasure {σ | A σ} := by
  apply (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have h := measureReal_past_event_and_actual_mark_le D I hI i hi A hA hε
  simpa only [MeasureTheory.Measure.real, Set.ofPred_and, Set.inter_comm] using h

omit [Field F] in

theorem witness_marginal (J : Finset (Line F)) (g : Finset (Line F) → ℝ) :
    (𝔼 σ : Equiv.Perm (Line F), g (J.map σ.toEmbedding)) =
      𝔼 C ∈ (Finset.univ : Finset (Line F)).powersetCard J.card, g C :=
  PermutationSubsetLaw.expect_image J g

omit [Field F] in

theorem witness_and_order_law (J : Finset (Line F))
    (g : Finset (Line F) → Equiv.Perm (Line F) → ℝ) :
    (𝔼 σ : Equiv.Perm (Line F), g (J.map σ.toEmbedding) σ) =
      𝔼 C ∈ (Finset.univ : Finset (Line F)).powersetCard J.card,
        𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Line F) =>
          J.map σ.toEmbedding = C), g C σ := by
  rw [expect_by_image J (fun σ => g (J.map σ.toEmbedding) σ)]
  apply Finset.expect_congr rfl
  intro C _
  apply Finset.expect_congr rfl
  intro σ hσ
  rw [(Finset.mem_filter.mp hσ).2]

theorem independent_outer_past_event_and_actual_mark_le
    {Ω : Type*} (S : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ S, 0 ≤ w ω)
    (D : Ω → Finset (Line F)) (I : Finset (Line F))
    (hI : I.card ≤ Fintype.card F) (i : Line F) (hi : i ∉ I)
    (A : Ω → Equiv.Perm (Line F) → Prop)
    (hA : ∀ ω ∈ S, ∀ σ τ, σ ∈ histories I τ → (A ω σ ↔ A ω τ))
    {ε : ℝ} (hε : 0 < ε) :
    (∑ ω ∈ S, w ω * (𝔼 σ : Equiv.Perm (Line F),
      if A ω σ ∧ Marked (pastUncovered (D ω) I σ) ε (σ i) then (1 : ℝ) else 0)) ≤
      (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        ∑ ω ∈ S, w ω *
          (𝔼 σ : Equiv.Perm (Line F), if A ω σ then (1 : ℝ) else 0) := by
  calc
    _ ≤ ∑ ω ∈ S, w ω * ((1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (𝔼 σ : Equiv.Perm (Line F), if A ω σ then (1 : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left
        (past_event_and_actual_mark_le (D ω) I hI i hi (A ω) (hA ω hω) hε) (hw ω hω)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

end
end Balanced.CoverCountingExposure

end OAI
