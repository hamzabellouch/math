import OAI.Combinatorics.Ryser.Selection.ChunkEnergy
import OAI.Combinatorics.Ryser.Selection.ChunkLoss
import OAI.Combinatorics.Ryser.Selection.IndependentTail
import OAI.Combinatorics.Ryser.Selection.RegularTail
import OAI.Combinatorics.Ryser.Selection.Estimates
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

def equationBound (D : ℕ) : ℝ := 2 * (D : ℝ) ^ 3

def regularTailConstant (D : ℕ) (γ : ℝ) : ℝ :=
  (8 * equationBound D * (D : ℝ) ^ 7 + 2 * (D : ℝ) ^ 5) / γ ^ 2

def RegularEntry (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : Prop :=
  sourceEnergy data I U j ≤ (I.card : ℝ) * Fintype.card F *
    Real.sqrt (Fintype.card F)

noncomputable def regularEntries (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) :
    Finset (Position n K) := by
  classical
  exact E.filter (fun e => RegularEntry data I U e.1)

theorem regularTailConstant_nonneg (D : ℕ) (γ : ℝ) :
    0 ≤ regularTailConstant D γ := by
  unfold regularTailConstant equationBound
  positivity

theorem prob_regular_entry_gt_le (D : ℕ) (hD : 1 ≤ D) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hregular : RegularEntry data I U j) :
    (FiniteLaw.uniform (Point F)).prob (fun x =>
      equationBound D * frozenMass I U / Fintype.card F +
        γ * I.card * Fintype.card F < entryLoss data I U j x) ≤
      regularTailConstant D γ / Real.sqrt (Fintype.card F) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hC : 0 < equationBound D := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
    unfold equationBound
    positivity
  have hmean : (FiniteLaw.uniform (Point F)).expectation (entryLoss data I U j) ≤
      equationBound D * frozenMass I U / Fintype.card F := by
    simpa only [equationBound] using expectation_entryLoss_le D data hdata I U j
  have hvar : (FiniteLaw.uniform (Point F)).variance (entryLoss data I U j) ≤
      2 * (D : ℝ) ^ 7 * I.card * (Fintype.card F : ℝ) ^ 2 +
        2 * (D : ℝ) ^ 5 * (I.card : ℝ) ^ 2 * Fintype.card F *
          Real.sqrt (Fintype.card F) := by
    have hactual := variance_entryLoss_le D data hdata I U j
    have hmul := mul_le_mul_of_nonneg_left hregular
      (by positivity : 0 ≤ 2 * (D : ℝ) ^ 5 * I.card)
    unfold RegularEntry at hregular
    change 2 * (D : ℝ) ^ 5 * I.card * sourceEnergy data I U j ≤
      2 * (D : ℝ) ^ 5 * I.card *
        ((I.card : ℝ) * Fintype.card F * Real.sqrt (Fintype.card F)) at hmul
    nlinarith
  exact prob_regular_target_gt_le_sqrt (FiniteLaw.uniform (Point F))
    (entryLoss data I U j) D I.card (Fintype.card F) γ (equationBound D)
    (frozenMass I U) (Nat.cast_nonneg D) hm hq hγ hC hlarge hmean hvar

theorem card_irregularEntries_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) (hm : 0 < (I.card : ℝ)) :
    ((E.filter (fun e : Position n K => ¬ RegularEntry data I U e.1)).card : ℝ) ≤
      (K : ℝ) * D * Real.sqrt (Fintype.card F) := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  simpa only [RegularEntry, not_le] using card_irregular_le E
    (fun e => sourceEnergy data I U e.1) K D I.card (Fintype.card F) hm hq
    (fun e _ => sourceEnergy_nonneg data I U e.1)
    (sum_sourceEnergy_le D data hdata I U E)

theorem prob_many_regular_exceedances_le (D : ℕ) (hD : 1 ≤ D) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) (γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card) :
    (FiniteLaw.pi (fun _ : Position n K => FiniteLaw.uniform (Point F))).prob
      (fun pool => Nat.ceil (γ * Fintype.card F) ≤
        ((regularEntries data I U E).filter (fun e =>
          equationBound D * frozenMass I U / Fintype.card F +
            γ * I.card * Fintype.card F < entryLoss data I U e.1 (pool e))).card) ≤
      (2 : ℝ) ^ E.card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  have hp : 0 ≤ regularTailConstant D γ / Real.sqrt (Fintype.card F) :=
    div_nonneg (regularTailConstant_nonneg D γ) (Real.sqrt_nonneg _)
  have htail := prob_many_coordinate_events_le
    (fun _ : Position n K => FiniteLaw.uniform (Point F))
    (regularEntries data I U E)
    (fun e x => equationBound D * frozenMass I U / Fintype.card F +
      γ * I.card * Fintype.card F < entryLoss data I U e.1 x)
    (Nat.ceil (γ * Fintype.card F))
    (regularTailConstant D γ / Real.sqrt (Fintype.card F)) hp
    (fun e he => prob_regular_entry_gt_le D hD data hdata I U e.1 γ hm hγ hlarge
      (Finset.mem_filter.mp he).2)
  refine htail.trans ?_
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_filter_le _ _)

theorem chunk_recurrence_of_few_regular_exceedances (D : ℕ) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) (α γ : ℝ) (hm : 0 < (I.card : ℝ)) (hγ : 0 ≤ γ)
    (hhalf : equationBound D * α = 1 / 2)
    (hsize : (E.card : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F)
    (hfew : ((regularEntries data I U E).filter (fun e =>
      equationBound D * frozenMass I U / Fintype.card F +
        γ * I.card * Fintype.card F < entryLoss data I U e.1 (pool e))).card <
      Nat.ceil (γ * Fintype.card F)) :
    frozenMass I U / 2 - (α + 2 * equationBound D) * γ *
        ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2) ≤
      frozenMass I (chunkFeasibleSet data U E pool) := by
  classical
  let threshold := equationBound D * frozenMass I U / Fintype.card F +
    γ * I.card * Fintype.card F
  let bad : Position n K → Prop := fun e =>
    ¬ RegularEntry data I U e.1 ∨ threshold < entryLoss data I U e.1 (pool e)
  let irregular := E.filter (fun e : Position n K => ¬ RegularEntry data I U e.1)
  let exceeds := (regularEntries data I U E).filter (fun e =>
    threshold < entryLoss data I U e.1 (pool e))
  have hbadsub : E.filter bad ⊆ irregular ∪ exceeds := by
    intro e he
    obtain ⟨heE, heBad⟩ := Finset.mem_filter.mp he
    by_cases hregular : RegularEntry data I U e.1
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨heE, hregular⟩, ?_⟩
      exact heBad.resolve_left (not_not.mpr hregular)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨heE, hregular⟩))
  have hbadnat : (E.filter bad).card ≤ irregular.card + exceeds.card :=
    (Finset.card_le_card hbadsub).trans (Finset.card_union_le _ _)
  have hirregular : (irregular.card : ℝ) ≤ γ * Fintype.card F :=
    (card_irregularEntries_le D data hdata I U E hm).trans hcutoff
  have hexceeds : (exceeds.card : ℝ) < γ * Fintype.card F := Nat.lt_ceil.mp hfew
  have hbad : ((E.filter bad).card : ℝ) ≤ 2 * γ * Fintype.card F := by
    have hbadreal : ((E.filter bad).card : ℝ) ≤
        (irregular.card : ℝ) + exceeds.card := by exact_mod_cast hbadnat
    linarith
  have hloss := chunk_mass_loss_le_entryLoss data I U E pool
  refine mass_after_chunk_ge E bad (fun e => entryLoss data I U e.1 (pool e))
    (frozenMass I U) (frozenMass I (chunkFeasibleSet data U E pool))
    I.card (Fintype.card F) (equationBound D) α γ ?_ hm.le ?_ ?_ hγ
    hhalf hsize hbad ?_ ?_ ?_
  · exact Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  · exact_mod_cast Fintype.card_pos
  · unfold equationBound
    positivity
  · intro e he hgood
    exact le_of_not_gt (fun hgt => hgood (Or.inr hgt))
  · intro e he hbad
    exact entryLoss_le D data hdata I U e.1 (pool e)
  · linarith

theorem prob_chunk_recurrence_failure_le (D : ℕ) (hD : 1 ≤ D) (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) (α γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hhalf : equationBound D * α = 1 / 2)
    (hsize : (E.card : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F) :
    (FiniteLaw.pi (fun _ : Position n K => FiniteLaw.uniform (Point F))).prob
      (fun pool => frozenMass I (chunkFeasibleSet data U E pool) <
        frozenMass I U / 2 - (α + 2 * equationBound D) * γ *
          ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ E.card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  refine (FiniteLaw.prob_mono _ ?_).trans
    (prob_many_regular_exceedances_le D hD data hdata I U E γ hm hγ hlarge)
  intro pool hfailure
  by_contra hnot
  have hfew := Nat.lt_of_not_ge hnot
  have hgood := chunk_recurrence_of_few_regular_exceedances D data hdata I U E pool
    α γ hm hγ.le hhalf hsize hcutoff hfew
  exact (not_lt_of_ge hgood) hfailure

end RyserCoveringCounterexample.Selection

end

end OAI
