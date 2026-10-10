import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Coverage by full blocks containing a heavy position

The `b`th full block consists literally of positions `b * h + z`, for `z < h`.
Every full block that is not used consists of light positions. Counting the
disjoint full blocks and the final remainder transfers bounds within used
blocks to counts in the entire interval.
-/

open scoped BigOperators

namespace QuantitativeVanDerWaerden.BlockCoverage

/-- Position `z` in full block `b`. -/
def blockIndex (k h : ℕ) (b : Fin (k / h)) (z : Fin h) : Fin k :=
  ⟨b.val * h + z.val, by
    calc
      b.val * h + z.val < b.val * h + h := Nat.add_lt_add_left z.isLt _
      _ = b.val.succ * h := (Nat.succ_mul _ _).symm
      _ ≤ (k / h) * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt b.isLt)
      _ ≤ k := Nat.div_mul_le_self k h⟩

@[simp]
theorem blockIndex_val (k h : ℕ) (b : Fin (k / h)) (z : Fin h) :
    (blockIndex k h b z).val = b.val * h + z.val := rfl

theorem blockIndex_div (k h : ℕ) (hh : 0 < h)
    (b : Fin (k / h)) (z : Fin h) :
    (blockIndex k h b z).val / h = b.val := by
  change (b.val * h + z.val) / h = b.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hh,
    Nat.div_eq_of_lt z.isLt, Nat.zero_add]

theorem blockIndex_injective (k h : ℕ) (b : Fin (k / h)) :
    Function.Injective (blockIndex k h b) := by
  intro z w heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  exact Nat.add_left_cancel hv

def blockPositions (k h : ℕ) (b : Fin (k / h)) : Finset (Fin k) :=
  Finset.univ.image (blockIndex k h b)

@[simp]
theorem card_blockPositions (k h : ℕ) (b : Fin (k / h)) :
    (blockPositions k h b).card = h := by
  rw [blockPositions, Finset.card_image_of_injective _ (blockIndex_injective k h b)]
  simp

theorem blockPositions_disjoint (k h : ℕ) (hh : 0 < h)
    {b c : Fin (k / h)} (hbc : b ≠ c) :
    Disjoint (blockPositions k h b) (blockPositions k h c) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp hq
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hp
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hq
  have hv := congrArg (fun p : Fin k => p.val / h) (hz.trans hw.symm)
  change (blockIndex k h b z).val / h = (blockIndex k h c w).val / h at hv
  rw [blockIndex_div k h hh, blockIndex_div k h hh] at hv
  exact hbc (Fin.ext hv)

def blockUnion (k h : ℕ) (B : Finset (Fin (k / h))) : Finset (Fin k) :=
  B.biUnion (blockPositions k h)

theorem blockUnion_mono (k h : ℕ) {B C : Finset (Fin (k / h))} (hBC : B ⊆ C) :
    blockUnion k h B ⊆ blockUnion k h C := by
  intro p hp
  obtain ⟨b, hb, hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨b, hBC hb, hp⟩

theorem card_blockUnion (k h : ℕ) (hh : 0 < h) (B : Finset (Fin (k / h))) :
    (blockUnion k h B).card = B.card * h := by
  unfold blockUnion
  rw [Finset.card_biUnion (fun b _ c _ hbc => blockPositions_disjoint k h hh hbc)]
  exact Finset.sum_const_nat fun b _ => card_blockPositions k h b

def usedBlocks (k h : ℕ) (heavy : Fin k → Prop) [DecidablePred heavy] :
    Finset (Fin (k / h)) :=
  Finset.univ.filter fun b => ∃ z : Fin h, heavy (blockIndex k h b z)

@[simp]
theorem mem_usedBlocks (k h : ℕ) (heavy : Fin k → Prop) [DecidablePred heavy]
    (b : Fin (k / h)) :
    b ∈ usedBlocks k h heavy ↔ ∃ z : Fin h, heavy (blockIndex k h b z) := by
  simp [usedBlocks]

def lightPositions {k : ℕ} (heavy : Fin k → Prop) [DecidablePred heavy] :
    Finset (Fin k) :=
  Finset.univ.filter fun p => ¬ heavy p

def lightCount {k : ℕ} (heavy : Fin k → Prop) [DecidablePred heavy] : ℕ :=
  (lightPositions heavy).card

/-- Every full-block position not covered by a used block is light. -/
theorem unused_full_positions_light (k h : ℕ) (heavy : Fin k → Prop)
    [DecidablePred heavy] :
    blockUnion k h Finset.univ \ blockUnion k h (usedBlocks k h heavy) ⊆
      lightPositions heavy := by
  intro p hp
  obtain ⟨hfull, hnot⟩ := Finset.mem_sdiff.mp hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hpheavy
  obtain ⟨b, _, hpb⟩ := Finset.mem_biUnion.mp hfull
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hpb
  have hb : b ∈ usedBlocks k h heavy := by
    apply (mem_usedBlocks k h heavy b).mpr
    refine ⟨z, ?_⟩
    rw [hz]
    exact hpheavy
  exact hnot (Finset.mem_biUnion.mpr ⟨b, hb, hpb⟩)

theorem full_positions_le_light_add_used (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy] :
    (k / h) * h ≤ lightCount heavy + (usedBlocks k h heavy).card * h := by
  have hsub := blockUnion_mono k h (Finset.subset_univ (usedBlocks k h heavy))
  have hpart := Finset.card_sdiff_add_card_eq_card hsub
  have hlight := Finset.card_le_card (unused_full_positions_light k h heavy)
  have hfull : (blockUnion k h Finset.univ).card = (k / h) * h := by
    simpa using card_blockUnion k h hh Finset.univ
  have hused := card_blockUnion k h hh (usedBlocks k h heavy)
  unfold lightCount
  omega

/-- The final remainder has fewer than `h` positions, and unused full blocks
are charged to individual light positions. -/
theorem usedBlocks_mul_lower (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy] :
    (k : ℝ) - (h : ℝ) - (lightCount heavy : ℝ) ≤
      ((usedBlocks k h heavy).card : ℝ) * (h : ℝ) := by
  have hfull := full_positions_le_light_add_used k h hh heavy
  have hrem := Nat.mod_lt k hh
  have hdiv := Nat.div_add_mod' k h
  have hn : k ≤ h + lightCount heavy + (usedBlocks k h heavy).card * h := by omega
  have hr : (k : ℝ) ≤ (h : ℝ) + (lightCount heavy : ℝ) +
      ((usedBlocks k h heavy).card : ℝ) * (h : ℝ) := by exact_mod_cast hn
  linarith

theorem usedPositions_lower (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy] :
    (k : ℝ) - (h : ℝ) - (lightCount heavy : ℝ) ≤
      ((blockUnion k h (usedBlocks k h heavy)).card : ℝ) := by
  rw [card_blockUnion k h hh, Nat.cast_mul]
  exact usedBlocks_mul_lower k h hh heavy

def blockColorCount (k h : ℕ) (color : Fin k → Bool) (c : Bool)
    (b : Fin (k / h)) : ℕ :=
  ((blockPositions k h b).filter fun p => color p = c).card

def colorCount {k : ℕ} (color : Fin k → Bool) (c : Bool) : ℕ :=
  (Finset.univ.filter fun p => color p = c).card

/-- Counts in any collection of distinct full blocks sum to at most the
corresponding count in the whole interval. -/
theorem sum_blockColorCount_le (k h : ℕ) (hh : 0 < h)
    (B : Finset (Fin (k / h))) (color : Fin k → Bool) (c : Bool) :
    (∑ b ∈ B, blockColorCount k h color c b) ≤ colorCount color c := by
  let sets := fun b => (blockPositions k h b).filter fun p => color p = c
  have hdisj : (B : Set (Fin (k / h))).PairwiseDisjoint sets := by
    intro b _ d _ hbd
    exact (blockPositions_disjoint k h hh hbd).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsub : B.biUnion sets ⊆ Finset.univ.filter (fun p => color p = c) := by
    intro p hp
    obtain ⟨b, _, hp⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  exact hcard

/-- If every used full block contains at least `h/8` positions of a specified
color, that color occupies at least `(k-h-lightCount)/8` positions globally. -/
theorem colorCount_lower (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy]
    (color : Fin k → Bool) (c : Bool)
    (hblocks : ∀ b ∈ usedBlocks k h heavy,
      (h : ℝ) / 8 ≤ (blockColorCount k h color c b : ℝ)) :
    ((k : ℝ) - (h : ℝ) - (lightCount heavy : ℝ)) / 8 ≤
      (colorCount color c : ℝ) := by
  have hsum : ((usedBlocks k h heavy).card : ℝ) * ((h : ℝ) / 8) ≤
      ∑ b ∈ usedBlocks k h heavy, (blockColorCount k h color c b : ℝ) := by
    calc
      _ = ∑ _b ∈ usedBlocks k h heavy, (h : ℝ) / 8 := by simp
      _ ≤ _ := Finset.sum_le_sum hblocks
  have hupper : (∑ b ∈ usedBlocks k h heavy, (blockColorCount k h color c b : ℝ)) ≤
      (colorCount color c : ℝ) := by
    exact_mod_cast sum_blockColorCount_le k h hh (usedBlocks k h heavy) color c
  have hcoverage := usedBlocks_mul_lower k h hh heavy
  linarith

/-- The one-tenth light-position and block-size bounds give the desired
one-tenth global count for each color. -/
theorem colorCount_tenth (k h : ℕ) (hh : 0 < h)
    (heavy : Fin k → Prop) [DecidablePred heavy]
    (color : Fin k → Bool)
    (hlight : (lightCount heavy : ℝ) ≤ (k : ℝ) / 10)
    (hsmall : (h : ℝ) ≤ (k : ℝ) / 10)
    (hblocks : ∀ b ∈ usedBlocks k h heavy, ∀ c : Bool,
      (h : ℝ) / 8 ≤ (blockColorCount k h color c b : ℝ)) :
    ∀ c : Bool, (k : ℝ) / 10 ≤ (colorCount color c : ℝ) := by
  intro c
  have hglobal := colorCount_lower k h hh heavy color c (fun b hb => hblocks b hb c)
  linarith

end QuantitativeVanDerWaerden.BlockCoverage

end OAI
