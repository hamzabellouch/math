import OAI.Combinatorics.DiscreteConvexity.Basic
import OAI.Combinatorics.DiscreteConvexity.DyadicBins
import OAI.Combinatorics.DiscreteConvexity.FiniteFibers
import OAI.Combinatorics.DiscreteConvexity.BinNumerics

namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The generators whose weights pay directly for their cost. -/
noncomputable def largeWeightFamily (W : Finset α → ℝ) : Family α := by
  classical
  exact Finset.univ.filter fun U => U ≠ ∅ ∧ (1 / 2 : ℝ) ^ (64 * U.card) ≤ W U

/-- The remaining nonzero weights; this finite family is partitioned into bins. -/
noncomputable def smallWeightFamily (W : Finset α → ℝ) : Family α := by
  classical
  exact Finset.univ.filter fun U =>
    U ≠ ∅ ∧ 0 < W U ∧ W U < (1 / 2 : ℝ) ^ (64 * U.card)

noncomputable def weightBinKey (W : Finset α → ℝ) (U : Finset α) : ℕ × ℕ :=
  (U.card, binExponent (W U))

noncomputable def occupiedWeightBins (W : Finset α → ℝ) : Finset (ℕ × ℕ) :=
  FiniteFibers.keys (smallWeightFamily W) (weightBinKey W)

noncomputable def weightBin (W : Finset α → ℝ) (b : ℕ × ℕ) : Family α :=
  FiniteFibers.fiber (smallWeightFamily W) (weightBinKey W) b

@[simp] theorem mem_largeWeightFamily {W : Finset α → ℝ} {U : Finset α} :
    U ∈ largeWeightFamily W ↔
      U ≠ ∅ ∧ (1 / 2 : ℝ) ^ (64 * U.card) ≤ W U := by
  classical
  simp [largeWeightFamily]

@[simp] theorem mem_smallWeightFamily {W : Finset α → ℝ} {U : Finset α} :
    U ∈ smallWeightFamily W ↔
      U ≠ ∅ ∧ 0 < W U ∧ W U < (1 / 2 : ℝ) ^ (64 * U.card) := by
  classical
  simp [smallWeightFamily]

theorem mem_weightBin {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ} :
    U ∈ weightBin W b ↔ U ∈ smallWeightFamily W ∧ weightBinKey W U = b := by
  classical
  simp [weightBin, FiniteFibers.fiber]

theorem weightBin_card {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ}
    (hU : U ∈ weightBin W b) : U.card = b.1 := by
  exact congrArg Prod.fst (mem_weightBin.mp hU).2

theorem weightBin_bounds {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ}
    (hU : U ∈ weightBin W b) :
    (1 / 2 : ℝ) ^ (b.2 + 1) < W U ∧ W U ≤ (1 / 2 : ℝ) ^ b.2 := by
  have hmem := mem_weightBin.mp hU
  have hw := mem_smallWeightFamily.mp hmem.1
  have hle : W U ≤ 1 := hw.2.2.le.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hbin := binExponent_spec hw.2.1 hle
  have he : binExponent (W U) = b.2 := congrArg Prod.snd hmem.2
  simpa only [he] using hbin

theorem occupiedWeightBins_bounds {W : Finset α → ℝ} {b : ℕ × ℕ}
    (hb : b ∈ occupiedWeightBins W) : 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2 := by
  classical
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hb
  have hw := mem_smallWeightFamily.mp hU
  exact ⟨Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hw.1),
    le_binExponent_of_lt_pow hw.2.1 hw.2.2⟩

omit [DecidableEq α] in
theorem subfamily_weight_sum_le {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 ≤ q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) (A : Family α) :
    (∑ U ∈ A, q ^ U.card * W U) ≤ 1 := by
  exact (Finset.sum_le_univ_sum_of_nonneg
    (fun U => mul_nonneg (pow_nonneg hq _) (hW U))).trans hglobal

/-- Each occupied bin satisfies the size hypothesis of the covering lemma. -/
theorem weightBin_cost_bound {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 < q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) (b : ℕ × ℕ) :
    ((weightBin W b).card : ℝ) * (q / (2 : ℝ) ^ 70) ^ b.1 ≤
      (2 : ℝ) ^ (b.2 + 1) := by
  have hlo : ((weightBin W b).card : ℝ) * q ^ b.1 *
      (1 / 2 : ℝ) ^ (b.2 + 1) ≤ 1 := by
    calc
      _ = ∑ U ∈ weightBin W b, q ^ b.1 * (1 / 2 : ℝ) ^ (b.2 + 1) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ∑ U ∈ weightBin W b, q ^ U.card * W U := by
        apply Finset.sum_le_sum
        intro U hU
        rw [weightBin_card hU]
        exact mul_le_mul_of_nonneg_left (weightBin_bounds hU).1.le (pow_nonneg hq.le _)
      _ ≤ 1 := subfamily_weight_sum_le hq.le hW hglobal _
  exact bin_card_cost_bound hq hlo

/-- All large weights together have cost at most one sixty-fourth. -/
theorem largeWeightFamily_cost_le {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 ≤ q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) :
    cost (q / (2 : ℝ) ^ 70) (largeWeightFamily W) ≤ 1 / 64 := by
  calc
    _ ≤ ∑ U ∈ largeWeightFamily W, (1 / 64 : ℝ) * (q ^ U.card * W U) := by
      apply Finset.sum_le_sum
      intro U hU
      have hw := mem_largeWeightFamily.mp hU
      simpa only [mul_assoc] using outright_weight_le
        (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hw.1)) hq hw.2
    _ = (1 / 64 : ℝ) * ∑ U ∈ largeWeightFamily W, q ^ U.card * W U := by
      rw [Finset.mul_sum]
    _ ≤ (1 / 64 : ℝ) * 1 := mul_le_mul_of_nonneg_left
      (subfamily_weight_sum_le hq hW hglobal _) (by norm_num)
    _ = 1 / 64 := by ring

/-- In an uncovered bin, the sixteenth powers have the required geometric bound. -/
theorem weightBin_power_sum_le {W : Finset α → ℝ} (hW : ∀ U, 0 ≤ W U)
    (S : Finset α) (b : ℕ × ℕ)
    (hcount : ((weightBin W b).filter (fun U => U ⊆ S)).card ≤ 2 ^ (12 * b.2)) :
    (∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S), (W U) ^ 16) ≤
      (1 / 2 : ℝ) ^ (4 * b.2) := by
  calc
    _ ≤ ∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S),
        ((1 / 2 : ℝ) ^ b.2) ^ 16 := by
      apply Finset.sum_le_sum
      intro U hU
      exact pow_le_pow_left₀ (hW U) (weightBin_bounds (Finset.mem_filter.mp hU).1).2 _
    _ = (((weightBin W b).filter (fun U => U ⊆ S)).card : ℝ) *
        ((1 / 2 : ℝ) ^ b.2) ^ 16 := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / 2 : ℝ) ^ (4 * b.2) := bin_power_bound hcount

/-- Removing zero weights and partitioning the remainder is a finite identity. -/
theorem subset_power_sum_le_bins {W : Finset α → ℝ} (hW : ∀ U, 0 ≤ W U)
    (S : Finset α) (hlarge : ∀ U ∈ largeWeightFamily W, ¬ U ⊆ S) :
    (∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) ≤
      ∑ b ∈ occupiedWeightBins W,
        ∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S), (W U) ^ 16 := by
  classical
  let A := S.powerset.erase ∅
  have hzero : (∑ U ∈ A, (W U) ^ 16) =
      ∑ U ∈ A.filter (fun U => 0 < W U), (W U) ^ 16 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U hU hnot
    have hn : ¬ 0 < W U := fun h => hnot (Finset.mem_filter.mpr ⟨hU, h⟩)
    have hz : W U = 0 := le_antisymm (le_of_not_gt hn) (hW U)
    simp [hz]
  have hsub : A.filter (fun U => 0 < W U) ⊆
      (smallWeightFamily W).filter (fun U => U ⊆ S) := by
    intro U hU
    obtain ⟨hUA, hpos⟩ := Finset.mem_filter.mp hU
    obtain ⟨hne, hUS⟩ := Finset.mem_erase.mp hUA
    have hsubset : U ⊆ S := Finset.mem_powerset.mp hUS
    refine Finset.mem_filter.mpr ⟨mem_smallWeightFamily.mpr ⟨hne, hpos, ?_⟩, hsubset⟩
    by_contra hlt
    exact hlarge U (mem_largeWeightFamily.mpr ⟨hne, le_of_not_gt hlt⟩) hsubset
  calc
    _ = ∑ U ∈ A.filter (fun U => 0 < W U), (W U) ^ 16 := hzero
    _ ≤ ∑ U ∈ (smallWeightFamily W).filter (fun U => U ⊆ S), (W U) ^ 16 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun U _ _ => pow_nonneg (hW U) _)
    _ = _ := FiniteFibers.sum_filter_eq_sum_fibers _ _ _ _

end TalagrandDiscreteConvexity

end OAI
