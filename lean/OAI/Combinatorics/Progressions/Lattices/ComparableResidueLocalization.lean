import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxPartition

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_comparable_residue_piece {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N H : I → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (r s v w : I → ℤ) (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    {ε : ℝ} (hε : ε < 1 / 2)
    (hsmallR : (∑ i, (r i : ℝ) / (H i : ℝ)) ≤ ε)
    (hsmallS : (∑ i, (s i : ℝ) / (H i : ℝ)) ≤ ε)
    (f : IntegerResidueBox a (fun i => a i + N i) r v → ℂ)
    (g : IntegerResidueBox a (fun i => a i + N i) s w → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) :
    let P := comparableBoxPartitions N H hH hHN
    ∃ k : (∀ i, (P i).Label),
      0 < (partitionCell (boxIntervalResidueCell a N P r v) k).card ∧
      0 < (partitionCell (boxIntervalResidueCell a N P s w) k).card ∧
      ‖(𝔼 x, f x) - (𝔼 x, g x)‖ - 8 * ε ≤
        ‖(𝔼 x ∈ partitionCell (boxIntervalResidueCell a N P r v) k, f x) -
          (𝔼 x ∈ partitionCell (boxIntervalResidueCell a N P s w) k, g x)‖ := by
  intro P
  let := comparableBoxPartitions_nonempty N H hH hHN
  have hstep : ∀ i k, (P i).step k = 1 := comparableBoxPartitions_step N H hH hHN
  have hpos : ∀ i k, 0 < (P i).length k := fun i k =>
    (hH i).trans_le (comparableBoxPartitions_length N H hH hHN i k).1
  let lo : (∀ i, (P i).Label) → I → ℤ := fun k i => intervalCellLower (a i) (P i) (k i)
  let hi : (∀ i, (P i).Label) → I → ℤ := fun k i => intervalCellUpper (a i) (P i) (k i)
  have hbox : ∀ k i, lo k i < hi k i := by
    intro k i
    apply sub_pos.mp
    change 0 < intervalCellUpper (a i) (P i) (k i) - intervalCellLower (a i) (P i) (k i)
    rw [intervalCell_width]
    exact_mod_cast hpos i (k i)
  have hR : ∀ k, (∑ i, (r i : ℝ) / ((hi k i - lo k i : ℤ) : ℝ)) ≤ ε :=
    fun k => (comparableBoxPartitions_ratio_le a N H hH hHN r (fun i => (hr i).le) k).trans hsmallR
  have hS : ∀ k, (∑ i, (s i : ℝ) / ((hi k i - lo k i : ℤ) : ℝ)) ≤ ε :=
    fun k => (comparableBoxPartitions_ratio_le a N H hH hHN s (fun i => (hs i).le) k).trans hsmallS
  let F : (∀ i, (P i).Label) → ℂ := fun k =>
    𝔼 x ∈ partitionCell (boxIntervalResidueCell a N P r v) k, f x
  let G : (∀ i, (P i).Label) → ℂ := fun k =>
    𝔼 x ∈ partitionCell (boxIntervalResidueCell a N P s w) k, g x
  have hG : ∀ k, ‖G k‖ ≤ 1 := by
    intro k
    let S := partitionCell (boxIntervalResidueCell a N P s w) k
    change ‖𝔼 x ∈ S, g x‖ ≤ 1
    by_cases hS : S.Nonempty
    · apply (RCLike.norm_expect_le (K := ℂ)).trans
      exact (Finset.expect_le_expect (fun x _ => hg x)).trans_eq (Finset.expect_const hS 1)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hS
      simp only [he, Finset.expect_empty, norm_zero, zero_le_one]
  obtain ⟨k, hkr, hks, hgap⟩ := exists_rectangular_residue_piece_discrepancy
    lo hi r s (fun _ => v) (fun _ => w) hbox hr hs hε hR hS F G hG
  have hmR := boxIntervalResidue_mixture a N P hstep hpos r v f
  have hmS := boxIntervalResidue_mixture a N P hstep hpos s w g
  simp only [div_mul_eq_mul_div, ← Finset.sum_div] at hmR hmS
  rw [← hmR, ← hmS] at hgap
  refine ⟨k, ?_, ?_, hgap⟩
  · rw [boxIntervalResidueCell_card a N P hstep hpos r v]
    exact Nat.cast_pos.mp hkr
  · rw [boxIntervalResidueCell_card a N P hstep hpos s w]
    exact Nat.cast_pos.mp hks

end Erdos3

end

end OAI
