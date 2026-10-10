import OAI.Analysis.LipschitzHilbert.Trees.GeometricBoundaryDepth

namespace OAI

/-! The geometric envelope equals the first angular scale crossing, and hence
controls the shifted differences of the actual boundary argument. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace LipschitzHilbert

theorem geometricBoundaryDepth_eq_crossing {ε q b : ℝ} {r : ℕ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 < b)
    (hbefore : ∀ j < r, b < ε * q ^ j) (hcross : ε * q ^ r ≤ b) :
    geometricBoundaryDepth ε q b = (r : ℝ) := by
  unfold geometricBoundaryDepth
  rw [tsum_eq_sum (s := Finset.range r)]
  · have heq : ∀ j ∈ Finset.range r, geometricBoundaryLayer ε q j b = 1 := by
      intro j hj
      exact indicator_of_mem
        (show b ∈ Ioo 0 (ε * q ^ j) from ⟨hb, hbefore j (Finset.mem_range.mp hj)⟩)
        (fun _ => (1 : ℝ))
    simp only [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · intro j hj
    have hle : ε * q ^ j ≤ b :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq hq1 (by
        simpa only [Finset.mem_range, not_lt] using hj)) hε).trans hcross
    exact indicator_of_notMem (show b ∉ Ioo 0 (ε * q ^ j) from by
      intro hmem
      exact (not_lt_of_ge hle) hmem.2) _

/-- Every positive boundary distance has a finite first crossing scale. The
geometric depth counts exactly the preceding scales. -/
theorem exists_geometricBoundaryDepth_crossing {ε q b : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 < b) :
    ∃ r : ℕ, geometricBoundaryDepth ε q b = (r : ℝ) ∧ ε * q ^ r ≤ b ∧
      ∀ j < r, b < ε * q ^ j := by
  have ht : Filter.Tendsto (fun j : ℕ => ε * q ^ j) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).const_mul ε
  have he : ∃ r : ℕ, ε * q ^ r ≤ b := by
    obtain ⟨r, hr⟩ := (ht.eventually (gt_mem_nhds hb)).exists
    exact ⟨r, hr.le⟩
  let r := Nat.find he
  have hcross : ε * q ^ r ≤ b := Nat.find_spec he
  have hbefore : ∀ j < r, b < ε * q ^ j := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min he hj)
  exact ⟨r, geometricBoundaryDepth_eq_crossing hε hq hq1.le hb hbefore hcross,
    hcross, hbefore⟩

/-- The finite-difference estimate can use the first scale crossing directly,
without losing the number of levels in the path. -/
theorem boundary_loss_le_geometricDepth (a loss : ℕ → ℝ) (k : ℕ) {ε q b B : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 < b)
    (ha : ∀ i, 0 ≤ a i) (hbound : ∀ i, a i ≤ B)
    (hloss : ∀ r : ℕ, ε * q ^ r ≤ b →
      ∀ i < k, loss i ≤ a i - a (i + r)) :
    (∑ i ∈ Finset.range k, loss i) ≤ geometricBoundaryDepth ε q b * B := by
  obtain ⟨r, hr, hcross, _⟩ := exists_geometricBoundaryDepth_crossing hε hq hq1 hb
  rw [hr]
  exact boundary_loss_sum_le a loss k r ha (fun i _ => hbound i) (hloss r hcross)

end LipschitzHilbert

end

end OAI
