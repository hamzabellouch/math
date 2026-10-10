import OAI.Combinatorics.Crossing.RankDetector

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem detectorAtom_entry_split (s : ℕ) (node : ι → ℝ) (p q : ι) (ab cd : BiExponent s) :
    detectorAtom s node p q ab cd =
      (node p^(ab.1.val+cd.1.val+1) / derivativeAtNode node p) *
        (node q^(ab.2.val+cd.2.val) / derivativeAtNode node q) -
      (node p^(ab.1.val+cd.1.val) / derivativeAtNode node p) *
        (node q^(ab.2.val+cd.2.val+1) / derivativeAtNode node q) := by
  rw [detectorAtom_entry]
  simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

theorem detectorAtom_row_sum (s : ℕ) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) (p : ι) : ∑ q, detectorAtom s node p q = 0 := by
  funext ab cd
  simp only [Matrix.sum_apply, Matrix.zero_apply, detectorAtom_entry_split,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hb := ab.2.isLt
  have hd := cd.2.isLt
  rw [node_power_moment node hn _ (by omega), node_power_moment node hn _ (by omega)]
  ring

theorem detectorAtom_column_sum (s : ℕ) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) (q : ι) : ∑ p, detectorAtom s node p q = 0 := by
  funext ab cd
  simp only [Matrix.sum_apply, Matrix.zero_apply, detectorAtom_entry_split,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  have ha := ab.1.isLt
  have hc := cd.1.isLt
  rw [node_power_moment node hn _ (by omega), node_power_moment node hn _ (by omega)]
  ring

theorem rankDetector_additive (s : ℕ) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) (r c : ι → ℝ) :
    rankDetector s node (fun p q => r p+c q) = 0 := by
  change (∑ p, ∑ q, (r p+c q) • detectorAtom s node p q) = 0
  simp only [add_smul, Finset.sum_add_distrib]
  have hr : (∑ p, ∑ q, r p • detectorAtom s node p q) = 0 := by
    simp only [← Finset.smul_sum, detectorAtom_row_sum s node hn hcard, smul_zero, Finset.sum_const_zero]
  have hc : (∑ p, ∑ q, c q • detectorAtom s node p q) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, detectorAtom_column_sum s node hn hcard, smul_zero,
      Finset.sum_const_zero]
  rw [hr, hc, add_zero]

end Zarankiewicz

end

end OAI
