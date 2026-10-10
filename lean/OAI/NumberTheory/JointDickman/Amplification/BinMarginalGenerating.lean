import OAI.NumberTheory.JointDickman.Amplification.BinStateLimit

namespace OAI

/-! # High-bin marginal as an explicit generating value -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def highBinZeroWeight (J k : ℕ) (i : Fin (J-1)) : ℝ :=
  if k ≤ i.val+1 then 0 else 1

theorem highBinZeroWeight_mem (J k : ℕ) (i : Fin (J-1)) :
    highBinZeroWeight J k i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold highBinZeroWeight
  split_ifs <;> norm_num

theorem highBinZeroWeight_product (J k : ℕ) (r : BinCountState J) :
    (∏ i, highBinZeroWeight J k i ^ (r i).val) =
      if ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0 then 1 else 0 := by
  classical
  by_cases hr : ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0
  · rw [ite_eq_left hr]
    apply prod_eq_one
    intro i _
    unfold highBinZeroWeight
    split_ifs with hi
    · rw [hr i hi]
      simp
    · simp
  · rw [ite_eq_right hr]
    push Not at hr
    obtain ⟨i, hi, hri⟩ := hr
    apply prod_eq_zero (mem_univ i)
    have hval : (r i).val ≠ 0 := by
      intro he
      apply hri
      exact Fin.ext he
    simp [highBinZeroWeight, hi, hval]

theorem highBinMarginal_eq_generating {J : ℕ} (hJ : 2 ≤ J)
    (ν : BinCountState J → ℝ)
    (hν : ∀ r, Tendsto (fun x => binStateDensity J 1 x r) atTop (𝓝 (ν r)))
    (k : ℕ) :
    (∑ r with ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0, ν r) =
      binGeneratingLimit J (highBinZeroWeight J k) := by
  classical
  have ht := tendsto_finsetSum univ (fun r _ =>
    (hν r).mul_const (∏ i, highBinZeroWeight J k i^(r i).val))
  have hg := binStateGeneratingAverage_tendsto hJ (highBinZeroWeight J k)
    (highBinZeroWeight_mem J k) zero_lt_one
  rw [show (fun x => binStateGeneratingAverage J (highBinZeroWeight J k) 1 x) =
      (fun x => ∑ r : BinCountState J,
        binStateDensity J 1 x r * ∏ i, highBinZeroWeight J k i ^ (r i).val) by
    funext x; exact binStateGeneratingAverage_states _ _ _ _] at hg
  have he := tendsto_nhds_unique ht hg
  rw [← he]
  simp only [highBinZeroWeight_product, mul_ite, mul_one, mul_zero]
  exact sum_filter _ _

end JointDickman

end OAI
