import OAI.NumberTheory.JointDickman.Arithmetic.BrunPrimeBlocks
import OAI.NumberTheory.JointDickman.Arithmetic.BrunGeometric

namespace OAI

/-! # Every truncated block choice has product below the sifting bound -/
namespace JointDickman
open Finset

 theorem brunPrimeBlocks_cutoff (P : Finset ℕ) {L z : ℝ} (hL : 0 ≤ L)
    (hscale : 8*L ≤ Real.log z) (hz : 0 < z) (hp : ∀ p ∈ P, 0 < (p:ℝ)) (N : ℕ)
    (D : Fin N → Finset ℕ)
    (hD : D ∈ brunBlockChoices (fun j : Fin N => brunPrimeBlock P L j.val) (fun j => j.val+1)) :
    (∏ p ∈ brunBlockUnion D, p : ℕ) ≤ z := by
  classical
  have hchoice := (brunBlockChoices_mem _ _ D).mp hD
  have hd : (↑(univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint D := by
    intro i _ j _ hij
    exact (brunPrimeBlocks_disjoint P hL N hij).mono (hchoice i).1 (hchoice j).1
  have hDP (p : ℕ) (hpu : p ∈ brunBlockUnion D) : p ∈ P := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hpu
    exact brunPrimeBlock_subset P L i.val ((hchoice i).1 hi)
  have hpos : 0 < (∏ p ∈ brunBlockUnion D, (p:ℝ)) := prod_pos (fun p hpu => hp p (hDP p hpu))
  have heq : ((∏ p ∈ brunBlockUnion D, p : ℕ):ℝ) = ∏ p ∈ brunBlockUnion D, (p:ℝ) := by simp only [Nat.cast_prod]
  rw [heq]
  apply (Real.log_le_log_iff hpos hz).mp
  calc
    _ = ∑ i : Fin N, ∑ p ∈ D i, Real.log p := by
      rw [Real.log_prod (fun p hpu => (hp p (hDP p hpu)).ne'),brunBlockUnion,sum_biUnion hd]
    _ ≤ ∑ i : Fin N, (2*((i.val:ℝ)+1))*(L/(2:ℝ)^i.val) := by
      apply sum_le_sum
      intro i _
      calc
        _ ≤ ∑ _p ∈ D i, L/(2:ℝ)^i.val := by
          apply sum_le_sum
          intro p hpi
          exact (mem_filter.mp ((hchoice i).1 hpi)).2.2
        _ = (D i).card*(L/(2:ℝ)^i.val) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (hchoice i).2) (by positivity)
    _ = 2*L*(∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (2*((i:ℝ)+1))*(L/(2:ℝ)^i)) N,mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ 2*L*4 := mul_le_mul_of_nonneg_left (brun_weighted_geometric_le N) (by positivity)
    _ ≤ Real.log z := by linarith

end JointDickman

end OAI
