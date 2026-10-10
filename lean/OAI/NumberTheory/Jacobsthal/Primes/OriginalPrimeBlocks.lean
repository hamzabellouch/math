import OAI.NumberTheory.Jacobsthal.Partitions.CommonSliceGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosLargeHeightBlocks


noncomputable def blockPrimes (C0 : ℤ) (R xi : ℝ) (H i : ℕ) : Finset ℕ :=
  ErdosTagSubbins.subbin R xi (blockCount C0 R xi H) i

theorem mem_blockPrimes (C0 : ℤ) (R xi : ℝ) (H i p : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) :
    p ∈ blockPrimes C0 R xi H i ↔ p.Prime ∧
      blockLeft C0 R xi H i < (p : ℝ) ∧ (p : ℝ) ≤ blockRight C0 R xi H i :=
  ErdosTagSubbins.mem_subbin hR hxi (blockCount_pos C0 R xi H)

theorem block_partition (C0 : ℤ) (R xi : ℝ) (H : ℕ) (hR : 0 < R) (hxi : 0 < xi) :
    (Finset.univ : Finset (Fin (blockCount C0 R xi H))).biUnion
      (fun i => blockPrimes C0 R xi H i) = ErdosInversePrimeBin.primeBin R xi :=
  ErdosTagSubbins.finite_partition hR hxi (blockCount_pos C0 R xi H)

theorem block_pairwise_disjoint (C0 : ℤ) (R xi : ℝ) (H : ℕ) (hR : 0 < R) (hxi : 0 < xi) :
    Pairwise (fun i j : Fin (blockCount C0 R xi H) =>
      Disjoint (blockPrimes C0 R xi H i) (blockPrimes C0 R xi H j)) :=
  ErdosTagSubbins.subbins_pairwise_disjoint hR hxi (blockCount_pos C0 R xi H)

theorem unique_original_prime_block (C0 : ℤ) (R xi : ℝ) (H p : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hp : p ∈ ErdosInversePrimeBin.primeBin R xi) :
    ∃! i : Fin (blockCount C0 R xi H), p ∈ blockPrimes C0 R xi H i :=
  ErdosTagSubbins.unique_prime_subbin hR hxi (blockCount_pos C0 R xi H) hp

theorem original_prime_sum {B : Type*} [AddCommMonoid B]
    (C0 : ℤ) (R xi : ℝ) (H : ℕ) (hR : 0 < R) (hxi : 0 < xi) (f : ℕ → B) :
    (∑ p ∈ ErdosInversePrimeBin.primeBin R xi, f p) =
      ∑ i : Fin (blockCount C0 R xi H), ∑ p ∈ blockPrimes C0 R xi H i, f p :=
  ErdosTagSubbins.sum_partition hR hxi (blockCount_pos C0 R xi H) f

theorem block_width_sum (C0 : ℤ) (R xi : ℝ) (H : ℕ) :
    (∑ i : Fin (blockCount C0 R xi H),
      (blockRight C0 R xi H i-blockLeft C0 R xi H i)) = xi*R := by
  simp only [blockRight,blockLeft,ErdosTagSubbins.right_sub_left,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [ErdosTagSubbins.total_step (blockCount_pos C0 R xi H)]
  ring

theorem last_block_endpoint (C0 : ℤ) (R xi : ℝ) (H : ℕ) :
    blockRight C0 R xi H (blockCount C0 R xi H-1) = (1+xi)*R := by
  have hn : 1 ≤ blockCount C0 R xi H := blockCount_pos C0 R xi H
  rw [blockRight,ErdosTagSubbins.right,Nat.sub_add_cancel hn,
    ErdosTagSubbins.total_step (blockCount_pos C0 R xi H)]
  ring

theorem final_upper_endpoint_included (C0 : ℤ) (R xi : ℝ) (H p : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hp : p.Prime) (he : (p : ℝ)=(1+xi)*R) :
    p ∈ blockPrimes C0 R xi H (blockCount C0 R xi H-1) := by
  apply ErdosTagSubbins.upper_endpoint_included hR hxi (blockCount_pos C0 R xi H) hp
  exact he.trans (last_block_endpoint C0 R xi H).symm

end ErdosLargeHeightBlocks


end Erdos970

end OAI
