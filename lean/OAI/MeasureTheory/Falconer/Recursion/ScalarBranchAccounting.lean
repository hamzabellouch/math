import OAI.MeasureTheory.Falconer.Estimates.ScalarActualClusterGain
import OAI.MeasureTheory.Falconer.Estimates.ScalarPrefixEntropy

namespace OAI

/-! Exact exponent accounting from original blocks through compressed
 blocks and the bunch ledger. -/
namespace Falconer

 theorem ScalarBunchChain.nat_weight_partition {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) (w : ℕ → ℕ) :
    (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum =
        ∑ i ∈ Finset.Ico lo top, w i := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hp := Finset.sum_Ico_consecutive w h.start_le (b.start_lt_cut.le.trans b.cut_le_stop)
    have hb := Finset.sum_Ico_consecutive w b.start_lt_cut.le b.cut_le_stop
    simp only [List.map_cons,List.sum_cons]
    omega

 theorem ScalarBunchChain.total_weight {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) (w : ℕ → ℕ) :
    (∑ i ∈ Finset.range top, w i) = (∑ i ∈ Finset.range lo, w i)+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum := by
  have hp := Finset.sum_Ico_consecutive w (Nat.zero_le lo) h.start_le
  have hh := h.nat_weight_partition w
  simp only [Nat.Ico_zero_eq_range] at hp
  omega

namespace Regularization

 theorem scalar_compressed_branch_sum (e k : ℕ → ℕ) (he : Monotone e)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, scalarCompressedBranch e k j) = ∑ i ∈ Finset.Ico (e a) (e b), k i := by
  induction b,hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab,ih]
    exact Finset.sum_Ico_consecutive k (he hab) (he (Nat.le_succ b))

 theorem scalar_uniform_total_card {N M : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k : ℕ → ℕ)
    (hd : Monotone d) (hd0 : d 0 = 0) (hdM : d M = N)
    (hcard : ∀ i < M, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i)) :
    L.card = 2^(∑ i ∈ Finset.range M, k i) := by
  have hh := scalar_uniform_prefix_card L hne d k hd hd0 hcard (le_refl M)
  rw [hdM] at hh
  have hi : L.image (List.take N) = L := by
    calc
      _ = L.image id := Finset.image_congr (by
        intro q hq
        have hn := (mem_cubePaths 1 N q).mp (hL hq)
        change q.take N = q
        rw [← hn,List.take_length])
      _ = _ := Finset.image_id
  rwa [hi] at hh

 theorem scalar_total_branch_decomposition {M T lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain T lo bs) (e k : ℕ → ℕ) (he : Monotone e)
    (he0 : e 0 = 0) (heT : e T ≤ M) :
    (∑ i ∈ Finset.range M, k i) = (∑ i ∈ Finset.Ico (e T) M, k i)+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i)).sum+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, scalarCompressedBranch e k i)).sum+
      (∑ i ∈ Finset.range lo, scalarCompressedBranch e k i) := by
  have hc := scalar_compressed_branch_sum e k he (Nat.zero_le T)
  simp only [he0,Nat.Ico_zero_eq_range] at hc
  have ht := hchain.total_weight (scalarCompressedBranch e k)
  have hp := Finset.sum_Ico_consecutive k (Nat.zero_le (e T)) heT
  simp only [Nat.Ico_zero_eq_range] at hp
  omega

end Regularization
end Falconer

end OAI
