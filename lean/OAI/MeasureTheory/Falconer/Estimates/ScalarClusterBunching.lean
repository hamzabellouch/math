import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterPathTree

namespace OAI

/-! Bunching preserves the whole terminal fiber, including its mass. -/
namespace Falconer.Regularization

 theorem scalar_cluster_bunch_pruning {N M T lo m : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain T lo bs) (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k n : ℕ → ℕ)
    (hd : Monotone d) (hdN : ∀ i ≤ M, d i ≤ N)
    (hleaf : ∀ p ∈ L.image (List.take (d M)), (prefixFiber L (d M) p).card = m)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T = M) :
    ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
      L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        scalarCompressedBranch e k i)).sum)*Q.card ∧
      (∀ c ≤ d (e lo), Q.image (List.take c) = L.image (List.take c)) ∧
      (∀ p ∈ Q.image (List.take (d (e T))), (prefixFiber Q (d (e T)) p).card = m) ∧
      (∀ b ∈ bs, ScalarPathLevel Q (d (e b.start)) (d (e b.stop))
        (2^(∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i))
        (4*(1/2:ℝ)^(n (e b.cut-1)))) := by
  classical
  have heT' : e T ≤ M := heT.le
  have hcard : ∀ i < T, ∀ p ∈ L.image (List.take (d (e i))),
      (prefixChildren L (d (e i)) (d (e (i+1))) p).card = 2^(scalarCompressedBranch e k i) :=
    fun i hi => (scalar_compressed_path_level hL d k n hd hdN hlevel e he heT' hi).card
  have hm : ∀ p ∈ L.image (List.take (d (e T))), (prefixFiber L (d (e T)) p).card = m := by
    simpa only [heT] using hleaf
  have hg : ∀ b ∈ bs, ∀ p ∈ L.image (List.take (d (e b.start))),
      ∀ u ∈ prefixChildren L (d (e b.start)) (d (e b.cut)) p,
      ∀ v ∈ prefixChildren L (d (e b.start)) (d (e b.cut)) p,
      u ≠ v → 6*(1/2:ℝ)^(n (e b.cut-1)) ≤ |scalarPathCenter u-scalarPathCenter v| := by
    intro b hb
    have hbound := hchain.mem_bounds b hb
    exact scalar_compressed_group_separated hL d k n hd hdN hlevel e he heT'
      b.start_lt_cut (b.cut_le_stop.trans hbound.2)
  obtain ⟨Q,hQL,hQne,hsize,hprefix,hfiber,hlevels⟩ := scalar_trim_bunch_chain hchain
    (fun j => d (e j)) (scalarCompressedBranch e k) (hd.comp he.monotone)
    (fun b => 6*(1/2:ℝ)^(n (e b.cut-1))) L m hL hne
    (by rw [heT]; exact hdN M le_rfl) hcard hm hg
  refine ⟨Q,hQL,hQne,hsize,hprefix,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [hfiber _ le_rfl q hq]
    exact hm _ (Finset.mem_image_of_mem _ (hQL hq))
  intro b hb
  apply (hlevels b hb).mono_gap
  have hpos : 0 < e b.cut := (Nat.zero_le (e b.start)).trans_lt (he b.start_lt_cut)
  have hbound := hchain.mem_bounds b hb
  have hecut : e b.cut ≤ M := (he.monotone (b.cut_le_stop.trans hbound.2)).trans heT'
  have hx := (hlevel (e b.cut-1) (by omega)).level_hi
  rw [Nat.sub_add_cancel hpos] at hx
  have hs : (1/2:ℝ)^(d (e b.cut)) ≤ (1/2:ℝ)^(n (e b.cut-1)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hx
  change 4*(1/2:ℝ)^(n (e b.cut-1)) ≤
    6*(1/2:ℝ)^(n (e b.cut-1))-2*(1/2:ℝ)^(d (e b.cut))
  linarith


end Falconer.Regularization

end OAI
