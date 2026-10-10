import OAI.MeasureTheory.Falconer.Estimates.ScalarCompressedLevels

namespace OAI

/-! Realizing a bunching ledger after grouping the original regularized
 dyadic levels. The final gap is stated in the original geometric scale. -/
namespace Falconer.Regularization

 theorem ScalarPathLevel.mono_gap {Q : Finset (CellPath 1)} {a b K : ℕ} {g h : ℝ}
    (hp : ScalarPathLevel Q a b K g) (hh : h ≤ g) : ScalarPathLevel Q a b K h :=
  ⟨hp.order,hp.card,fun p hq u hu v hv hne => hh.trans (hp.separated p hq u hu v hv hne)⟩

 theorem scalar_compressed_bunch_pruning_of_leaves {N M T lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain T lo bs) (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k n : ℕ → ℕ)
    (hd : Monotone d) (hdN : ∀ i ≤ M, d i ≤ N)
    (hleaf : ∀ p ∈ L.image (List.take (d M)), (prefixFiber L (d M) p).card = 1)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T = M) :
    ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
      L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        scalarCompressedBranch e k i)).sum)*Q.card ∧
      (∀ c ≤ d (e lo), Q.image (List.take c) = L.image (List.take c)) ∧
      (∀ b ∈ bs, ScalarPathLevel Q (d (e b.start)) (d (e b.stop))
        (2^(∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i))
        (4*(1/2:ℝ)^(n (e b.cut-1)))) := by
  classical
  have heT' : e T ≤ M := heT.le
  have hcard : ∀ i < T, ∀ p ∈ L.image (List.take (d (e i))),
      (prefixChildren L (d (e i)) (d (e (i+1))) p).card = 2^(scalarCompressedBranch e k i) :=
    fun i hi => (scalar_compressed_path_level hL d k n hd hdN hlevel e he heT' hi).card
  have hm : ∀ p ∈ L.image (List.take (d (e T))), (prefixFiber L (d (e T)) p).card = 1 := by
    simpa only [heT] using hleaf
  have hg : ∀ b ∈ bs, ∀ p ∈ L.image (List.take (d (e b.start))),
      ∀ u ∈ prefixChildren L (d (e b.start)) (d (e b.cut)) p,
      ∀ v ∈ prefixChildren L (d (e b.start)) (d (e b.cut)) p,
      u ≠ v → 6*(1/2:ℝ)^(n (e b.cut-1)) ≤ |scalarPathCenter u-scalarPathCenter v| := by
    intro b hb
    have hbound := hchain.mem_bounds b hb
    exact scalar_compressed_group_separated hL d k n hd hdN hlevel e he heT'
      b.start_lt_cut (b.cut_le_stop.trans hbound.2)
  obtain ⟨Q,hQL,hQne,hsize,hprefix,_,hlevels⟩ := scalar_trim_bunch_chain hchain
    (fun j => d (e j)) (scalarCompressedBranch e k) (hd.comp he.monotone)
    (fun b => 6*(1/2:ℝ)^(n (e b.cut-1))) L 1 hL hne
    (by rw [heT]; exact hdN M le_rfl) hcard hm hg
  refine ⟨Q,hQL,hQne,hsize,hprefix,?_⟩
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

 theorem scalar_compressed_bunch_pruning {N M T lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain T lo bs) (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k n : ℕ → ℕ)
    (hd : Monotone d) (hdN : ∀ i ≤ M, d i ≤ N) (hdM : d M = N)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T = M) :
    ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
      L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        scalarCompressedBranch e k i)).sum)*Q.card ∧
      (∀ c ≤ d (e lo), Q.image (List.take c) = L.image (List.take c)) ∧
      (∀ b ∈ bs, ScalarPathLevel Q (d (e b.start)) (d (e b.stop))
        (2^(∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i))
        (4*(1/2:ℝ)^(n (e b.cut-1)))) := by
  apply scalar_compressed_bunch_pruning_of_leaves hchain L hL hne d k n hd hdN _ hlevel e he heT
  rw [hdM]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 1 N q).mp (hL hq)
  have ht : q.take N = q := by rw [← hlen,List.take_length]
  rw [ht,prefixFiber_leaf hL hq]
  simp

end Falconer.Regularization

end OAI
