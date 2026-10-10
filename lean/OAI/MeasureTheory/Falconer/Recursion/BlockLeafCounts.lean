import OAI.MeasureTheory.Falconer.Recursion.BlockRegularization
import OAI.MeasureTheory.Falconer.Recursion.PrefixCounting

namespace OAI

namespace PlanarFalconer

noncomputable def blockBin (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : ℕ :=
  2 ^ Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card

noncomputable def blockProduct (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : ℕ := ∏ j ∈ Finset.range i, blockBin L F N B j p

theorem blockBin_pos (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : 0 < blockBin L F N B i p := by
  unfold blockBin; positivity

theorem blockProduct_pos (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : 0 < blockProduct L F N B i p := by
  exact Finset.prod_pos (fun j _ => blockBin_pos L F N B j p)

theorem blockBin_le {N : ℕ} {L : Finset CellPath} (hL : L ⊆ dyadicPaths N)
    (F : CellPath → List ℕ) (B i : ℕ) (p : CellPath) :
    blockBin L F N B i p ≤ 4 ^ (blockDepth N B i-blockDepth N B (i+1)) := by
  have hlog := child_bin_le (blockDepth_antitone N B (Nat.le_succ i)) (Nat.sub_le _ _) hL F p
  have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hlog
  simpa only [pow_mul, show (2:ℕ)^2 = 4 by norm_num, blockBin] using hp

theorem blockClass_child_bounds (L : Finset CellPath) (N B : ℕ) (f : CellPath → List ℕ)
    {K i : ℕ} (hi : i < K) (p : CellPath)
    {P : CellPath}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B (i+1)))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockBin L F N B i p ≤ (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ∧
      (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ≤ 2*blockBin L F N B i p := by
  classical
  dsimp only
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  rw [prefixChildren_class_eq L _ _ _ hq]
  have hqL := (Finset.mem_filter.mp hq).1
  have hclass := (Finset.mem_filter.mp hq).2
  unfold blockBin
  rw [block_final_bin_eq L N B f hi hclass.symm]
  have hpos := Finset.card_pos.mpr (labeledChildren_nonempty
    (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) hqL)
  refine ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos), ?_⟩
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
    (labeledChildren L (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) q).card
  simpa only [pow_succ, Nat.mul_comm] using hu.le

theorem blockClass_leaf_count {N : ℕ} {L : Finset CellPath} (hL : L ⊆ dyadicPaths N)
    (B : ℕ) (f : CellPath → List ℕ) (K : ℕ) (p : CellPath)
    {i : ℕ} (hi : i ≤ K) {P : CellPath}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hC : C ⊆ dyadicPaths N := fun q hq => hL (Finset.mem_filter.mp hq).1
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p
  change P ∈ C.image (List.take (blockDepth N B i)) at hP
  induction i generalizing P with
  | zero =>
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hlen : q.length = N := (mem_dyadicPaths _ _).mp (hC hq)
    simp only [blockDepth, Nat.zero_mul, Nat.sub_zero, ← hlen, List.take_length]
    rw [show q.length = N from hlen, prefixFiber_leaf hC hq]
    simp [blockProduct]
  | succ i ih =>
    have hb := blockClass_child_bounds L N B f (by omega : i < K) p hP
    have hc := prefixFiber_count_bounds (blockDepth_antitone N B (Nat.le_succ i)) P hb
      (fun c hc => ih (by omega) (prefixChildren_mem_image hc))
    dsimp only [blockProduct] at hc ⊢
    rw [Finset.prod_range_succ]
    constructor
    · simpa only [Nat.mul_comm] using hc.1
    · have hh := hc.2
      convert hh using 1
      ring

theorem blockClass_root_count {N : ℕ} {L : Finset CellPath} (hL : L ⊆ dyadicPaths N)
    {B : ℕ} (hB : 0 < B) (f : CellPath → List ℕ) {p : CellPath} (hp : p ∈ L) :
    let K := N/B+1
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K * blockProduct L F N B K p := by
  classical
  have hpC : p ∈ classLeaves L (blockLabel L N B f (N/B+1)) (blockLabel L N B f (N/B+1) p) := by
    simp [classLeaves,hp]
  have hc := blockClass_leaf_count hL B f (N/B+1) p (le_refl (N/B+1))
    (P := []) (by rw [blockDepth_terminal N hB]; exact Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  simpa only [blockDepth_terminal N hB, prefixFiber_zero] using hc

end PlanarFalconer

end OAI
