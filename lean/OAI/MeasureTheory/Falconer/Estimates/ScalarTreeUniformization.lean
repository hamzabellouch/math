import OAI.MeasureTheory.Falconer.Incidence.BlockLeafCounts
import Mathlib.Combinatorics.Pigeonhole

namespace OAI

/-! Scalar dyadic block regularization for the multiscale sum-product
argument. Exact prefix classes preserve local child counts; the loss per
block is only its width plus one. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem scalar_blockLabel_card_le {L : Finset (CellPath 1)} {N : ℕ}
    (hL : L ⊆ cubePaths 1 N) (B : ℕ) (f : CellPath 1 → List ℕ) (K : ℕ) :
    (L.image (blockLabel L N B f K)).card ≤ (B+1)^K*(L.image f).card := by
  induction K with
  | zero => simp [blockLabel]
  | succ K ih =>
    have hs := extendLabel_card_le (blockDepth_antitone N B (Nat.le_succ K))
      (Nat.sub_le N (K*B)) hL (blockLabel L N B f K)
    have hb : 1*(blockDepth N B K-blockDepth N B (K+1))+1 ≤ B+1 :=
      by simpa only [one_mul] using Nat.add_le_add_right (blockDepth_gap N B K) 1
    calc
      _ ≤ (B+1)*(L.image (blockLabel L N B f K)).card :=
        hs.trans (Nat.mul_le_mul_right _ hb)
      _ ≤ (B+1)*((B+1)^K*(L.image f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ac_rfl

theorem exists_large_scalar_block_class {L : Finset (CellPath 1)} {N : ℕ}
    (hL : L ⊆ cubePaths 1 N) (hLne : L.Nonempty) (B K : ℕ) :
    let F := blockLabel L N B (fun _ => []) K
    ∃ p ∈ L, L.card ≤ (B+1)^K*(classLeaves L F (F p)).card := by
  dsimp only
  let F := blockLabel L N B (fun _ => []) K
  obtain ⟨T,hT,hmax⟩ := (L.image F).exists_max_image
    (fun T => (classLeaves L F T).card) (hLne.image F)
  obtain ⟨p,hp,hpT⟩ := Finset.mem_image.mp hT
  refine ⟨p,hp,?_⟩
  have hc : (L.image F).card ≤ (B+1)^K := by
    have h := scalar_blockLabel_card_le hL B (fun _ => []) K
    have hi : (L.image (fun _ : CellPath 1 => ([] : List ℕ))).card ≤ 1 :=
      Finset.card_le_one.mpr (by intro a ha b hb; simp_all)
    exact h.trans ((Nat.mul_le_mul_left _ hi).trans_eq (Nat.mul_one _))
  calc
    L.card = ∑ t ∈ L.image F, (classLeaves L F t).card := by
      simpa only [classLeaves] using Finset.card_eq_sum_card_image F L
    _ ≤ ∑ _t ∈ L.image F, (classLeaves L F T).card := Finset.sum_le_sum hmax
    _ = (L.image F).card*(classLeaves L F T).card := by simp
    _ ≤ (B+1)^K*(classLeaves L F T).card := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← hpT]

theorem scalar_block_uniformization {L : Finset (CellPath 1)} {N : ℕ}
    (hL : L ⊆ cubePaths 1 N) (hLne : L.Nonempty) (B : ℕ) :
    ∃ Q : Finset (CellPath 1), ∃ n : ℕ → ℕ,
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ (B+1)^(N/B+1)*Q.card ∧
      ∀ i < N/B+1, 0 < n i ∧
        n i ≤ 2^(1*(blockDepth N B i-blockDepth N B (i+1))) ∧
        ∀ P ∈ Q.image (List.take (blockDepth N B (i+1))),
          n i ≤ (prefixChildren Q (blockDepth N B (i+1)) (blockDepth N B i) P).card ∧
          (prefixChildren Q (blockDepth N B (i+1)) (blockDepth N B i) P).card ≤ 2*n i := by
  let K := N/B+1
  let F := blockLabel L N B (fun _ => []) K
  obtain ⟨p,hp,hsize⟩ := exists_large_scalar_block_class hL hLne B K
  let Q := classLeaves L F (F p)
  have hpQ : p ∈ Q := by simp [Q,classLeaves,hp]
  refine ⟨Q,(fun i => blockBin L F N B i p),⟨p,hpQ⟩,Finset.filter_subset _ _,hsize,?_⟩
  intro i hi
  exact ⟨blockBin_pos L F N B i p,blockBin_le hL F B i p,
    fun P hP => blockClass_child_bounds L N B (fun _ => []) hi p hP⟩

end Falconer.Regularization

end OAI
