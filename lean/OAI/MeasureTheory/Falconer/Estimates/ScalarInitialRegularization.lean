import OAI.MeasureTheory.Falconer.Recursion.ScalarBranchingLevel
import OAI.MeasureTheory.Falconer.Estimates.ScalarTreeUniformization

namespace OAI

/-! Initial scalar tree regularization with actual separated child cells,
 exact dyadic branching, and a quadratic loss per block. -/
namespace Falconer.Regularization

 theorem scalar_initial_regularization {N : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (B : ℕ) :
    ∃ Q : Finset (CellPath 1), ∃ k n : ℕ → ℕ,
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ (2050*(B+1)^2)^(N/B+1)*Q.card ∧
      ∀ i < N/B+1, ScalarBranchingLevel Q (blockDepth N B (i+1)) (blockDepth N B i) (k i) (n i) := by
  classical
  let D := 2050*(B+1)^2
  have hbuild : ∀ i ≤ N/B+1, ∃ Q : Finset (CellPath 1), ∃ m : ℕ, ∃ k n : ℕ → ℕ,
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ D^i*Q.card ∧
      (∀ p ∈ Q.image (List.take (blockDepth N B i)),
        (prefixFiber Q (blockDepth N B i) p).card = m) ∧
      ∀ j < i, ScalarBranchingLevel Q (blockDepth N B (j+1)) (blockDepth N B j) (k j) (n j) := by
    intro i hi
    induction i with
    | zero =>
      refine ⟨L,1,fun _ => 0,fun _ => 0,hne,Finset.Subset.refl _,by simp,?_,by simp⟩
      intro p hp
      simp only [blockDepth,Nat.zero_mul,Nat.sub_zero] at hp ⊢
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      have hlen := (mem_cubePaths 1 N q).mp (hL hq)
      have he : q.take N = q := by rw [← hlen,List.take_length]
      change (prefixFiber L N (q.take N)).card = 1
      rw [he,prefixFiber_leaf hL hq]
      simp
    | succ i ih =>
      obtain ⟨Q,m,k,n,hQne,hQL,hsize,hm,hlevels⟩ := ih (by omega)
      have hab := blockDepth_antitone N B (Nat.le_succ i)
      have hb : blockDepth N B i ≤ N := Nat.sub_le _ _
      obtain ⟨K,k0,n0,hRne,hRQ,hQR,hlevel,hm'⟩ :=
        scalar_block_pruning_level Q (hQL.trans hL) hQne hab hb m hm
      let R := scalarPruneLeaves Q (blockDepth N B (i+1)) (blockDepth N B i) K
      have hloc : 2050*(blockDepth N B i-blockDepth N B (i+1)+1)^2 ≤ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (blockDepth_gap N B i) 1) 2)
      refine ⟨R,2^k0*m,Function.update k i k0,Function.update n i n0,hRne,hRQ.trans hQL,?_,hm',?_⟩
      · calc
          L.card ≤ D^i*Q.card := hsize
          _ ≤ D^i*((2050*(blockDepth N B i-blockDepth N B (i+1)+1)^2)*R.card) :=
            Nat.mul_le_mul_left _ hQR
          _ ≤ D^i*(D*R.card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hloc)
          _ = D^(i+1)*R.card := by rw [pow_succ]; ring
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self] using hlevel
        · have hji' : j < i := by omega
          have hdepth : blockDepth N B i ≤ blockDepth N B (j+1) :=
            blockDepth_antitone N B (by omega)
          have hh := (hlevels j hji').prune hab hdepth K
          simpa only [Function.update_of_ne hji] using hh
  obtain ⟨Q,_,k,n,hQne,hQL,hcard,_,hlevels⟩ := hbuild (N/B+1) le_rfl
  exact ⟨Q,k,n,hQne,hQL,hcard,hlevels⟩

end Falconer.Regularization

end OAI
