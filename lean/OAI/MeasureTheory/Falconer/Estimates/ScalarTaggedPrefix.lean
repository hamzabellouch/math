import OAI.MeasureTheory.Falconer.Measures.ScalarPrefixPruning
import OAI.MeasureTheory.Falconer.Measures.ScalarTaggedPruning

namespace OAI

/-! Common-tag selection for a scalar dyadic block. The operation
 removes whole child cells and therefore keeps lower completed fibers. -/
namespace Falconer.Regularization

 theorem prefixFiber_pairwise_disjoint (L : Finset (CellPath 1)) (a : ℕ)
    (P : Finset (CellPath 1)) : (P : Set (CellPath 1)).PairwiseDisjoint (prefixFiber L a) := by
  classical
  intro p _ q _ hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hpq ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)

 theorem prefixFiber_biUnion (L : Finset (CellPath 1)) (a : ℕ) :
    (L.image (List.take a)).biUnion (prefixFiber L a) = L := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨p,_,hq⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_filter.mp hq).1
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨q.take a,Finset.mem_image_of_mem _ hq,
      Finset.mem_filter.mpr ⟨hq,rfl⟩⟩

 theorem scalarPruneLeaves_fiber_uniform (L : Finset (CellPath 1)) {a b : ℕ}
    (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1)) (p : CellPath 1)
    (hK : K p ⊆ prefixChildren L a b p) (m : ℕ)
    (hm : ∀ c ∈ prefixChildren L a b p, (prefixFiber L b c).card = m) :
    (prefixFiber (scalarPruneLeaves L a b K) a p).card = (K p).card*m := by
  rw [scalarPruneLeaves_fiber_card L hab K p hK]
  calc
    _ = ∑ _c ∈ K p, m := Finset.sum_congr rfl (fun c hc => hm c (hK hc))
    _ = _ := by simp

 theorem scalar_tagged_prefix_prune (L : Finset (CellPath 1)) (hL : L.Nonempty)
    {a b : ℕ} (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1))
    {τ : Type*} [DecidableEq τ] (tag : CellPath 1 → τ) (D H m : ℕ)
    (hK : ∀ p ∈ L.image (List.take a), K p ⊆ prefixChildren L a b p)
    (hkeep : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).card ≤ D*(K p).card)
    (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m)
    (htags : ((L.image (List.take a)).image tag).card ≤ H) :
    ∃ t ∈ (L.image (List.take a)).image tag,
      let Kt := fun p => if tag p = t then K p else ∅
      L.card ≤ D*H*(scalarPruneLeaves L a b Kt).card ∧
      ∀ q ∈ scalarPruneLeaves L a b Kt, tag (q.take a) = t := by
  classical
  let P := L.image (List.take a)
  let R := scalarPruneLeaves L a b K
  let C := prefixFiber L a
  let F := prefixFiber R a
  have hFC : ∀ p ∈ P, F p ⊆ C p := by
    intro p _ q hq
    exact Finset.mem_filter.mpr ⟨scalarPruneLeaves_subset L a b K (Finset.mem_filter.mp hq).1,
      (Finset.mem_filter.mp hq).2⟩
  have hcards : ∀ p ∈ P, (C p).card ≤ D*(F p).card := by
    intro p hp
    have hm' : ∀ c ∈ prefixChildren L a b p, (prefixFiber L b c).card = m :=
      fun c hc => hm c (prefixChildren_mem_image hc)
    have hc : (C p).card = (prefixChildren L a b p).card*m := by
      rw [prefixFiber_card_sum hab]
      calc
        _ = ∑ _c ∈ prefixChildren L a b p, m := Finset.sum_congr rfl hm'
        _ = _ := by simp
    have hf : (F p).card = (K p).card*m := scalarPruneLeaves_fiber_uniform L hab K p (hK p hp) m hm'
    rw [hc,hf]
    calc
      _ ≤ (D*(K p).card)*m := Nat.mul_le_mul_right m (hkeep p hp)
      _ = _ := by ring
  obtain ⟨t,ht,hbound⟩ := scalar_tagged_child_pruning P (hL.image (List.take a)) C F tag D H hFC
    (prefixFiber_pairwise_disjoint L a P) hcards htags
  let Kt := fun p => if tag p = t then K p else ∅
  have heq : (P.filter fun p => tag p = t).biUnion F = scalarPruneLeaves L a b Kt := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp,hq⟩ := Finset.mem_biUnion.mp hq
      have hpt := (Finset.mem_filter.mp hp).2
      have hqa := (Finset.mem_filter.mp hq).2
      have hqR := (Finset.mem_filter.mp hq).1
      have hqL := scalarPruneLeaves_subset L a b K hqR
      have hqK := (Finset.mem_filter.mp hqR).2
      apply Finset.mem_filter.mpr
      refine ⟨hqL,?_⟩
      change q.take b ∈ if tag (q.take a) = t then K (q.take a) else ∅
      rw [hqa,ite_eq_left hpt]
      rwa [hqa] at hqK
    · intro hq
      have hqL := (Finset.mem_filter.mp hq).1
      have hqKt := (Finset.mem_filter.mp hq).2
      have hqt : tag (q.take a) = t := by
        by_contra hh
        simp only [Kt,ite_eq_right hh,Finset.notMem_empty] at hqKt
      have hqK : q.take b ∈ K (q.take a) := by
        simpa only [Kt,ite_eq_left hqt] using hqKt
      exact Finset.mem_biUnion.mpr ⟨q.take a,
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hqL,hqt⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hqL,hqK⟩,rfl⟩⟩
  refine ⟨t,ht,?_,?_⟩
  · rw [← heq,← prefixFiber_biUnion L a]
    exact hbound
  · intro q hq
    have hh := (Finset.mem_filter.mp hq).2
    by_contra hqt
    simp only [ite_eq_right hqt,Finset.notMem_empty] at hh

end Falconer.Regularization

end OAI
