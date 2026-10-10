import OAI.NumberTheory.Ostmann.Characters.QuartetProductFibers

namespace OAI

/-! # Leaf coordinates within a labeled bottom quartet -/

namespace Ostmann

open scoped BigOperators

def quartetLeafIndex : (n : ℕ) → TreeLeafIndex n → TreeLeafIndex 2 → TreeLeafIndex (n + 2)
  | 0, _, j => j
  | n + 1, .inl q, j => .inl (quartetLeafIndex n q j)
  | n + 1, .inr q, j => .inr (quartetLeafIndex n q j)

def quartetLeafCoordinates : (n : ℕ) → TreeLeafIndex (n + 2) → TreeLeafIndex n × TreeLeafIndex 2
  | 0, j => ((), j)
  | n + 1, .inl j => let q := quartetLeafCoordinates n j; (.inl q.1, q.2)
  | n + 1, .inr j => let q := quartetLeafCoordinates n j; (.inr q.1, q.2)

theorem quartetLeafCoordinates_index (n : ℕ) (q : TreeLeafIndex n) (j : TreeLeafIndex 2) :
    quartetLeafCoordinates n (quartetLeafIndex n q j) = (q, j) := by
  induction n with
  | zero => cases q; rfl
  | succ n ih => cases q <;> simp only [quartetLeafIndex, quartetLeafCoordinates, ih]

theorem quartetLeafIndex_coordinates (n : ℕ) (j : TreeLeafIndex (n + 2)) :
    quartetLeafIndex n (quartetLeafCoordinates n j).1 (quartetLeafCoordinates n j).2 = j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact congrArg Sum.inl (ih j)
    | inr j => exact congrArg Sum.inr (ih j)

theorem quartetLeafCoordinates_fst (n : ℕ) (j : TreeLeafIndex (n + 2)) :
    (quartetLeafCoordinates n j).1 = bottomQuartet n j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact congrArg Sum.inl (ih j)
    | inr j => exact congrArg Sum.inr (ih j)

theorem bottomQuartet_leafIndex (n : ℕ) (q : TreeLeafIndex n) (j : TreeLeafIndex 2) :
    bottomQuartet n (quartetLeafIndex n q j) = q := by
  rw [← quartetLeafCoordinates_fst, quartetLeafCoordinates_index]

def quartetLeafIndexEquiv (n : ℕ) : TreeLeafIndex (n + 2) ≃ TreeLeafIndex n × TreeLeafIndex 2 where
  toFun := quartetLeafCoordinates n
  invFun q := quartetLeafIndex n q.1 q.2
  left_inv := quartetLeafIndex_coordinates n
  right_inv q := quartetLeafCoordinates_index n q.1 q.2

def quartetIndexFiberEquiv (n : ℕ) (q : TreeLeafIndex n) :
    {j : TreeLeafIndex (n + 2) // bottomQuartet n j = q} ≃ TreeLeafIndex 2 where
  toFun j := (quartetLeafCoordinates n j.1).2
  invFun j := ⟨quartetLeafIndex n q j, bottomQuartet_leafIndex n q j⟩
  left_inv j := by
    apply Subtype.ext
    have h := quartetLeafIndex_coordinates n j.1
    rw [quartetLeafCoordinates_fst, j.property] at h
    exact h
  right_inv j := congrArg Prod.snd (quartetLeafCoordinates_index n q j)

theorem quartetBlockEquiv_read (A : Type*) (n : ℕ) (m : TreeLeafTuple A (n + 2))
    (q : TreeLeafIndex n) (j : TreeLeafIndex 2) :
    treeLeafTupleEquiv A 2 (quartetBlockEquiv A n m q) j =
      treeLeafTupleEquiv A (n + 2) m (quartetLeafIndex n q j) := by
  induction n with
  | zero => cases q; rfl
  | succ n ih =>
    cases q with
    | inl q => exact ih m.1 q
    | inr q => exact ih m.2 q

theorem sum_bottomQuartet_fiber {R : Type*} [AddCommMonoid R] (n : ℕ)
    (q : TreeLeafIndex n) (f : TreeLeafIndex (n + 2) → R) :
    (∑ j ∈ Finset.univ.filter (fun j => bottomQuartet n j = q), f j) =
      ∑ j : TreeLeafIndex 2, f (quartetLeafIndex n q j) := by
  classical
  have h := (quartetIndexFiberEquiv n q).symm.sum_comp
    (fun j : {j : TreeLeafIndex (n + 2) // bottomQuartet n j = q} => f j.1)
  change (∑ j : TreeLeafIndex 2, f (quartetLeafIndex n q j)) =
    ∑ j : {j : TreeLeafIndex (n + 2) // bottomQuartet n j = q}, f j.1 at h
  rw [h]
  exact Finset.sum_subtype _ (by simp) f

theorem sum_four_treeLeaves {R : Type*} [AddCommMonoid R] (f : TreeLeafIndex 2 → R) :
    (∑ i : TreeLeafIndex 2, f i) =
      (f (.inl (.inl ())) + f (.inl (.inr ()))) +
        (f (.inr (.inl ())) + f (.inr (.inr ()))) := by
  calc
    _ = (∑ i : Unit ⊕ Unit, f (.inl i)) + ∑ i : Unit ⊕ Unit, f (.inr i) :=
      Fintype.sum_sum_type f
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Fintype.sum_unique]
      congr 5

end Ostmann

end OAI
