import OAI.Probability.Ising.Basic

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma fkWeight_nonneg {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) :
    0 ≤ fkWeight G I J F ω := by
  classical
  unfold fkWeight
  apply mul_nonneg (pow_nonneg (by norm_num) _)
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    nlinarith [G.coupling_nonneg e]
  · exact (Real.exp_pos _).le

lemma fkWeight_empty_pos {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) : 0 < fkWeight G I J F ∅ := by
  classical
  unfold fkWeight
  simp only [Finset.notMem_empty, ↓reduceIte]
  exact mul_pos (pow_pos (by norm_num) _) (Finset.prod_pos fun _ _ => Real.exp_pos _)

lemma comparison_empty_preserves_I {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J) (x y : KeptVertex F)
    (hxy : (comparisonSetoid G I J F ∅).r x y) :
    x.val ∈ I ↔ y.val ∈ I := by
  induction hxy with
  | rel x y h =>
    rcases h with h | h | ⟨e, he, _⟩
    · exact iff_of_true h.1 h.2
    · exact iff_of_false
        (fun hx => Finset.disjoint_left.mp hIJ hx h.1)
        (fun hy => Finset.disjoint_left.mp hIJ hy h.2)
    · exact (Finset.notMem_empty e he).elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

lemma qZero_nonneg_lt_one {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    0 ≤ qZero G I J F i j ∧ qZero G I J F i j < 1 := by
  classical
  have he : (∅ : Finset (Fin m)) ∈ (keptEdges G F).powerset :=
    Finset.mem_powerset.mpr (Finset.empty_subset _)
  have hden : 0 < ∑ ω ∈ (keptEdges G F).powerset, fkWeight G I J F ω :=
    lt_of_lt_of_le (fkWeight_empty_pos G I J F)
      (Finset.single_le_sum (fun ω _ => fkWeight_nonneg G I J F ω) he)
  have hno : ¬(comparisonSetoid G I J F ∅).r i j := by
    intro hconn
    exact Finset.disjoint_left.mp hIJ
      ((comparison_empty_preserves_I G I J F hIJ i j hconn).mp hi) hj
  unfold qZero
  constructor
  · apply div_nonneg _ hden.le
    apply Finset.sum_nonneg
    intro ω _
    split_ifs
    · exact fkWeight_nonneg G I J F ω
    · exact le_rfl
  · apply (div_lt_one hden).mpr
    apply Finset.sum_lt_sum
    · intro ω _
      split_ifs
      · exact le_rfl
      · exact fkWeight_nonneg G I J F ω
    · exact ⟨∅, he, by simpa only [hno, ite_false] using fkWeight_empty_pos G I J F⟩

lemma comparisonRel_terminal_swap {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) :
    comparisonRel G I J F ω = comparisonRel G J I F ω := by
  funext x y
  apply propext
  simp only [comparisonRel]
  exact or_left_comm

/-- The zero-field terminal connection probability is symmetric under exchange of the terminal sets. -/
lemma qZero_terminal_swap {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) :
    qZero G I J F i j = qZero G J I F j i := by
  classical
  have hs : ∀ ω, comparisonSetoid G I J F ω = comparisonSetoid G J I F ω := by
    intro ω
    unfold comparisonSetoid
    rw [comparisonRel_terminal_swap G I J F ω]
  have hw : ∀ ω, fkWeight G I J F ω = fkWeight G J I F ω := by
    intro ω
    unfold fkWeight clusterCount
    rw [hs ω]
  have hr : ∀ ω, (comparisonSetoid G I J F ω).r i j ↔
      (comparisonSetoid G J I F ω).r j i := by
    intro ω
    change Relation.EqvGen (comparisonRel G I J F ω) i j ↔
      Relation.EqvGen (comparisonRel G J I F ω) j i
    rw [comparisonRel_terminal_swap G I J F ω]
    exact ⟨fun h => Relation.EqvGen.symm _ _ h, fun h => Relation.EqvGen.symm _ _ h⟩
  unfold qZero
  simp only [hw, hr]

lemma qZero_independent_representatives {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i i' j j' : KeptVertex F)
    (hi : i.val ∈ I) (hi' : i'.val ∈ I) (hj : j.val ∈ J) (hj' : j'.val ∈ J) :
    qZero G I J F i j = qZero G I J F i' j' := by
  classical
  unfold qZero
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  have hconn : (comparisonSetoid G I J F ω).r i j ↔
      (comparisonSetoid G I J F ω).r i' j' := by
    have hii : (comparisonSetoid G I J F ω).r i i' :=
      Relation.EqvGen.rel _ _ (Or.inl ⟨hi, hi'⟩)
    have hjj : (comparisonSetoid G I J F ω).r j j' :=
      Relation.EqvGen.rel _ _ (Or.inr (Or.inl ⟨hj, hj'⟩))
    have hsym : ∀ {u v}, (comparisonSetoid G I J F ω).r u v →
        (comparisonSetoid G I J F ω).r v u := (comparisonSetoid G I J F ω).iseqv.symm
    have htrans : ∀ {u v z}, (comparisonSetoid G I J F ω).r u v →
        (comparisonSetoid G I J F ω).r v z → (comparisonSetoid G I J F ω).r u z :=
      (comparisonSetoid G I J F ω).iseqv.trans
    exact ⟨fun h => htrans (hsym hii) (htrans h hjj),
      fun h => htrans hii (htrans h (hsym hjj))⟩
  simp only [hconn]

end BufferedIsing

end OAI
