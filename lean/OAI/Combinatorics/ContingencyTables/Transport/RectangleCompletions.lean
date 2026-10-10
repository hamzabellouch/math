import OAI.Combinatorics.ContingencyTables.Transport.CompletionCounts

namespace OAI

/-! # Supported completions are tables on the actual large rectangle -/

namespace ContingencyTables.CompletionCounts

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

lemma sum_subtype_eq_of_zero {K : Type*} [Fintype K] (p : K → Prop)
    (f : K → ℕ) (hf : ∀ k,¬p k → f k=0) :
    (∑ k : {k // p k},f k.val)=∑ k,f k := by
  calc
    _ = ∑ k ∈ Finset.univ.filter p,f k := (Finset.sum_subtype _ (by simp) f).symm
    _ = ∑ k,f k := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : p k
      · rw [ite_eq_left hk]
      · rw [ite_eq_right hk,hf k hk]

noncomputable def rectangleRestrict (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ) (A : LargeCompletion small R C) :
    Table (fun i : {i // p i} => R i.val) (fun j : {j // q j} => C j.val) := by
  refine ⟨fun i j => A.val.val i.val j.val,?_,?_⟩
  · intro i
    rw [sum_subtype_eq_of_zero q (A.val.val i.val)]
    · exact A.val.property.1 i.val
    · intro j hj
      apply A.property
      apply Bool.eq_true_of_ne_false
      intro hs
      exact hj ((hrect i.val j).mp hs).2
  · intro j
    rw [sum_subtype_eq_of_zero p (fun i => A.val.val i j.val)]
    · exact A.val.property.2 j.val
    · intro i hi
      apply A.property
      apply Bool.eq_true_of_ne_false
      intro hs
      exact hi ((hrect i j.val).mp hs).1

noncomputable def rectangleExtend (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ)
    (hR : ∀ i,¬p i → R i=0) (hC : ∀ j,¬q j → C j=0)
    (A : Table (fun i : {i // p i} => R i.val) (fun j : {j // q j} => C j.val)) :
    LargeCompletion small R C := by
  let F : I → J → ℕ := fun i j => if hi : p i then if hj : q j then A.val ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0
  have hzero (i : I) (j : J) (hs : small i j=true) : F i j=0 := by
    dsimp only [F]
    split_ifs with hi hj
    · have hh := (hrect i j).mpr ⟨hi,hj⟩
      rw [hs] at hh
      contradiction
    · rfl
    · rfl
  refine ⟨⟨F,?_,?_⟩,hzero⟩
  · intro i
    by_cases hi : p i
    · rw [← sum_subtype_eq_of_zero q (F i) (by
        intro j hj; simp [F,hi,hj])]
      convert A.property.1 ⟨i,hi⟩ using 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [F,dite_eq_left hi,dite_eq_left j.property]
    · simp [F,hi,hR i hi]
  · intro j
    by_cases hj : q j
    · rw [← sum_subtype_eq_of_zero p (fun i => F i j) (by
        intro i hi; simp [F,hi])]
      convert A.property.2 ⟨j,hj⟩ using 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [F,dite_eq_left i.property,dite_eq_left hj]
    · have hz : ∀ i,F i j=0 := by intro i; dsimp only [F]; split_ifs <;> simp_all
      simp only [hz,Finset.sum_const_zero,hC j hj]

noncomputable def rectangleCompletionEquiv (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ)
    (hR : ∀ i,¬p i → R i=0) (hC : ∀ j,¬q j → C j=0) :
    LargeCompletion small R C ≃
      Table (fun i : {i // p i} => R i.val) (fun j : {j // q j} => C j.val) where
  toFun := rectangleRestrict small p q hrect R C
  invFun := rectangleExtend small p q hrect R C hR hC
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    change (if hi : p i then if hj : q j then A.val.val i j else 0 else 0)=A.val.val i j
    split_ifs with hi hj
    · rfl
    · symm
      apply A.property
      apply Bool.eq_true_of_ne_false
      intro hs
      exact hj ((hrect i j).mp hs).2
    · symm
      apply A.property
      apply Bool.eq_true_of_ne_false
      intro hs
      exact hi ((hrect i j).mp hs).1
  right_inv A := by
    apply Subtype.ext
    funext i j
    change (if hi : p i.val then if hj : q j.val then A.val ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0 else 0)=A.val i j
    simp only [dite_eq_left i.property,dite_eq_left j.property]

end ContingencyTables.CompletionCounts

end OAI
