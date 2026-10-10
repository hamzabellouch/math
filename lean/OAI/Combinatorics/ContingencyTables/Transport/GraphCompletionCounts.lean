import OAI.Combinatorics.ContingencyTables.Transport.GraphCompletionUnique

namespace OAI

/-!
# Multiplicity-one forest-coordinate sums

The finite coordinates are the actual tree cells of the row/column
forest, with physical intervals [-10 d b,10 d b]. A solution of the
nonroot equations contributes exactly once, with its original weight.
-/

namespace ContingencyTables.GraphCompletionCounts

open scoped BigOperators Classical
open SimpleGraph
open ForestCapacity GraphIntegralCompletion GraphCompletionUnique

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev TreeCell (T : SimpleGraph (I⊕J)) :=
  {a : I×J // T.Adj (.inl a.1) (.inr a.2)}

abbrev TreeIndex (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) :=
  (e : TreeCell T) → Fin (20*d*b e.val.1 e.val.2+1)

noncomputable def physical (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ)
    (a : TreeIndex T d b) (i : I) (j : J) : ℤ :=
  if h : T.Adj (.inl i) (.inr j) then
    -((10*d*b i j:ℕ):ℤ)+(a ⟨(i,j),h⟩).val else 0

omit [Fintype I] [Fintype J] in
lemma physical_supported (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ)
    (a : TreeIndex T d b) (i : I) (j : J) (h : ¬T.Adj (.inl i) (.inr j)) :
    physical T d b a i j=0 := by simp only [physical,h,not_false_eq_true,dite_eq_right]

omit [Fintype I] [Fintype J] in
lemma physical_injective (T : SimpleGraph (I⊕J)) (d : ℕ) (b : I → J → ℕ) :
    Function.Injective (physical T d b) := by
  intro a a' h
  funext e
  apply Fin.ext
  have he := congrFun (congrFun h e.val.1) e.val.2
  simp only [physical,e.property,dite_eq_left] at he
  exact_mod_cast (add_left_cancel he : ((a e).val:ℤ)=((a' e).val:ℤ))

def NonrootMargins (T : SimpleGraph (I⊕J)) (r : I → ℤ) (c : J → ℤ)
    (z : I → J → ℤ) : Prop :=
  (∀ i, Sum.inl i≠componentRoot T (.inl i) → (∑ j, z i j)=r i) ∧
  (∀ j, Sum.inr j≠componentRoot T (.inr j) → (∑ i, z i j)=c j)

noncomputable def solutionIndex (T : SimpleGraph (I⊕J)) (r : I → ℤ) (c : J → ℤ)
    (d : ℕ) (b : I → J → ℕ)
    (hbox : ∀ i j, T.Adj (.inl i) (.inr j) →
      -((10*d*b i j:ℕ):ℤ)≤tableCompletion T r c i j ∧
        tableCompletion T r c i j≤(10*d*b i j:ℕ)) : TreeIndex T d b := fun e =>
  ⟨(tableCompletion T r c e.val.1 e.val.2+(10*d*b e.val.1 e.val.2:ℕ)).toNat,by
    have h := hbox e.val.1 e.val.2 e.property
    have hz : 0≤tableCompletion T r c e.val.1 e.val.2+(10*d*b e.val.1 e.val.2:ℕ) := by omega
    have hle : (tableCompletion T r c e.val.1 e.val.2+(10*d*b e.val.1 e.val.2:ℕ)).toNat≤
        20*d*b e.val.1 e.val.2 := by
      exact_mod_cast (show ((tableCompletion T r c e.val.1 e.val.2+
        (10*d*b e.val.1 e.val.2:ℕ)).toNat:ℤ)≤(20*d*b e.val.1 e.val.2:ℕ) by
          rw [Int.toNat_of_nonneg hz]
          push_cast at h ⊢
          nlinarith)
    omega⟩

lemma physical_solutionIndex (T : SimpleGraph (I⊕J)) (r : I → ℤ) (c : J → ℤ)
    (d : ℕ) (b : I → J → ℕ)
    (hbox : ∀ i j, T.Adj (.inl i) (.inr j) →
      -((10*d*b i j:ℕ):ℤ)≤tableCompletion T r c i j ∧
        tableCompletion T r c i j≤(10*d*b i j:ℕ)) :
    physical T d b (solutionIndex T r c d b hbox)=tableCompletion T r c := by
  funext i j
  by_cases h : T.Adj (.inl i) (.inr j)
  · have hz : 0≤tableCompletion T r c i j+(10*d*b i j:ℕ) := by
      have hb := hbox i j h
      omega
    simp only [physical,h,dite_eq_left,solutionIndex,Int.toNat_of_nonneg hz]
    omega
  · simp only [physical,h,not_false_eq_true,dite_eq_right,tableCompletion_supported T r c i j h]

/-- The actual tree intervals contain the unique completion, so the
finite equality-indicator sum has multiplicity exactly one. -/
theorem weighted_completion_sum (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (hT : T.IsAcyclic)
    (r : I → ℤ) (c : J → ℤ) (d : ℕ) (b : I → J → ℕ)
    (hbox : ∀ i j, T.Adj (.inl i) (.inr j) →
      -((10*d*b i j:ℕ):ℤ)≤tableCompletion T r c i j ∧
        tableCompletion T r c i j≤(10*d*b i j:ℕ))
    (weight : (I → J → ℤ) → ℝ) :
    (∑ a : TreeIndex T d b, if NonrootMargins T r c (physical T d b a)
      then weight (physical T d b a) else 0)=weight (tableCompletion T r c) := by
  let a₀ := solutionIndex T r c d b hbox
  have ha₀ : physical T d b a₀=tableCompletion T r c := physical_solutionIndex T r c d b hbox
  have hsol : NonrootMargins T r c (tableCompletion T r c) :=
    ⟨tableCompletion_row small T hTG r c,tableCompletion_column small T hTG r c⟩
  rw [Finset.sum_eq_single a₀]
  · simp only [ha₀,hsol,ite_true]
  · intro a _ hne
    by_cases ha : NonrootMargins T r c (physical T d b a)
    · have he := tableCompletion_unique small T hTG hT r c (physical T d b a)
        (physical_supported T d b a) ha.1 ha.2
      have haa : a=a₀ := physical_injective T d b (he.trans ha₀.symm)
      exact (hne haa).elim
    · simp only [ha,ite_false]
  · simp

end ContingencyTables.GraphCompletionCounts

end OAI
