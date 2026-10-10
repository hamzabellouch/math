import OAI.Combinatorics.ContingencyTables.Transport.IntegerRecursiveFlow

namespace OAI

/-! # The actual leaf energy as a finite sum of complete displays -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

noncomputable def leafClique {C : Type*} [Fintype C] [DecidableEq C]
    (F H : (C → ℕ) → ℝ) (z : C → ℕ) : ℝ :=
  SignedTransport.cliqueEnergy (oneHole F z) (fun _ => 1) (fun i => H (removeOne z i))

lemma oneHole_reindex {C D : Type*} [DecidableEq C] [DecidableEq D]
    (e : C ≃ D) (F : (D → ℕ) → ℝ) (z : C → ℕ) (i : C) :
    oneHole (fun x => F (x ∘ e.symm)) z i = oneHole F (z ∘ e.symm) (e i) := by
  unfold oneHole
  simp only [Function.comp_apply, Equiv.symm_apply_apply, removeOne_reindex]

lemma leafClique_reindex {C D : Type*} [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] (e : C ≃ D) (F H : (D → ℕ) → ℝ) (z : C → ℕ) :
    leafClique (fun x => F (x ∘ e.symm)) (fun x => H (x ∘ e.symm)) z =
      leafClique F H (z ∘ e.symm) := by
  unfold leafClique SignedTransport.cliqueEnergy
  simp only [one_mul, oneHole_reindex, removeOne_reindex]
  congr 1
  calc
    _ = ∑ i : C, ∑ j : D,
        min (oneHole F (z ∘ e.symm) (e i)) (oneHole F (z ∘ e.symm) j) *
          (H (removeOne (z ∘ e.symm) (e i))-H (removeOne (z ∘ e.symm) j))^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j : D =>
        min (oneHole F (z ∘ e.symm) (e i)) (oneHole F (z ∘ e.symm) j) *
          (H (removeOne (z ∘ e.symm) (e i))-H (removeOne (z ∘ e.symm) j))^2)
    _ = _ := e.sum_comp (fun i : D => ∑ j : D,
      min (oneHole F (z ∘ e.symm) i) (oneHole F (z ∘ e.symm) j) *
        (H (removeOne (z ∘ e.symm) i)-H (removeOne (z ∘ e.symm) j))^2)

noncomputable def leafEnergySum {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) : ℝ :=
  ∑ a : Assignments Ms, leafClique F H (embedding Ms z a)

/-- Every recursive leaf is exactly its literal full display, counted
once in the Cartesian product of the ordinary balanced profiles. -/
theorem recursiveEnergy_eq_leafEnergySum : ∀ (Ms : List ℕ) {I : Type u}
    [Fintype I] [DecidableEq I] (F H : (Coordinates I Ms → ℕ) → ℝ)
    (z : I → ℕ) (h : I → ℝ),
    recursiveEnergy Ms F H z h=leafEnergySum Ms F H z := by
  intro Ms
  induction Ms with
  | nil =>
    intro I _ _ F H z h
    simp only [recursiveEnergy, leafEnergySum, Assignments, embedding, Fintype.sum_unique, leafClique]
  | cons U Ms ih =>
    intro I _ _ F H z h
    let f := exposedFamily Ms F
    let g := pairCoefficient (cross f (U+1) z) (innerWeight f (U+1) z) h
    change (∑ j : Fin (U+1), recursiveEnergy Ms
      (fun x => F (x ∘ (exposeEquiv (I := I) Ms).symm))
      (fun x => H (x ∘ (exposeEquiv (I := I) Ms).symm))
      (profile z j.val (U-j.val)) (extendCoefficients h (g j.val) (g (j.val+1)))) = _
    simp_rw [ih]
    unfold leafEnergySum
    simp_rw [leafClique_reindex]
    have he (j : Fin (U+1)) (a : Assignments Ms) :
        embedding Ms (profile z j.val (U-j.val)) a ∘ (exposeEquiv (I := I) Ms).symm =
          profile (embedding Ms z a) j.val (U-j.val) :=
      expose_embedding Ms z j.val (U-j.val) a
    simp_rw [he]
    rw [Finset.sum_comm]
    change (∑ a : Assignments Ms, ∑ j : Fin (U+1),
      leafClique F H (profile (embedding Ms z a) j.val (U-j.val))) =
      ∑ a : Assignments Ms × Fin (U+1), leafClique F H (embedding (U::Ms) z a)
    rw [Fintype.sum_prod_type]
    rfl

lemma embedding_injective {I : Type u} (Ms : List ℕ) (z : I → ℕ) :
    Function.Injective (embedding Ms z) := by
  induction Ms with
  | nil => intro a b _; exact Subsingleton.elim _ _
  | cons U Ms ih =>
    intro a b hab
    apply Prod.ext
    · apply ih
      funext i
      exact congrFun hab (.inl i)
    · apply Fin.ext
      exact congrFun hab (.inr false)

/-- Distinct valid holes recover their full display by the coordinate
maximum. This is the reason different leaf cliques share no edges. -/
lemma max_removeOne {C : Type*} [DecidableEq C] (z : C → ℕ) (i j : C)
    (hij : i ≠ j) :
    (fun k => max (removeOne z i k) (removeOne z j k))=z := by
  funext k
  unfold removeOne
  by_cases hki : k=i
  · subst k
    simp only [hij, ↓reduceIte, Nat.sub_zero]
    exact max_eq_right (Nat.sub_le _ _)
  · by_cases hkj : k=j
    · subst k
      simp only [hki, ↓reduceIte, Nat.sub_zero]
      exact max_eq_left (Nat.sub_le _ _)
    · simp only [hki,hkj,↓reduceIte,Nat.sub_zero,max_self]

lemma removeOne_injective_valid {C : Type*} [DecidableEq C] (z : C → ℕ)
    (i j : C) (hi : 0 < z i) (he : removeOne z i=removeOne z j) : i=j := by
  by_contra hij
  have h := congrFun he i
  simp only [removeOne, hij, ↓reduceIte, Nat.sub_zero] at h
  omega

def leafEdgeCodes {I : Type u} [Fintype I] [DecidableEq I] (Ms : List ℕ) (z : I → ℕ) :
    Finset (Assignments Ms × Coordinates I Ms × Coordinates I Ms) :=
  Finset.univ.filter (fun e => 0 < embedding Ms z e.1 e.2.1 ∧
    0 < embedding Ms z e.1 e.2.2 ∧ e.2.1 ≠ e.2.2)

def leafEdgeState {I : Type u} [DecidableEq I] (Ms : List ℕ) (z : I → ℕ)
    (e : Assignments Ms × Coordinates I Ms × Coordinates I Ms) :
    (Coordinates I Ms → ℕ) × (Coordinates I Ms → ℕ) :=
  (removeOne (embedding Ms z e.1) e.2.1, removeOne (embedding Ms z e.1) e.2.2)

/-- An oriented exchange edge determines its display, then its branch
assignment, then its two hole coordinates. -/
theorem leafEdgeState_injective {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) :
    Set.InjOn (leafEdgeState Ms z) (leafEdgeCodes Ms z) := by
  intro a ha b hb he
  obtain ⟨hai,haj,haij⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨hbi,hbj,hbij⟩ := (Finset.mem_filter.mp hb).2
  have hd : embedding Ms z a.1=embedding Ms z b.1 := by
    calc
      _ = fun k => max ((leafEdgeState Ms z a).1 k) ((leafEdgeState Ms z a).2 k) :=
        (max_removeOne _ _ _ haij).symm
      _ = fun k => max ((leafEdgeState Ms z b).1 k) ((leafEdgeState Ms z b).2 k) := by rw [he]
      _ = _ := max_removeOne _ _ _ hbij
  have hab := embedding_injective Ms z hd
  apply Prod.ext hab
  apply Prod.ext
  · apply removeOne_injective_valid (embedding Ms z a.1) _ _ hai
    have ht := congrArg Prod.fst he
    change removeOne (embedding Ms z a.1) a.2.1=removeOne (embedding Ms z b.1) b.2.1 at ht
    simpa only [←hab] using ht
  · apply removeOne_injective_valid (embedding Ms z a.1) _ _ haj
    have ht := congrArg Prod.snd he
    change removeOne (embedding Ms z a.1) a.2.2=removeOne (embedding Ms z b.1) b.2.2 at ht
    simpa only [←hab] using ht

noncomputable def leafEdges {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) :
    Finset ((Coordinates I Ms → ℕ) × (Coordinates I Ms → ℕ)) :=
  (leafEdgeCodes Ms z).image (leafEdgeState Ms z)

noncomputable def edgeTerm {C : Type*} (F H : (C → ℕ) → ℝ)
    (e : (C → ℕ) × (C → ℕ)) : ℝ :=
  min (F e.1) (F e.2) * (H e.1-H e.2)^2

lemma leafClique_eq_valid_sum {C : Type*} [Fintype C] [DecidableEq C]
    (F H : (C → ℕ) → ℝ) (z : C → ℕ) (hF : ∀ x, 0 ≤ F x) :
    leafClique F H z = (∑ i, ∑ j,
      if 0 < z i ∧ 0 < z j ∧ i ≠ j then
        edgeTerm F H (removeOne z i,removeOne z j) else 0)/2 := by
  unfold leafClique SignedTransport.cliqueEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_mul]
  by_cases hij : i=j
  · subst j
    simp
  · by_cases hi : 0 < z i
    · by_cases hj : 0 < z j
      · simp [oneHole,edgeTerm,hi,hj,hij]
      · simp only [oneHole,hi,hj,↓reduceIte,and_false,false_and,
          min_eq_right (hF _),zero_mul]
    · have hj := oneHole_nonnegative F hF z j
      simp only [oneHole,hi,↓reduceIte] at hj ⊢
      rw [min_eq_left hj]
      simp

/-- Complete leaf cliques have disjoint oriented edges. The resulting
energy is exactly the ordinary minimum-endpoint graph sum. -/
theorem leafEnergySum_eq_edges {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ)
    (hF : ∀ x, 0 ≤ F x) :
    leafEnergySum Ms F H z = (∑ e ∈ leafEdges Ms z, edgeTerm F H e)/2 := by
  unfold leafEnergySum
  simp_rw [leafClique_eq_valid_sum F H _ hF]
  rw [← Finset.sum_div]
  congr 1
  rw [leafEdges, Finset.sum_image (leafEdgeState_injective Ms z)]
  unfold leafEdgeCodes
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  rfl

def IntegerExchangeAdjacent {C : Type*} [DecidableEq C] (X Y : C → ℕ) : Prop :=
  ∃ (D : C → ℕ) (i j : C), i ≠ j ∧ 0 < D i ∧ 0 < D j ∧
    X=removeOne D i ∧ Y=removeOne D j

noncomputable def integerGraphEnergy {C : Type*} [DecidableEq C]
    (V : Finset (C → ℕ)) (F H : (C → ℕ) → ℝ) : ℝ :=
  (∑ e ∈ (V ×ˢ V).filter (fun e => IntegerExchangeAdjacent e.1 e.2), edgeTerm F H e)/2

noncomputable def leafVertices {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) : Finset (Coordinates I Ms → ℕ) :=
  Finset.univ.biUnion (fun a : Assignments Ms =>
    (Finset.univ.filter (fun i => 0 < embedding Ms z a i)).image
      (fun i => removeOne (embedding Ms z a) i))

lemma leafEdges_states_adjacent {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (z : I → ℕ) (e : (Coordinates I Ms → ℕ) × (Coordinates I Ms → ℕ))
    (he : e ∈ leafEdges Ms z) :
    e.1 ∈ leafVertices Ms z ∧ e.2 ∈ leafVertices Ms z ∧ IntegerExchangeAdjacent e.1 e.2 := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hi,hj,hij⟩ := (Finset.mem_filter.mp ha).2
  have hv (i : Coordinates I Ms) (h : 0 < embedding Ms z a.1 i) :
      removeOne (embedding Ms z a.1) i ∈ leafVertices Ms z := by
    apply Finset.mem_biUnion.mpr
    refine ⟨a.1,Finset.mem_univ _,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  exact ⟨hv _ hi,hv _ hj,embedding Ms z a.1,a.2.1,a.2.2,hij,hi,hj,rfl,rfl⟩

/-- The full exchange graph may contain further edges; their energies
are nonnegative. Every leaf edge occurs once in this graph. -/
theorem leafEnergySum_le_graphEnergy {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ)
    (hF : ∀ x, 0 ≤ F x) (V : Finset (Coordinates I Ms → ℕ))
    (hV : leafVertices Ms z ⊆ V) :
    leafEnergySum Ms F H z ≤ integerGraphEnergy V F H := by
  rw [leafEnergySum_eq_edges Ms F H z hF]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨hx,hy,hadj⟩ := leafEdges_states_adjacent Ms z e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hV hx,hV hy⟩,hadj⟩
  · intro e _ _
    exact mul_nonneg (le_min (hF _) (hF _)) (sq_nonneg _)

theorem recursiveEnergy_le_graphEnergy {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ)
    (hF : ∀ x, 0 ≤ F x) (V : Finset (Coordinates I Ms → ℕ))
    (hV : leafVertices Ms z ⊆ V) :
    recursiveEnergy Ms F H z h ≤ integerGraphEnergy V F H := by
  rw [recursiveEnergy_eq_leafEnergySum]
  exact leafEnergySum_le_graphEnergy Ms F H z hF V hV

end ContingencyTables.IntegerWeightedTransport

end OAI
