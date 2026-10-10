import OAI.Combinatorics.ContingencyTables.Rooted.ForestCapacity

namespace OAI

/-!
# Integral completion of actual graph incidence equations

Integral root-path flows give an explicit solution of every nonroot
incidence equation. This works directly on the finite row/column graph,
including disconnected components and singleton components.
-/

namespace ContingencyTables.GraphIntegralCompletion

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V]

omit [Fintype V] in
noncomputable def edgeFlow (u v a b : V) : ℤ :=
  (if u=a ∧ v=b then 1 else 0)-(if u=b ∧ v=a then 1 else 0)

omit [Fintype V] in
lemma edgeFlow_skew (u v a b : V) : edgeFlow u v a b= -edgeFlow u v b a := by
  unfold edgeFlow
  ring

omit [Fintype V] in
lemma edgeFlow_nonadj (G : SimpleGraph V) {u v a b : V}
    (h : G.Adj u v) (hab : ¬G.Adj a b) : edgeFlow u v a b=0 := by
  have hf : ¬(u=a ∧ v=b) := by rintro ⟨rfl,rfl⟩; exact hab h
  have hr : ¬(u=b ∧ v=a) := by rintro ⟨rfl,rfl⟩; exact hab h.symm
  simp only [edgeFlow,hf,hr,ite_false,sub_self]

lemma edgeFlow_sum (u v a : V) :
    (∑ b, edgeFlow u v a b)=(if u=a then (1:ℤ) else 0)-(if v=a then 1 else 0) := by
  simp [edgeFlow,Finset.sum_sub_distrib,ite_and]

omit [Fintype V] in
noncomputable def walkFlow {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (a b : V) : ℤ :=
  (p.darts.map (fun d => edgeFlow d.fst d.snd a b)).sum

omit [Fintype V] in
@[simp] lemma walkFlow_nil (G : SimpleGraph V) (u a b : V) :
    walkFlow (Walk.nil : G.Walk u u) a b=0 := rfl

omit [Fintype V] in
lemma walkFlow_cons {G : SimpleGraph V} {u v w : V} (h : G.Adj u v)
    (p : G.Walk v w) (a b : V) :
    walkFlow (Walk.cons h p) a b=edgeFlow u v a b+walkFlow p a b := by
  simp only [walkFlow,Walk.darts_cons,List.map_cons,List.sum_cons]

omit [Fintype V] in
lemma walkFlow_skew {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (a b : V) :
    walkFlow p a b= -walkFlow p b a := by
  induction p with
  | nil => simp only [walkFlow_nil,neg_zero]
  | cons h p ih => rw [walkFlow_cons,walkFlow_cons,edgeFlow_skew,ih]; ring

omit [Fintype V] in
lemma walkFlow_supported {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (a b : V) (hab : ¬G.Adj a b) : walkFlow p a b=0 := by
  induction p with
  | nil => rfl
  | cons h p ih => rw [walkFlow_cons,edgeFlow_nonadj G h hab,ih,zero_add]

lemma walkFlow_sum {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (a : V) :
    (∑ b, walkFlow p a b)=(if u=a then (1:ℤ) else 0)-(if v=a then 1 else 0) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp_rw [walkFlow_cons]
    rw [Finset.sum_add_distrib,edgeFlow_sum,ih]
    ring

omit [Fintype V] in
noncomputable def componentRoot (G : SimpleGraph V) (v : V) : V :=
  Classical.choose (G.connectedComponentMk v).exists_rep

omit [Fintype V] in
lemma componentRoot_component (G : SimpleGraph V) (v : V) :
    G.connectedComponentMk (componentRoot G v)=G.connectedComponentMk v :=
  Classical.choose_spec (G.connectedComponentMk v).exists_rep

omit [Fintype V] in
lemma componentRoot_reachable (G : SimpleGraph V) (v : V) :
    G.Reachable v (componentRoot G v) :=
  ConnectedComponent.exact (componentRoot_component G v).symm

omit [Fintype V] in
lemma componentRoot_constant (G : SimpleGraph V) {u v : V} (h : G.Reachable u v) :
    componentRoot G u=componentRoot G v := by
  exact congrArg (fun C : G.ConnectedComponent => Classical.choose C.exists_rep)
    (ConnectedComponent.sound h)

omit [Fintype V] in
lemma componentRoot_idempotent (G : SimpleGraph V) (v : V) :
    componentRoot G (componentRoot G v)=componentRoot G v :=
  (componentRoot_constant G (componentRoot_reachable G v)).symm

omit [Fintype V] in
noncomputable def rootPath (G : SimpleGraph V) (v : V) : G.Walk v (componentRoot G v) :=
  Classical.choice (componentRoot_reachable G v)

noncomputable def completionFlow (G : SimpleGraph V) (r : V → ℤ) (a b : V) : ℤ :=
  ∑ v, r v*walkFlow (rootPath G v) a b

lemma completionFlow_skew (G : SimpleGraph V) (r : V → ℤ) (a b : V) :
    completionFlow G r a b= -completionFlow G r b a := by
  unfold completionFlow
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [walkFlow_skew,mul_neg]

lemma completionFlow_supported (G : SimpleGraph V) (r : V → ℤ)
    (a b : V) (hab : ¬G.Adj a b) : completionFlow G r a b=0 := by
  unfold completionFlow
  apply Finset.sum_eq_zero
  intro v _
  rw [walkFlow_supported _ a b hab,mul_zero]

/-- Every prescribed integral nonroot divergence is satisfied exactly.
The chosen roots are the only vertices where a discrepancy can remain. -/
theorem completionFlow_divergence (G : SimpleGraph V) (r : V → ℤ)
    (a : V) (ha : a≠componentRoot G a) : (∑ b, completionFlow G r a b)=r a := by
  have hroot : ∀ v, componentRoot G v≠a := by
    intro v hv
    have h := componentRoot_idempotent G v
    rw [hv] at h
    exact ha h.symm
  unfold completionFlow
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,walkFlow_sum,mul_sub,Finset.sum_sub_distrib]
  simp [hroot,eq_comm]

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [Fintype I] [Fintype J] in
noncomputable def tableFlow (z : I → J → ℤ) : I⊕J → I⊕J → ℤ
  | .inl i,.inr j => z i j
  | .inr j,.inl i => -z i j
  | _,_ => 0

omit [Fintype V] [Fintype I] [Fintype J] in
lemma tableFlow_skew (z : I → J → ℤ) (a b : I⊕J) :
    tableFlow z a b= -tableFlow z b a := by
  cases a <;> cases b <;> simp [tableFlow]

omit [Fintype V] in
lemma tableFlow_row (z : I → J → ℤ) (i : I) :
    (∑ v, tableFlow z (.inl i) v)=∑ j, z i j := by
  simp [Fintype.sum_sum_type,tableFlow]

omit [Fintype V] in
lemma tableFlow_column (z : I → J → ℤ) (j : J) :
    (∑ v, tableFlow z (.inr j) v)= -(∑ i, z i j) := by
  simp [Fintype.sum_sum_type,tableFlow,Finset.sum_neg_distrib]

omit [Fintype V] in
noncomputable def tableCompletion (T : SimpleGraph (I⊕J)) (r : I → ℤ) (c : J → ℤ)
    (i : I) (j : J) : ℤ :=
  completionFlow T (Sum.elim r (fun j => -c j)) (.inl i) (.inr j)

omit [Fintype V] in
lemma tableCompletion_supported (T : SimpleGraph (I⊕J)) (r : I → ℤ) (c : J → ℤ)
    (i : I) (j : J) (h : ¬T.Adj (.inl i) (.inr j)) : tableCompletion T r c i j=0 :=
  completionFlow_supported T _ _ _ h

omit [Fintype V] in
lemma tableCompletion_row (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (r : I → ℤ) (c : J → ℤ) (i : I)
    (hi : Sum.inl i≠componentRoot T (.inl i)) : (∑ j, tableCompletion T r c i j)=r i := by
  have hs := completionFlow_divergence T (Sum.elim r (fun j => -c j)) (.inl i) hi
  rw [Fintype.sum_sum_type] at hs
  have hzero : (∑ i', completionFlow T (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply completionFlow_supported
    intro h
    exact hT h
  simpa only [hzero,zero_add,Sum.elim_inl,tableCompletion] using hs

omit [Fintype V] in
lemma tableCompletion_column (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hT : T≤ForestCapacity.cellGraph small) (r : I → ℤ) (c : J → ℤ) (j : J)
    (hj : Sum.inr j≠componentRoot T (.inr j)) : (∑ i, tableCompletion T r c i j)=c j := by
  have hs := completionFlow_divergence T (Sum.elim r (fun j => -c j)) (.inr j) hj
  rw [Fintype.sum_sum_type] at hs
  have hzero : (∑ j', completionFlow T (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply completionFlow_supported
    intro h
    exact hT h
  have hskew : (∑ i, completionFlow T (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i, tableCompletion T r c i j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact completionFlow_skew T _ _ _
  simp only [hzero,add_zero,Sum.elim_inr,hskew,neg_inj] at hs
  exact hs

end ContingencyTables.GraphIntegralCompletion

end OAI
