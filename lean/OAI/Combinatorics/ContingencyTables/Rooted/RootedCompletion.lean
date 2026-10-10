import OAI.Combinatorics.ContingencyTables.Transport.GraphCompletionUnique
import OAI.Combinatorics.ContingencyTables.Transport.FiniteGraphRoots

namespace OAI

/-! # Forest completion with an explicit component-root selector

Only reachability and constancy on each component are needed for the
integral completion. Making these data explicit permits the executed
least-root selector to replace the original quotient representative,
without asserting that two different selectors are equal.
-/

namespace ContingencyTables.RootedCompletion

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestCut ForestCapacity MaximumForest

variable {V : Type*}

structure Selection (G : SimpleGraph V) where
  root : V → V
  reachable : ∀ v,G.Reachable v (root v)
  constant : ∀ {u v},G.Reachable u v → root u=root v

lemma Selection.idempotent {G : SimpleGraph V} (S : Selection G) (v : V) :
    S.root (S.root v)=S.root v := (S.constant (S.reachable v)).symm

noncomputable def original (G : SimpleGraph V) : Selection G where
  root := componentRoot G
  reachable := componentRoot_reachable G
  constant := componentRoot_constant G

def canonical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Selection G where
  root := FiniteGraphRoots.root G
  reachable := FiniteGraphRoots.root_reachable G
  constant := FiniteGraphRoots.root_constant G

def Selection.map {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (S : Selection G) (e : G ≃g H) : Selection H where
  root v := e (S.root (e.symm v))
  reachable v := by
    have h := (S.reachable (e.symm v)).map e.toHom
    change H.Reachable (e (e.symm v)) (e (S.root (e.symm v))) at h
    simpa only [RelIso.apply_symm_apply] using h
  constant h := congrArg e (S.constant (h.map e.symm.toHom))

/-- The concrete row-then-column vertex order of the contingency graph. -/
def rowColumn {m n : ℕ} (T : SimpleGraph (Fin m⊕Fin n)) [DecidableRel T.Adj] :
    Selection T :=
  (canonical (T.comap finSumFinEquiv.symm)).map (Iso.comap finSumFinEquiv.symm T)

lemma rowColumn_root {m n : ℕ} (T : SimpleGraph (Fin m⊕Fin n)) [DecidableRel T.Adj]
    (v : Fin m⊕Fin n) :
    (rowColumn T).root v=finSumFinEquiv.symm
      (FiniteGraphRoots.root (T.comap finSumFinEquiv.symm) (finSumFinEquiv v)) := rfl

noncomputable def path {G : SimpleGraph V} (S : Selection G) (v : V) : G.Walk v (S.root v) :=
  Classical.choice (S.reachable v)

variable [Fintype V]

noncomputable def flow {G : SimpleGraph V} (S : Selection G) (r : V → ℤ) (a b : V) : ℤ :=
  ∑ v,r v*walkFlow (path S v) a b

lemma flow_skew {G : SimpleGraph V} (S : Selection G) (r : V → ℤ) (a b : V) :
    flow S r a b= -flow S r b a := by
  unfold flow
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [walkFlow_skew,mul_neg]

lemma flow_supported {G : SimpleGraph V} (S : Selection G) (r : V → ℤ)
    (a b : V) (hab : ¬G.Adj a b) : flow S r a b=0 := by
  unfold flow
  apply Finset.sum_eq_zero
  intro v _
  rw [walkFlow_supported _ a b hab,mul_zero]

theorem flow_divergence_all {G : SimpleGraph V} (S : Selection G) (r : V → ℤ) (a : V) :
    (∑ b,flow S r a b)=r a-∑ v,if S.root v=a then r v else 0 := by
  unfold flow
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,walkFlow_sum,mul_sub,Finset.sum_sub_distrib]
  simp [mul_ite,eq_comm]

theorem flow_divergence {G : SimpleGraph V} (S : Selection G) (r : V → ℤ)
    (a : V) (ha : a≠S.root a) : (∑ b,flow S r a b)=r a := by
  have hroot : ∀ v,S.root v≠a := by
    intro v hv
    have h := S.idempotent v
    rw [hv] at h
    exact ha h.symm
  rw [flow_divergence_all]
  simp only [hroot,ite_false,Finset.sum_const_zero,sub_zero]

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] in
noncomputable def table (T : SimpleGraph (I⊕J)) (S : Selection T)
    (r : I → ℤ) (c : J → ℤ) (i : I) (j : J) : ℤ :=
  flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inr j)

omit [Fintype V] in
lemma table_supported (T : SimpleGraph (I⊕J)) (S : Selection T)
    (r : I → ℤ) (c : J → ℤ) (i : I) (j : J) (h : ¬T.Adj (.inl i) (.inr j)) :
    table T S r c i j=0 := flow_supported S _ _ _ h

omit [Fintype V] in
lemma table_row (small : I → J → Bool) (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hT : T≤cellGraph small) (r : I → ℤ) (c : J → ℤ) (i : I)
    (hi : Sum.inl i≠S.root (.inl i)) : (∑ j,table T S r c i j)=r i := by
  have hs := flow_divergence S (Sum.elim r (fun j => -c j)) (.inl i) hi
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ i',flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply flow_supported
    intro h
    exact hT h
  simpa only [hz,zero_add,Sum.elim_inl,table] using hs

omit [Fintype V] in
lemma table_column (small : I → J → Bool) (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hT : T≤cellGraph small) (r : I → ℤ) (c : J → ℤ) (j : J)
    (hj : Sum.inr j≠S.root (.inr j)) : (∑ i,table T S r c i j)=c j := by
  have hs := flow_divergence S (Sum.elim r (fun j => -c j)) (.inr j) hj
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ j',flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply flow_supported
    intro h
    exact hT h
  have hskew : (∑ i,flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i,table T S r c i j) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact flow_skew S _ _ _
  simpa only [hz,add_zero,Sum.elim_inr,hskew,neg_inj] using hs

omit [Fintype V] in
theorem zero_of_nonroot_sums (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hT : T.IsAcyclic) (z : I → J → ℝ)
    (hsupport : ∀ i j,¬T.Adj (.inl i) (.inr j) → z i j=0)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) → (∑ j,z i j)=0)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) → (∑ i,z i j)=0) :
    ∀ i j,z i j=0 := by
  intro i₀ j₀
  by_cases ht : T.Adj (.inl i₀) (.inr j₀)
  · let t : Sym2 (I⊕J) := s(Sum.inl i₀,Sum.inr j₀)
    let D := T.deleteEdges {t}
    let root := S.root (.inl i₀)
    obtain ⟨v,hv,hroot,hcross⟩ := exists_root_avoiding_side T hT ht root
      (S.reachable (.inl i₀)).symm
    let rowU : I → Bool := fun i => side D v (.inl i)
    let colU : J → Bool := fun j => side D v (.inr j)
    have hcross' : rowU i₀≠colU j₀ := hcross
    have hnonroot : ∀ a : I⊕J,side D v a=true → a≠S.root a := by
      intro a ha he
      have hva : D.Reachable v a := by simpa only [side,decide_eq_true_eq] using ha
      have hcomp := hv.trans (hva.mono (T.deleteEdges_le {t}))
      have hsame : S.root a=root := by
        rw [←S.constant hcomp,S.idempotent]
      have haroot : a=root := he.trans hsame
      have hbad : side D v root=true := by simpa only [haroot] using ha
      exact Bool.false_ne_true (hroot.symm.trans hbad)
    let f : I×J → ℝ := fun a => cutTerm (fun _ _ => false) rowU colU 0 0 z 0 a.1 a.2
    have hsum : (∑ a,f a)=0 := by
      rw [Fintype.sum_prod_type]
      apply cut_sum_zero
      · intro i hi
        simpa only [rowDifference,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero]
          using hr i (hnonroot (.inl i) hi)
      · intro j hj
        simpa only [columnDifference,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero]
          using hc j (hnonroot (.inr j) hj)
    have hother : ∀ a : I×J,a≠(i₀,j₀) → f a=0 := by
      rintro ⟨i,j⟩ hne
      by_cases hij : T.Adj (.inl i) (.inr j)
      · have he : rowU i=colU j := side_eq_of_tree_edge T t v hij
          (fun h => hne (cell_edge_injective h))
        simp [f,cutTerm,he]
      · simp [f,cutTerm,hsupport i j hij]
    have hisolate : (∑ a,f a)=f (i₀,j₀) := by
      apply Finset.sum_eq_single (i₀,j₀)
      · intro a _ hne
        exact hother a hne
      · simp
    rw [hisolate] at hsum
    have habs : |f (i₀,j₀)|=|z i₀ j₀| := by
      simp only [f,cutTerm,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero,
        abs_mul,abs_indicator_sub hcross',one_mul]
    rw [hsum,abs_zero] at habs
    exact abs_eq_zero.mp habs.symm
  · exact hsupport i₀ j₀ ht

omit [Fintype V] in
theorem table_unique (small : I → J → Bool) (T : SimpleGraph (I⊕J)) (S : Selection T)
    (hTG : T≤cellGraph small) (hT : T.IsAcyclic) (r : I → ℤ) (c : J → ℤ)
    (z : I → J → ℤ)
    (hsupport : ∀ i j,¬T.Adj (.inl i) (.inr j) → z i j=0)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) → (∑ j,z i j)=r i)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) → (∑ i,z i j)=c j) :
    z=table T S r c := by
  let delta : I → J → ℝ := fun i j => (z i j:ℝ)-table T S r c i j
  have hz := zero_of_nonroot_sums T S hT delta (by
    intro i j hij
    simp only [delta,hsupport i j hij,Int.cast_zero,table_supported T S r c i j hij,sub_self])
    (by
      intro i hi
      dsimp only [delta]
      rw [Finset.sum_sub_distrib,←Int.cast_sum,←Int.cast_sum,
        hr i hi,table_row small T S hTG r c i hi,sub_self])
    (by
      intro j hj
      dsimp only [delta]
      rw [Finset.sum_sub_distrib,←Int.cast_sum,←Int.cast_sum,
        hc j hj,table_column small T S hTG r c j hj,sub_self])
  funext i j
  exact_mod_cast (sub_eq_zero.mp (hz i j))

omit [Fintype V] in
theorem table_original (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (hT : T.IsAcyclic) (r : I → ℤ) (c : J → ℤ) :
    table T (original T) r c=tableCompletion T r c :=
  GraphCompletionUnique.tableCompletion_unique small T hTG hT r c _
    (table_supported T (original T) r c)
    (table_row small T (original T) hTG r c)
    (table_column small T (original T) hTG r c)

end ContingencyTables.RootedCompletion

end OAI
