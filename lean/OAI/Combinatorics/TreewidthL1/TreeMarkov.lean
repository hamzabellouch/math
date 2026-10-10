import OAI.Combinatorics.TreewidthL1.TreeParticles

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3

namespace BoundedTreewidthL1.TreeMarkov
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- A symmetric edge interaction; nonedge values are irrelevant. -/
abbrev Symmetric (R : (i j : I) → A i → A j → ℝ) : Prop :=
  ∀ i j a b, R i j a b = R j i b a

noncomputable def edgeFactor (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (x : (i : I) → A i) : Sym2 I → ℝ :=
  Sym2.lift ⟨fun i j => R i j (x i) (x j), fun i j => hs i j (x i) (x j)⟩

noncomputable def density (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : I) → A i) : ℝ :=
  (∏ i, μ i (x i)) * ∏ e ∈ T.edgeFinset, edgeFactor A R hs x e

/-- The exact local normalization needed for junction gluing. At zero-mass
states no conditional probability is required. -/
def Normalized (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) : Prop :=
  (∀ i a, 0 ≤ μ i a) ∧ (∀ i, (∑ a, μ i a) = 1) ∧
  (∀ i j, T.Adj i j → ∀ a b, 0 ≤ R i j a b) ∧
  ∀ i j, T.Adj i j → ∀ a, μ i a ≠ 0 →
    (∑ b, μ j b * R i j a b) = 1

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

@[simp] lemma edgeFactor_mk
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (x : (i : I) → A i) (i j : I) :
    edgeFactor A R hs x s(i,j) = R i j (x i) (x j) := rfl

lemma density_nonneg (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A T μ R) (x : (i : I) → A i) :
    0 ≤ density A T μ R hs x := by
  apply mul_nonneg (Finset.prod_nonneg (fun i _ => hn.1 i (x i)))
  apply Finset.prod_nonneg
  intro e he
  induction e using Sym2.ind with
  | _ i j => exact hn.2.2.1 i j (by simpa using he) (x i) (x j)

lemma density_zero
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : I) → A i) (i : I) (hi : μ i (x i) = 0) :
    density A T μ R hs x = 0 := by
  have hz : (∏ j, μ j (x j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  simp [density, hz]

lemma edgeFinset_leaf (T : SimpleGraph I) {l p : I} (hlp : T.Adj l p)
    (hp : ∀ j, T.Adj l j → j = p) :
    T.edgeFinset = insert s(l,p)
      ((T.induce {i | i ≠ l}).edgeFinset.map
        (Function.Embedding.subtype (fun i => i ≠ l)).sym2Map) := by
  erw [SimpleGraph.map_edgeFinset_induce (s := {i | i ≠ l}) (G := T)]
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    simp only [Finset.mem_insert, Finset.mem_inter, SimpleGraph.mem_edgeFinset,
      Finset.mk_mem_sym2_iff, Set.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro hij
      by_cases hi : i = l
      · subst i
        left
        rw [hp j hij]
      · by_cases hj : j = l
        · subst j
          left
          rw [hp i hij.symm, Sym2.eq_swap]
        · exact Or.inr ⟨hij, hi, hj⟩
    · rintro (he | ⟨hij, _, _⟩)
      · have : s(i,j) ∈ T.edgeSet := he ▸ hlp
        exact this
      · exact hij

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

@[simp] lemma edgeFactor_induce
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (S : Set I)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : I) → A i) (e : Sym2 S) :
    edgeFactor A R hs x (Sym2.map Subtype.val e) =
      edgeFactor (fun i : S => A i) (fun i j => R i j)
        (fun i j => hs i j) (fun i => x i) e := by
  induction e using Sym2.ind with
  | _ i j => rfl

lemma density_leaf (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    {l p : I} (hlp : T.Adj l p) (hp : ∀ j, T.Adj l j → j = p)
    (x : (i : I) → A i) :
    density A T μ R hs x =
      density (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
        (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) (fun i => x i) *
      (μ l (x l) * R p l (x p) (x l)) := by
  have hnot : s(l,p) ∉ ((T.induce {i | i ≠ l}).edgeFinset.map
      (Function.Embedding.subtype (fun i => i ≠ l)).sym2Map) := by
    erw [SimpleGraph.map_edgeFinset_induce (s := {i | i ≠ l}) (G := T)]
    simp
  unfold density
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => μ i (x i)) l,
    edgeFinset_leaf T hlp hp, Finset.prod_insert hnot, Finset.prod_map]
  simp only [edgeFactor_mk]
  have hm : (∏ e ∈ (T.induce {i | i ≠ l}).edgeFinset,
      edgeFactor A R hs x ((Function.Embedding.subtype (fun i => i ≠ l)).sym2Map e)) =
      ∏ e ∈ (T.induce {i | i ≠ l}).edgeFinset,
        edgeFactor (fun i : {i // i ≠ l} => A i) (fun i j => R i j)
          (fun i j => hs i j) (fun i => x i) e := by
    apply Finset.prod_congr rfl
    intro e _
    exact edgeFactor_induce A {i | i ≠ l} R hs x e
  erw [hm]
  rw [hs l p]
  ring_nf
  congr 1

@[simp] lemma splitAt_here
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (l : I) (a : A l) (x : (i : {i // i ≠ l}) → A i) :
    (Equiv.piSplitAt l A).symm (a,x) l = a := by
  simp [Equiv.piSplitAt_symm_apply]

@[simp] lemma splitAt_away
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (l : I) (a : A l) (x : (i : {i // i ≠ l}) → A i)
    (i : I) (hi : i ≠ l) :
    (Equiv.piSplitAt l A).symm (a,x) i = x ⟨i,hi⟩ := by
  simp [Equiv.piSplitAt_symm_apply, hi]

lemma splitAt_restrict (l : I) (a : A l) (x : (i : {i // i ≠ l}) → A i) :
    (fun i : {i // i ≠ l} => (Equiv.piSplitAt l A).symm (a,x) i) = x := by
  funext i
  exact splitAt_away A l a x i i.property

lemma sum_leaf_density (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A T μ R)
    {l p : I} (hlp : T.Adj l p) (hp : ∀ j, T.Adj l j → j = p)
    (x : (i : {i // i ≠ l}) → A i) :
    (∑ a, density A T μ R hs ((Equiv.piSplitAt l A).symm (a,x))) =
      density (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
        (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) x := by
  have hpne : p ≠ l := hlp.ne.symm
  let p' : {i // i ≠ l} := ⟨p,hpne⟩
  simp_rw [density_leaf A T μ R hs hlp hp, splitAt_restrict,
    splitAt_here, splitAt_away A l _ x p hpne]
  rw [← Finset.mul_sum]
  by_cases hz : μ p (x p') = 0
  · have hd := density_zero (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
      (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) x p' hz
    rw [hd, zero_mul]
  · rw [hn.2.2.2 p l hlp.symm (x p') hz, mul_one]

lemma expectation_leaf (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A T μ R)
    {l p : I} (hlp : T.Adj l p) (hp : ∀ j, T.Adj l j → j = p)
    (f : ((i : {i // i ≠ l}) → A i) → ℝ) :
    (∑ x, density A T μ R hs x * f (fun i : {i // i ≠ l} => x i)) =
      ∑ x, density (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
        (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) x * f x := by
  rw [← (Equiv.piSplitAt l A).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [splitAt_restrict, ← Finset.sum_mul,
    sum_leaf_density A T μ R hs hn hlp hp]

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

lemma Normalized.induce {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]
    {T : SimpleGraph I} {μ : (i : I) → A i → ℝ}
    {R : (i j : I) → A i → A j → ℝ} (hn : Normalized A T μ R) (S : Set I) :
    Normalized (fun i : S => A i) (T.induce S) (fun i => μ i) (fun i j => R i j) := by
  exact ⟨fun i => hn.1 i, fun i => hn.2.1 i,
    fun i j hij => hn.2.2.1 i j hij, fun i j hij => hn.2.2.2 i j hij⟩

private theorem node_marginal_card (n : ℕ) :
    ∀ {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]
      (T : SimpleGraph I), Fintype.card I = n → T.IsTree →
      ∀ (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
        (hs : Symmetric A R), Normalized A T μ R →
        ∀ i a, (∑ x, if x i = a then density A T μ R hs x else 0) = μ i a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I _ A _ T hn hT μ R hs hnorm i a
    by_cases hsmall : Fintype.card I ≤ 1
    · let : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hsmall
      let : Unique I := ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩
      have hbot : T = ⊥ := Subsingleton.elim _ _
      have hd (x : (j : I) → A j) : density A T μ R hs x = μ i (x i) := by
        have he : T.edgeFinset = ∅ := by
          ext e
          induction e using Sym2.ind with
          | _ j k =>
            simp [Subsingleton.elim k j]
        simp only [density, he, Finset.prod_empty, mul_one, Fintype.prod_unique]
        rfl
      rw [← (Equiv.piUnique A).symm.sum_comp]
      simp [hd, Equiv.piUnique, uniqueElim]
    · let : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (lt_of_not_ge hsmall)
      obtain ⟨u,v,huv,hu,hv⟩ := hT.exists_ne_and_degree_eq_one
      have hex : ∃ l : I, l ≠ i ∧ T.degree l = 1 := by
        by_cases hui : u = i
        · exact ⟨v, fun hvi => huv (hui.trans hvi.symm), hv⟩
        · exact ⟨u,hui,hu⟩
      obtain ⟨l,hli,hl⟩ := hex
      obtain ⟨p,hlp,hp⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hl
      let S : Set I := {j | j ≠ l}
      have hT' : (T.induce S).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hl, hT.isAcyclic.induce S⟩
      have hc : Fintype.card S < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (p := fun j => j ∈ S) (x := l) (by simp [S])
      let i' : S := ⟨i,hli.symm⟩
      have hi := ih (Fintype.card S) hc (fun j : S => A j) (T.induce S) rfl hT'
        (fun j => μ j) (fun j k => R j k) (fun j k => hs j k) (hnorm.induce S) i' a
      have he := expectation_leaf A T μ R hs hnorm hlp hp
        (fun x => if x i' = a then (1:ℝ) else 0)
      simp only [mul_ite, mul_one, mul_zero] at he
      apply he.trans
      convert hi using 1
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      congr 1

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- Canonical root-independent tree density and exact one-node marginals.
Zero-mass states, deterministic edges and arbitrary finite state spaces allowed. -/
theorem tree_density (T : SimpleGraph I) (hT : T.IsTree)
    (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (hn : Normalized A T μ R) :
    (∀ x, 0 ≤ density A T μ R hs x) ∧
    (∑ x, density A T μ R hs x) = 1 ∧
    ∀ i a, (∑ x, if x i = a then density A T μ R hs x else 0) = μ i a := by
  have hm := node_marginal_card (Fintype.card I) A T rfl hT μ R hs hn
  refine ⟨density_nonneg A T μ R hs hn, ?_, hm⟩
  obtain ⟨i⟩ := hT.connected.nonempty
  have ht : (∑ a : A i, ∑ x, if x i = a then density A T μ R hs x else 0) =
      ∑ x, density A T μ R hs x := by
    rw [Finset.sum_comm]
    simp
  rw [← ht]
  simp only [hm]
  exact hn.2.1 i

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

lemma tree_path_mem_connected {I : Type*} (T : SimpleGraph I) (hT : T.IsTree)
    {S : Set I} (hS : (T.induce S).Connected) {a b v : I}
    (ha : a ∈ S) (hb : b ∈ S) (q : T.Walk a b) (hq : q.IsPath)
    (hv : v ∈ q.support) : v ∈ S := by
  obtain ⟨p, hp⟩ := hS.exists_isPath ⟨a, ha⟩ ⟨b, hb⟩
  let f := (SimpleGraph.Embedding.induce (G := T) S).toHom
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  have heq : p.map f = q := congrArg Subtype.val
    ((hT.isAcyclic.subsingleton_path a b).elim ⟨p.map f, hp'⟩ ⟨q, hq⟩)
  have hmem : v ∈ (p.map f).support := heq.symm ▸ hv
  rw [SimpleGraph.Walk.support_map] at hmem
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hmem
  exact hz ▸ z.property

/-- A proper connected subtree can be pruned from outside without altering it. -/
lemma exists_leaf_outside {I : Type*} [Fintype I] (T : SimpleGraph I) (hT : T.IsTree)
    (S : Set I) (hc : (T.induce S).Connected) (hproper : S ≠ Set.univ) :
    ∃ l : I, l ∉ S ∧ T.degree l = 1 := by
  obtain ⟨⟨r, hr⟩⟩ := hc.nonempty
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra hn
    apply hproper
    ext v
    simp only [Set.mem_univ, iff_true]
    by_contra hv
    exact hn ⟨v,hv⟩
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath r v
  let lengths : Set ℕ := {n | ∃ (l : I) (q : T.Walk r l),
    q.IsPath ∧ v ∈ q.support ∧ q.length = n}
  have hfin : lengths.Finite := Set.Finite.subset
    (Set.finite_le_nat (Fintype.card I)) (fun n ⟨l,q,hq,_,heq⟩ => heq ▸ hq.length_lt.le)
  obtain ⟨n, ⟨⟨l,q,hq,hvq,heq⟩, hmax⟩⟩ := hfin.exists_maximal
    ⟨p.length, ⟨v,p,hp,p.end_mem_support,rfl⟩⟩
  have hl : l ∉ S := fun hls => hv (tree_path_mem_connected T hT hc hr hls q hq hvq)
  have hnil : ¬ q.Nil := by
    intro hnil
    exact hl (hq.nil_iff_eq.mp hnil ▸ hr)
  refine ⟨l,hl,SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    ⟨q.penultimate, (q.adj_penultimate hnil).symm, ?_⟩⟩
  intro w hadj
  apply hT.isAcyclic.eq_penultimate_of_adj_end hq hadj
  by_contra hn
  have hqc : (q.concat hadj).IsPath := hq.concat hn hadj
  have hvc : v ∈ (q.concat hadj).support := by
    simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
    exact Or.inl hvq
  have hm := hmax ⟨w,q.concat hadj,hqc,hvc,rfl⟩
  have he : (q.concat hadj).length = q.length + 1 := q.length_concat hadj
  omega

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

lemma edgeFinset_comap_equiv {I J : Type*} [Fintype I] [Fintype J]
    (T : SimpleGraph I) (e : J ≃ I) :
    T.edgeFinset = (T.comap e).edgeFinset.map e.toEmbedding.sym2Map := by
  have hg : (T.comap e).map e.toEmbedding = T := by
    ext i j
    simp only [SimpleGraph.map_adj]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      subst i
      subst j
      exact hab
    · intro hij
      exact ⟨e.symm i,e.symm j,by simpa using hij,e.apply_symm_apply i,e.apply_symm_apply j⟩
  have he := SimpleGraph.edgeFinset_map e.toEmbedding (T.comap e)
  calc
    T.edgeFinset = ((T.comap e).map e.toEmbedding).edgeFinset := by
      ext z
      simp only [SimpleGraph.mem_edgeFinset]

      rw [hg]
    _ = _ := he

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

lemma density_equiv
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    {J : Type*} [Fintype J] (e : J ≃ I) (x : (i : I) → A i) :
    density A T μ R hs x =
      density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) (fun j => x (e j)) := by
  unfold density
  rw [← e.prod_comp (fun i => μ i (x i)), edgeFinset_comap_equiv T e,
    Finset.prod_map]
  congr 1
  apply Finset.prod_congr rfl
  intro z hz
  induction z using Sym2.ind with
  | _ i j => rfl

lemma expectation_surjective (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    {J : Type*} [Fintype J] (e : J ↪ I) (he : Function.Surjective e)
    (f : ((j : J) → A (e j)) → ℝ) :
    (∑ x, density A T μ R hs x * f (fun j => x (e j))) =
      ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x := by
  let E : J ≃ I := Equiv.ofBijective e ⟨e.injective,he⟩
  calc
    _ = ∑ x : (i : I) → A i, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k))
          (fun j => x (e j)) * f (fun j => x (e j)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [density_equiv A T μ R hs E x]
      rfl
    _ = _ := by
      have hfun (x : (i : I) → A i) :
          (Equiv.piCongrLeft A E).symm x = (fun j => x (e j)) := by
        funext j
        exact Equiv.piCongrLeft_symm_apply A E x j
      have hv := (Equiv.piCongrLeft A E).symm.sum_comp
        (fun x => density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
          (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x)
      simp_rw [hfun] at hv
      convert hv using 1 ; apply Finset.sum_congr
        (by ext x; constructor <;> intro _ <;> exact Finset.mem_univ _) ;
        intro x hx ; rfl

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

private theorem expectation_comap_card (n : ℕ) :
    ∀ {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]
      (T : SimpleGraph I), Fintype.card I = n → T.IsTree →
      ∀ (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
        (hs : Symmetric A R), Normalized A T μ R →
      ∀ {J : Type*} [Fintype J] (e : J ↪ I), (T.comap e).Connected →
      ∀ (f : ((j : J) → A (e j)) → ℝ),
      (∑ x, density A T μ R hs x * f (fun j => x (e j))) =
        ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
          (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I _ A _ T hn hT μ R hs hnorm J _ e hc f
    by_cases he : Function.Surjective e
    · exact expectation_surjective A T μ R hs e he f
    · have hc' : (T.induce (Set.range e)).Connected := by
        let hom : T.comap e →g T.induce (Set.range e) :=
          ⟨fun j => ⟨e j, ⟨j,rfl⟩⟩, fun h => h⟩
        apply hc.map hom
        rintro ⟨i,j,rfl⟩
        exact ⟨j,rfl⟩
      obtain ⟨l,hl,hd⟩ := exists_leaf_outside T hT (Set.range e) hc'
        (fun h => he (Set.range_eq_univ.mp h))
      obtain ⟨p,hlp,hp⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
      let K : Type _ := {i : I // i ≠ l}
      let e' : J ↪ K := ⟨fun j => ⟨e j, fun h => hl ⟨j,h⟩⟩,
        fun _ _ h => e.injective (congrArg Subtype.val h)⟩
      have hT' : (T.induce {i | i ≠ l}).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hd,
          hT.isAcyclic.induce _⟩
      have hcard : Fintype.card K < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (p := fun i => i ≠ l) (x := l) (by simp)
      have hnew := ih (Fintype.card K) hcard (fun i : K => A i)
        (T.induce {i | i ≠ l}) rfl hT' (fun i => μ i) (fun i j => R i j)
        (fun i j => hs i j) (hnorm.induce _) e' hc f
      have hold := expectation_leaf A T μ R hs hnorm hlp hp
        (fun x => f (fun j => x (e' j)))
      apply hold.trans
      convert hnew using 1 <;>
        apply Finset.sum_congr (by ext; simp) <;>
        intro x hx <;> congr 1

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- Exact connected-subtree marginal of the canonical junction law. In particular
this applies to a simple bag path, before projection to intersection assignments. -/
theorem expectation_comap (T : SimpleGraph I) (hT : T.IsTree)
    (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (hn : Normalized A T μ R)
    {J : Type*} [Fintype J] (e : J ↪ I) (hc : (T.comap e).Connected)
    (f : ((j : J) → A (e j)) → ℝ) :
    (∑ x, density A T μ R hs x * f (fun j => x (e j))) =
      ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x := by
  exact expectation_comap_card (Fintype.card I) A T rfl hT μ R hs hn e hc f

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- Interaction constructed from the actual local pair mass, not assumed. -/
noncomputable def interaction (μ : (i : I) → A i → ℝ)
    (J : (i j : I) → A i → A j → ℝ) (i j : I) (a : A i) (b : A j) : ℝ :=
  J i j a b / (μ i a * μ j b)

lemma interaction_symmetric
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (μ : (i : I) → A i → ℝ)
    (J : (i j : I) → A i → A j → ℝ) (hJ : Symmetric A J) :
    Symmetric A (interaction A μ J) := by
  intro i j a b
  simp only [interaction, hJ i j a b, mul_comm]

lemma interaction_normalized
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (T : SimpleGraph I)
    (μ : (i : I) → A i → ℝ) (J : (i j : I) → A i → A j → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hs : Symmetric A J)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, (∑ b, J i j a b) = μ i a) :
    Normalized A T μ (interaction A μ J) := by
  refine ⟨hμ,hμ₁,?_,?_⟩
  · intro i j hij a b
    exact div_nonneg (hJ i j hij a b) (mul_nonneg (hμ i a) (hμ j b))
  · intro i j hij a ha
    have hz (b : A j) (hb : μ j b = 0) : J i j a b = 0 := by
      have he := hrow j i hij.symm b
      rw [hb] at he
      have hz' : J j i b a = 0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => hJ j i hij.symm b c)).mp he a (Finset.mem_univ _)
      rw [hs i j a b]
      exact hz'
    calc
      _ = ∑ b, J i j a b / μ i a := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hb' : μ j b = 0
        · simp [interaction, hb', hz b hb']
        · dsimp [interaction]
          field_simp
      _ = (∑ b, J i j a b) / μ i a := (Finset.sum_div _ _ _).symm
      _ = 1 := by rw [hrow i j hij a, div_self ha]

/-- Canonical tree law from genuinely consistent adjacent pair distributions.
No positive lower bound on local state probabilities is imposed. -/
theorem coupling_tree (T : SimpleGraph I) (hT : T.IsTree)
    (μ : (i : I) → A i → ℝ) (J : (i j : I) → A i → A j → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hs : Symmetric A J)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, (∑ b, J i j a b) = μ i a) :
    let R := interaction A μ J
    let hR := interaction_symmetric A μ J hs
    (∀ x, 0 ≤ density A T μ R hR x) ∧
    (∑ x, density A T μ R hR x) = 1 ∧
    (∀ i a, (∑ x, if x i = a then density A T μ R hR x else 0) = μ i a) ∧
    ∀ {K : Type*} [Fintype K] (e : K ↪ I), (T.comap e).Connected →
      ∀ (f : ((j : K) → A (e j)) → ℝ),
      (∑ x, density A T μ R hR x * f (fun j => x (e j))) =
        ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
          (fun j k => R (e j) (e k)) (fun j k => hR (e j) (e k)) x * f x := by
  dsimp only
  have hn := interaction_normalized A T μ J hμ hμ₁ hs hJ hrow
  obtain ⟨hnon,hprob,hmarg⟩ := tree_density A T hT μ (interaction A μ J)
    (interaction_symmetric A μ J hs) hn
  refine ⟨hnon,hprob,hmarg,?_⟩
  intro K _ e hc f
  exact expectation_comap A T hT μ (interaction A μ J)
    (interaction_symmetric A μ J hs) hn e hc f
end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.MarkovFlow
abbrev History {r : ℕ} (L : Fin (r + 1) → Type*) := (i : Fin (r + 1)) → L i
/-- Same finite stochastic-product definition as the exact CKR obligation. -/
def IsMarkovLaw {r : ℕ} (L : Fin (r + 1) → Type*) [∀ i, Fintype (L i)]
    (μ : History L → ℝ) : Prop :=
  ∃ p : L 0 → ℝ, ∃ K : (i : Fin r) → L i.castSucc → L i.succ → ℝ,
    (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
    (∀ i a b, 0 ≤ K i a b) ∧ (∀ i a, (∑ b, K i a b) = 1) ∧
    ∀ x, μ x = p (x 0) * ∏ i : Fin r, K i (x i.castSucc) (x i.succ)
end BoundedTreewidthL1.MarkovFlow

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {r : ℕ} (A : Fin (r+1) → Type*) [∀ i, Fintype (A i)]

def pathEdge (n : ℕ) : Fin n ↪ Sym2 (Fin (n+1)) where
  toFun i := s(i.castSucc,i.succ)
  inj' := by
    intro i j he
    rcases Sym2.eq_iff.mp he with h | h
    · apply Fin.ext
      exact congrArg (fun k : Fin (n+1) => k.val) h.1
    · have h₁ := congrArg Fin.val h.1
      have h₂ := congrArg Fin.val h.2
      simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
      omega

lemma path_edges (n : ℕ) :
    (SimpleGraph.pathGraph (n+1)).edgeFinset = Finset.univ.map (pathEdge n) := by
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    rw [SimpleGraph.mem_edgeFinset]
    change (SimpleGraph.pathGraph (n+1)).Adj i j ↔ _
    rw [SimpleGraph.pathGraph_adj]
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases h with h | h
      · refine ⟨⟨i.val,by omega⟩,?_⟩
        change s((⟨i.val,_⟩ : Fin (n+1)),(⟨i.val+1,_⟩ : Fin (n+1))) = s(i,j)
        congr 1
        exact Fin.ext h
      · refine ⟨⟨j.val,by omega⟩,?_⟩
        apply Sym2.eq_iff.mpr
        right
        exact ⟨Fin.ext rfl, Fin.ext h⟩
    · rintro ⟨k,hk⟩
      change s(k.castSucc,k.succ) = s(i,j) at hk
      rcases Sym2.eq_iff.mp hk with hk | hk
      · left
        rw [← hk.1,← hk.2]
        rfl
      · right
        rw [← hk.1,← hk.2]
        rfl

lemma path_density
    {r : ℕ} (A : Fin (r + 1) → Type treewidthLevel1) [(i : Fin (r + 1)) → Fintype (A i)]
    (μ : (i : Fin (r+1)) → A i → ℝ)
    (R : (i j : Fin (r+1)) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : Fin (r+1)) → A i) :
    density A (SimpleGraph.pathGraph (r+1)) μ R hs x =
      (∏ i, μ i (x i)) * ∏ i : Fin r, R i.castSucc i.succ (x i.castSucc) (x i.succ) := by
  rw [density, path_edges, Finset.prod_map]
  rfl

lemma product_factorization (n : ℕ) (m : Fin (n+1) → ℝ)
    (q k : Fin n → ℝ)
    (hk : ∀ i, m i.castSucc ≠ 0 → k i = m i.succ * q i) :
    (∏ i, m i) * (∏ i, q i) = m 0 * ∏ i, k i := by
  induction n with
  | zero => simp
  | succ n ih =>
    let m' : Fin (n+1) → ℝ := fun i => m i.castSucc
    let q' : Fin n → ℝ := fun i => q i.castSucc
    let k' : Fin n → ℝ := fun i => k i.castSucc
    have hk' : ∀ i, m' i.castSucc ≠ 0 → k' i = m' i.succ * q' i := by
      intro i hi
      exact hk i.castSucc hi
    have hih := ih m' q' k' hk'
    rw [Fin.prod_univ_castSucc m, Fin.prod_univ_castSucc q, Fin.prod_univ_castSucc k]
    change ((∏ i, m' i) * m (Fin.last (n+1))) * ((∏ i, q' i) * q (Fin.last n)) =
      m' 0 * ((∏ i, k' i) * k (Fin.last n))
    by_cases hz : m' (Fin.last n) = 0
    · have hprod : (∏ i, m' i) = 0 := Finset.prod_eq_zero (Finset.mem_univ _) hz
      rw [hprod,zero_mul] at hih
      calc
        _ = 0 := by simp [hprod]
        _ = (m' 0 * ∏ i, k' i) * k (Fin.last n) := by rw [← hih,zero_mul]
        _ = _ := by ring
    · have hl := hk (Fin.last n) hz
      rw [hl]
      change ((∏ i, m' i) * m (Fin.last (n+1))) * ((∏ i, q' i) * q (Fin.last n)) =
        m' 0 * ((∏ i, k' i) * (m (Fin.last (n+1)) * q (Fin.last n)))
      calc
        _ = ((∏ i, m' i) * ∏ i, q' i) * (m (Fin.last (n+1)) * q (Fin.last n)) := by ring
        _ = _ := by rw [hih]; ring

/-- The canonical marginal on any simple bag-tree path is an actual Markov
product, not merely a collection of consistent adjacent marginals. -/
theorem path_markov (μ : (i : Fin (r+1)) → A i → ℝ)
    (R : (i j : Fin (r+1)) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A (SimpleGraph.pathGraph (r+1)) μ R) :
    MarkovFlow.IsMarkovLaw A (density A (SimpleGraph.pathGraph (r+1)) μ R hs) := by
  let K : (i : Fin r) → A i.castSucc → A i.succ → ℝ := fun i a b =>
    if μ i.castSucc a = 0 then μ i.succ b else μ i.succ b * R i.castSucc i.succ a b
  have hadj (i : Fin r) : (SimpleGraph.pathGraph (r+1)).Adj i.castSucc i.succ :=
    SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
  refine ⟨μ 0,K,hn.1 0,hn.2.1 0,?_,?_,?_⟩
  · intro i a b
    dsimp [K]
    split_ifs
    · exact hn.1 _ _
    · exact mul_nonneg (hn.1 _ _) (hn.2.2.1 _ _ (hadj i) a b)
  · intro i a
    by_cases ha : μ i.castSucc a = 0
    · simpa [K,ha] using hn.2.1 i.succ
    · simpa [K,ha] using hn.2.2.2 _ _ (hadj i) a ha
  · intro x
    rw [path_density]
    apply product_factorization
    intro i hi
    simp [K,hi]
end BoundedTreewidthL1.TreeMarkov

end OAI
