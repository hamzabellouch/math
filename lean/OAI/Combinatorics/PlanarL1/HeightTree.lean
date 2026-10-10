import OAI.Combinatorics.PlanarL1.WeightedMetric
import OAI.Combinatorics.PlanarL1.Distance

namespace OAI

section



namespace PlanarL1

/-- A rooted incidence tree with a nondecreasing metric height. Unlike the
shortest-path tree, added terminal branches are permitted to have zero length.
Termination follows the incidence tree, not strict metric height. -/
structure HeightTree (V : Type*) where
  root : V
  parent : V → V
  at_root : parent root = root
  wf : WellFounded (fun u v => v ≠ root ∧ u = parent v)
  height : V → ℝ
  height_mono : ∀ v, height (parent v) ≤ height v

namespace HeightTree
attribute [local instance] Classical.propDecidable
variable {V : Type*} (T : HeightTree V)

abbrev Step (u v : V) : Prop := v ≠ T.root ∧ u = T.parent v
abbrev Ancestor (u v : V) : Prop := Relation.ReflTransGen T.Step u v

lemma ancestor_height {u v : V} (h : T.Ancestor u v) : T.height u ≤ T.height v := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (h.2 ▸ T.height_mono _)

/-- McShane cones over the finite ancestral chain. The recursive minimum is
used instead of linear interpolation, so zero-length incidences need no division. -/
noncomputable def profile (q : V → ℝ) (v : V) : ℝ → ℝ :=
  T.wf.fix (fun v rec => if h : v = T.root then fun H => q v + |H-T.height v|
    else fun H => min (rec (T.parent v) ⟨h,rfl⟩ H) (q v + |H-T.height v|)) v

lemma profile_eq (q : V → ℝ) (v : V) :
    T.profile q v = if _h : v = T.root then fun H => q v + |H-T.height v|
      else fun H => min (T.profile q (T.parent v) H) (q v + |H-T.height v|) := by
  rw [profile,WellFounded.fix_eq]
  rfl

lemma profile_root (q : V → ℝ) (H : ℝ) :
    T.profile q T.root H = q T.root + |H-T.height T.root| := by
  rw [profile_eq,dite_eq_left rfl]

lemma profile_child (q : V → ℝ) {v : V} (hv : v ≠ T.root) (H : ℝ) :
    T.profile q v H = min (T.profile q (T.parent v) H) (q v + |H-T.height v|) := by
  rw [profile_eq,dite_eq_right hv]

lemma profile_le_cone (q : V → ℝ) (v : V) (H : ℝ) :
    T.profile q v H ≤ q v + |H-T.height v| := by
  by_cases hv : v = T.root
  · subst v; rw [profile_root]
  · rw [profile_child _ _ hv]; exact min_le_right _ _

lemma profile_lipschitz (q : V → ℝ) (v : V) : LipschitzWith 1 (T.profile q v) := by
  induction v using T.wf.induction with
  | h v ih =>
    have hcone : LipschitzWith 1 (fun H : ℝ => q v + |H-T.height v|) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq,add_sub_add_comm,sub_self,zero_add,NNReal.coe_one,one_mul] using
        abs_dist_sub_le x y (T.height v)
    by_cases hv : v = T.root
    · rw [profile_eq,dite_eq_left hv]; exact hcone
    · rw [profile_eq,dite_eq_right hv]
      simpa only [max_self] using (ih (T.parent v) ⟨hv,rfl⟩).min hcone

/-- Discrete one-Lipschitz data along the actual tree edges. -/
def Compatible (q : V → ℝ) : Prop :=
  ∀ v, |q v-q (T.parent v)| ≤ T.height v-T.height (T.parent v)

lemma profile_above {q : V → ℝ} (hq : T.Compatible q) (v : V) {H : ℝ}
    (hH : T.height v ≤ H) : T.profile q v H = q v + (H-T.height v) := by
  induction v using T.wf.induction with
  | h v ih =>
    by_cases hv : v = T.root
    · subst v; rw [profile_root,abs_of_nonneg (sub_nonneg.mpr hH)]
    · rw [profile_child _ _ hv,ih (T.parent v) ⟨hv,rfl⟩ ((T.height_mono v).trans hH),
        abs_of_nonneg (sub_nonneg.mpr hH)]
      apply min_eq_right
      have hb := (abs_le.mp (hq v)).2
      linarith

lemma profile_at {q : V → ℝ} (hq : T.Compatible q) (v : V) :
    T.profile q v (T.height v) = q v := by
  simpa only [sub_self,add_zero] using T.profile_above hq v le_rfl

lemma profile_below_parent {q : V → ℝ} (hq : T.Compatible q) {v : V}
    (hv : v ≠ T.root) {H : ℝ} (hH : H ≤ T.height (T.parent v)) :
    T.profile q v H = T.profile q (T.parent v) H := by
  rw [profile_child _ _ hv]
  apply min_eq_left
  have hc := T.profile_le_cone q (T.parent v) H
  rw [abs_of_nonpos (sub_nonpos.mpr hH)] at hc
  rw [abs_of_nonpos (sub_nonpos.mpr (hH.trans (T.height_mono v)))]
  have hb := (abs_le.mp (hq v)).1
  linarith

/-- Common root prefixes receive literally the same potential on every copy. -/
lemma profile_ancestor {q : V → ℝ} (hq : T.Compatible q) {u v : V}
    (h : T.Ancestor u v) {H : ℝ} (hH : H ≤ T.height u) :
    T.profile q v H = T.profile q u H := by
  induction h with
  | refl => rfl
  | @tail v w huv hvw ih =>
    rw [T.profile_below_parent hq hvw.1 (hH.trans (T.ancestor_height huv) |>.trans_eq (congrArg T.height hvw.2)),
      ← hvw.2]
    exact ih

lemma root_ancestor (v : V) : T.Ancestor T.root v := by
  induction v using T.wf.induction with
  | h v ih =>
    by_cases hv : v = T.root
    · subst v; exact Relation.ReflTransGen.refl
    · exact (ih (T.parent v) ⟨hv,rfl⟩).tail ⟨hv,rfl⟩

noncomputable def depth (v : V) : ℕ :=
  T.wf.fix (fun v rec => if h : v = T.root then 0
    else rec (T.parent v) ⟨h,rfl⟩ + 1) v

lemma depth_eq (v : V) :
    T.depth v = if _h : v = T.root then 0 else T.depth (T.parent v)+1 := by
  rw [depth,WellFounded.fix_eq]
  rfl

lemma step_depth {u v : V} (h : T.Step u v) : T.depth u < T.depth v := by
  rw [T.depth_eq v,dite_eq_right h.1,← h.2]
  omega

lemma ancestor_depth {u v : V} (h : T.Ancestor u v) : T.depth u ≤ T.depth v := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (T.step_depth h).le

lemma ancestor_antisymm {u v : V} (h : T.Ancestor u v) (h' : T.Ancestor v u) : u=v := by
  cases h with
  | refl => rfl
  | tail huv hwv =>
    have h₁ := T.ancestor_depth h'
    have h₂ := T.ancestor_depth huv
    have h₃ := T.step_depth hwv
    omega

def IsLeaf (v : V) : Prop := ∀ w, ¬T.Step v w

lemma exists_leaf [Fintype V] (v : V) : ∃ w, T.Ancestor v w ∧ T.IsLeaf w := by
  classical
  let S := Finset.univ.filter (T.Ancestor v)
  obtain ⟨w,hw,hmax⟩ := Finset.exists_max_image S T.depth ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ v,Relation.ReflTransGen.refl⟩⟩
  have hw' : T.Ancestor v w := (Finset.mem_filter.mp hw).2
  refine ⟨w,hw',fun u hu => ?_⟩
  have hu' : u∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ u,hw'.tail hu⟩
  exact (not_lt_of_ge (hmax u hu')) (T.step_depth hu)

noncomputable def leafAbove [Fintype V] (v : V) : {w : V // T.IsLeaf w} :=
  ⟨(T.exists_leaf v).choose,(T.exists_leaf v).choose_spec.2⟩

lemma ancestor_leafAbove [Fintype V] (v : V) : T.Ancestor v (T.leafAbove v).val :=
  (T.exists_leaf v).choose_spec.1

end HeightTree
end PlanarL1

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}

/-- Each orientation is one distinct new branch incidence. Paired incidences
are not identified until the column switch is installed. -/
def ExtraDart (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
    (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V) :=
  {d : G.Dart // ¬ (shortestParents hc hs hl o).graph.Adj d.fst d.snd}

namespace ExtraDart
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

noncomputable def reverse (d : ExtraDart hc hs hl o) : ExtraDart hc hs hl o :=
  ⟨d.val.symm,fun h => d.property h.symm⟩

lemma reverse_reverse (d : ExtraDart hc hs hl o) :
    reverse hc hs hl o (reverse hc hs hl o d)=d := by
  apply Subtype.ext
  exact SimpleGraph.Dart.symm_symm d.val

noncomputable def tipHeight (d : ExtraDart hc hs hl o) : ℝ :=
  (l d.val.fst d.val.snd + graphDistance G l o d.val.fst + graphDistance G l o d.val.snd)/2

lemma tipHeight_reverse (d : ExtraDart hc hs hl o) :
    tipHeight hc hs hl o (reverse hc hs hl o d)=tipHeight hc hs hl o d := by
  change (l d.val.snd d.val.fst + graphDistance G l o d.val.snd + graphDistance G l o d.val.fst)/2 = _
  rw [hs d.val.snd d.val.fst]
  unfold tipHeight
  ring

lemma height_le_tip (d : ExtraDart hc hs hl o) :
    graphDistance G l o d.val.fst ≤ tipHeight hc hs hl o d := by
  have h := (abs_le.mp (height_edge hc hs (fun u v h => (hl u v h).le) o d.val.adj)).2
  unfold tipHeight
  linarith

end ExtraDart

namespace EnlargedTree
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

abbrev Node := V ⊕ ExtraDart hc hs hl o

noncomputable def parent : Node hc hs hl o → Node hc hs hl o
  | .inl v => .inl ((shortestParents hc hs hl o).parent v)
  | .inr d => .inl d.val.fst

noncomputable def height : Node hc hs hl o → ℝ
  | .inl v => graphDistance G l o v
  | .inr d => ExtraDart.tipHeight hc hs hl o d

lemma parent_wf : WellFounded (fun u v : Node hc hs hl o =>
    v ≠ .inl o ∧ u = parent hc hs hl o v) := by
  let D := shortestParents hc hs hl o
  have ha : ∀ v : V, Acc (fun u v : Node hc hs hl o =>
      v ≠ .inl o ∧ u = parent hc hs hl o v) (.inl v) := by
    intro v
    induction v using D.wellFounded.induction with
    | h v ih =>
      constructor
      rintro u ⟨hv,rfl⟩
      exact ih (D.parent v) (D.descent v (fun he => hv (congrArg Sum.inl he)))
  constructor
  intro v
  cases v with
  | inl v => exact ha v
  | inr d =>
    constructor
    rintro u ⟨_,rfl⟩
    exact ha d.val.fst

/-- An abstract height tree, including zero-length branches. -/
noncomputable def tree : HeightTree (Node hc hs hl o) where
  root := .inl o
  parent := parent hc hs hl o
  at_root := congrArg Sum.inl (shortestParents hc hs hl o).at_root
  wf := parent_wf hc hs hl o
  height := height hc hs hl o
  height_mono := by
    intro v
    cases v with
    | inl v =>
      change (shortestParents hc hs hl o).height _ ≤ (shortestParents hc hs hl o).height v
      by_cases hv : v=o
      · subst v
        have hr : (shortestParents hc hs hl o).parent o=o := (shortestParents hc hs hl o).at_root
        rw [hr]
      · exact ((shortestParents hc hs hl o).descent v hv).le
    | inr d => exact ExtraDart.height_le_tip hc hs hl o d

lemma extra_leaf (d : ExtraDart hc hs hl o) :
    (tree hc hs hl o).IsLeaf (.inr d) := by
  intro v h
  cases v <;> exact Sum.inr_ne_inl h.2

/-- Graph-distance potentials extended to the two endpoints of each split
edge by their shortest distance through either of that edge's endpoints. -/
noncomputable def potential (z : V) : Node hc hs hl o → ℝ
  | .inl v => graphDistance G l z v
  | .inr d => min
      (graphDistance G l z d.val.fst + ExtraDart.tipHeight hc hs hl o d - graphDistance G l o d.val.fst)
      (graphDistance G l z d.val.snd + ExtraDart.tipHeight hc hs hl o d - graphDistance G l o d.val.snd)

lemma potential_reverse (z : V) (d : ExtraDart hc hs hl o) :
    potential hc hs hl o z (.inr (ExtraDart.reverse hc hs hl o d)) =
      potential hc hs hl o z (.inr d) := by
  change min
    (graphDistance G l z d.val.snd + ExtraDart.tipHeight hc hs hl o (ExtraDart.reverse hc hs hl o d) - graphDistance G l o d.val.snd)
    (graphDistance G l z d.val.fst + ExtraDart.tipHeight hc hs hl o (ExtraDart.reverse hc hs hl o d) - graphDistance G l o d.val.fst) = _
  rw [ExtraDart.tipHeight_reverse]
  exact min_comm _ _

lemma min_split_compatible {du dv a b : ℝ} (ha : 0≤a)
    (h : |du-dv|≤a+b) : |min (du+a) (dv+b)-du|≤a := by
  apply abs_le.mpr
  constructor
  · have h₁ : du-a≤du+a := by linarith
    have h₂ : du-a≤dv+b := by have := (abs_le.mp h).2; linarith
    have := le_min h₁ h₂
    linarith
  · have := min_le_left (du+a) (dv+b)
    linarith

lemma potential_compatible (z : V) :
    (tree hc hs hl o).Compatible (potential hc hs hl o z) := by
  intro v
  cases v with
  | inl v =>
    change |graphDistance G l z v - graphDistance G l z ((shortestParents hc hs hl o).parent v)| ≤
      graphDistance G l o v - graphDistance G l o ((shortestParents hc hs hl o).parent v)
    by_cases hv : v=o
    · subst v
      have hr : (shortestParents hc hs hl o).parent o=o := (shortestParents hc hs hl o).at_root
      rw [hr,sub_self,abs_zero,sub_self]
    · obtain ⟨hedge,hlen⟩ := shortestParents.parent_step hc hs hl o v hv
      have h := height_edge hc hs (fun u v h => (hl u v h).le) z hedge.symm
      rw [hs v ((shortestParents hc hs hl o).parent v)] at h
      linarith
  | inr d =>
    have ha := ExtraDart.height_le_tip hc hs hl o d
    have hd := height_edge hc hs (fun u v h => (hl u v h).le) z d.val.adj
    have hsum : (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.fst)+
        (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.snd)=l d.val.fst d.val.snd := by
      unfold ExtraDart.tipHeight
      ring
    have hx := min_split_compatible (du := graphDistance G l z d.val.fst)
      (dv := graphDistance G l z d.val.snd)
      (b := ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.snd)
      (sub_nonneg.mpr ha) (by rw [hsum]; exact hd)
    change |min (_ + _ - _) (_ + _ - _) - graphDistance G l z d.val.fst| ≤ ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.fst
    simpa only [add_sub_assoc] using hx

end EnlargedTree
end PlanarL1.Weighted

namespace PlanarL1.HeightTree
open Set Columns
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {n : ℕ} (T : HeightTree V)

/-- Adjacent copies in the cyclic contour of an ancestral subtree. -/
def prefixGraph (leaf : Fin n → V) (a : V) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ Consecutive i j ∧ T.Ancestor a (leaf i) ∧ T.Ancestor a (leaf j)
  symm := ⟨by
    rintro i j ⟨hij,hc,hi,hj⟩
    refine ⟨hij.symm,?_,hj,hi⟩
    rcases hc with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The combinatorial output of a planar tree contour construction. No metric
realization or metric estimates are part of this data. -/
structure Layout (n : ℕ) where
  leaf : Fin n → V
  isLeaf : ∀ i, T.IsLeaf (leaf i)
  injective : Function.Injective leaf
  covers : ∀ v, T.IsLeaf v → ∃ i, leaf i = v
  prefix_connected : ∀ a i j, T.Ancestor a (leaf i) → T.Ancestor a (leaf j) →
    (T.prefixGraph leaf a).Reachable i j
  pair : SimpleGraph (Fin n)
  noncrossing : ColumnOrder.Noncrossing pair
  paired_height : ∀ i j, pair.Adj i j → T.height (leaf i)=T.height (leaf j)
  matching : ∀ i j k, pair.Adj i j → pair.Adj i k → j=k

namespace Layout
variable {T} (L : T.Layout n)

noncomputable def heights (i j : Fin n) : Set ℝ :=
  (⋃ a : V, if i ≠ j ∧ Consecutive i j ∧ T.Ancestor a (L.leaf i) ∧ T.Ancestor a (L.leaf j)
    then Icc (T.height T.root) (T.height a) else ∅) ∪
  (if L.pair.Adj i j then {T.height (L.leaf i)} else ∅)

omit [Fintype V] in
lemma mem_heights (i j : Fin n) (H : ℝ) : H ∈ L.heights i j ↔
    (∃ a, (T.prefixGraph L.leaf a).Adj i j ∧ T.height T.root ≤ H ∧ H ≤ T.height a) ∨
    (L.pair.Adj i j ∧ H=T.height (L.leaf i)) := by
  classical
  simp only [heights,mem_union,mem_iUnion,mem_ite_empty_right,mem_Icc,mem_singleton_iff,prefixGraph]

omit [Fintype V] in
lemma heights_symm (i j : Fin n) : L.heights i j=L.heights j i := by
  ext H
  simp only [mem_heights]
  constructor <;> intro h
  · rcases h with ⟨a,ha,hH⟩ | ⟨ha,rfl⟩
    · exact Or.inl ⟨a,ha.symm,hH⟩
    · exact Or.inr ⟨ha.symm,L.paired_height i j ha⟩
  · rcases h with ⟨a,ha,hH⟩ | ⟨ha,rfl⟩
    · exact Or.inl ⟨a,ha.symm,hH⟩
    · exact Or.inr ⟨ha.symm,L.paired_height j i ha⟩

lemma heights_compact (i j : Fin n) : IsCompact (L.heights i j) := by
  apply IsCompact.union
  · apply isCompact_iUnion
    intro a
    split_ifs <;> first | exact isCompact_Icc | exact isCompact_empty
  · split_ifs <;> first | exact isCompact_singleton | exact isCompact_empty

omit [Fintype V] in
lemma switch_le_tip {i j : Fin n} {H : ℝ} (h : H ∈ L.heights i j) :
    H ≤ T.height (L.leaf i) := by
  rcases (L.mem_heights i j H).mp h with ⟨a,ha,_,hH⟩ | ⟨_,rfl⟩
  · exact hH.trans (T.ancestor_height ha.2.2.1)
  · rfl

noncomputable def model : Model n where
  link := (T.prefixGraph L.leaf T.root) ⊔ L.pair
  heights := L.heights
  symm := L.heights_symm
  permitted i j H h := by
    rcases (L.mem_heights i j H).mp h with ⟨a,ha,_⟩ | ⟨ha,_⟩
    · exact Or.inl ⟨ha.1,ha.2.1,T.root_ancestor _,T.root_ancestor _⟩
    · exact Or.inr ha
  compact := L.heights_compact
  noncrossing := by
    intro a b c d hab hbc hcd h
    have hac : ¬Consecutive a c := by
      simp only [Consecutive]
      omega
    have hbd : ¬Consecutive b d := by
      simp only [Consecutive]
      omega
    rcases h.1 with ha | ha
    · exact hac ha.2.1
    · rcases h.2 with hb | hb
      · exact hbd hb.2.1
      · exact L.noncrossing a b c d hab hbc hcd ⟨ha,hb⟩
  terminal i j ha hn := by
    have hp : L.pair.Adj i j := ha.resolve_left (fun h => hn h.2.1)
    refine ⟨T.height (L.leaf i),?_,?_⟩
    · ext H
      rw [L.mem_heights]
      constructor
      · rintro (⟨a,ha,_⟩ | ⟨_,he⟩)
        · exact (hn ha.2.1).elim
        · exact he
      · intro he
        exact Or.inr ⟨hp,he⟩
    · intro k H hH
      rcases hH with hH | hH
      · exact L.switch_le_tip hH
      · rw [L.paired_height i j hp]
        exact L.switch_le_tip hH

/-- Constant-height switches connect all copies on a common root prefix. -/
noncomputable def prefixPath {a : V} {i j : Fin n}
    (p : (T.prefixGraph L.leaf a).Walk i j) {H : ℝ}
    (hlo : T.height T.root ≤ H) (hhi : H ≤ T.height a) :
    L.model.Path univ i j :=
  match p with
  | .nil => .nil _
  | .cons h p => .cons H (mem_univ H) ((L.mem_heights _ _ _).mpr (Or.inl ⟨a,h,hlo,hhi⟩))
      (prefixPath p hlo hhi)

lemma prefixPath_length {a : V} {i j : Fin n}
    (p : (T.prefixGraph L.leaf a).Walk i j) {H : ℝ}
    (hlo : T.height T.root ≤ H) (hhi : H ≤ T.height a) :
    (L.prefixPath p hlo hhi).length H H=0 := by
  induction p with
  | nil => simp only [prefixPath,Model.Path.length,sub_self,abs_zero]
  | cons h p ih => simp only [prefixPath,Model.Path.length,sub_self,abs_zero,zero_add,ih]

lemma exists_prefixPath {a : V} {i j : Fin n}
    (hi : T.Ancestor a (L.leaf i)) (hj : T.Ancestor a (L.leaf j)) {H : ℝ}
    (hlo : T.height T.root ≤ H) (hhi : H ≤ T.height a) :
    ∃ p : L.model.Path univ i j, p.length H H=0 := by
  obtain ⟨p⟩ := L.prefix_connected a i j hi hj
  exact ⟨L.prefixPath p hlo hhi,L.prefixPath_length p hlo hhi⟩

noncomputable def column (v : V) : Fin n :=
  (L.covers _ (T.leafAbove v).property).choose

lemma ancestor_column (v : V) : T.Ancestor v (L.leaf (L.column v)) := by
  rw [column,(L.covers _ (T.leafAbove v).property).choose_spec]
  exact T.ancestor_leafAbove v

noncomputable def point (v : V) : L.model.Point univ (L.column T.root) where
  column := L.column v
  height := T.height v
  inBand := mem_univ _
  reachable := by
    obtain ⟨p,_⟩ := L.exists_prefixPath (T.root_ancestor (L.leaf (L.column T.root)))
      (T.root_ancestor (L.leaf (L.column v))) le_rfl le_rfl
    exact ⟨p.word⟩

end Layout
end PlanarL1.HeightTree

namespace PlanarL1.Columns.Model
open Set
variable {n : ℕ} (M : Model n)

/-- A scalar potential compatible with every actual switch bounds the length
of every switching path, irrespective of excursions into the separate tails. -/
lemma Path.potential_le {J : Set ℝ} {i j : Fin n} (p : M.Path J i j)
    (q : Fin n → ℝ → ℝ) (hLip : ∀ i, LipschitzWith 1 (q i))
    (hSwitch : ∀ i j H, H ∈ M.heights i j → q i H=q j H) (a b : ℝ) :
    |q i a-q j b| ≤ p.length a b := by
  induction p generalizing a with
  | nil i => simpa only [Path.length,Real.dist_eq,NNReal.coe_one,one_mul] using (hLip i).dist_le_mul a b
  | @cons i j k H hH hs p ih =>
    have hl : |q i a-q i H|≤|a-H| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using (hLip i).dist_le_mul a H
    have hb := abs_sub_le (q i a) (q i H) (q k b)
    rw [hSwitch i j H hs] at hb
    exact hb.trans (add_le_add (by rwa [← hSwitch i j H hs]) (ih H))

lemma Point.potential_le {J : Set ℝ} {root : Fin n} (x y : M.Point J root)
    (q : Fin n → ℝ → ℝ) (hLip : ∀ i, LipschitzWith 1 (q i))
    (hSwitch : ∀ i j H, H ∈ M.heights i j → q i H=q j H) :
    |q x.column x.height-q y.column y.height| ≤ x.distance y := by
  have := x.paths_nonempty y
  exact le_ciInf (fun p => p.potential_le M q hLip hSwitch x.height y.height)
end PlanarL1.Columns.Model

namespace PlanarL1.HeightTree
open Set Columns
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {n : ℕ} {T : HeightTree V}

omit [Fintype V] in
lemma IsLeaf.ancestor_eq {v w : V} (hv : T.IsLeaf v) (h : T.Ancestor v w) : v=w := by
  induction h with
  | refl => rfl
  | @tail u w hvu huw ih => exact (hv w (ih ▸ huw)).elim

namespace Layout
variable (L : T.Layout n)

lemma leaf_column {v : V} (hv : T.IsLeaf v) : L.leaf (L.column v)=v :=
  (hv.ancestor_eq (L.ancestor_column v)).symm

lemma column_leaf (i : Fin n) : L.column (L.leaf i)=i :=
  L.injective (L.leaf_column (L.isLeaf i))

lemma profile_switch {q : V → ℝ} (hq : T.Compatible q)
    (hpair : ∀ i j, L.pair.Adj i j → q (L.leaf i)=q (L.leaf j))
    (i j : Fin n) (H : ℝ) (hs : H ∈ L.model.heights i j) :
    T.profile q (L.leaf i) H=T.profile q (L.leaf j) H := by
  rcases (L.mem_heights i j H).mp hs with ⟨a,ha,_,hH⟩ | ⟨ha,rfl⟩
  · rw [T.profile_ancestor hq ha.2.2.1 hH,T.profile_ancestor hq ha.2.2.2 hH]
  · rw [T.profile_at hq,L.paired_height i j ha,T.profile_at hq,hpair i j ha]

lemma potential_le {q : V → ℝ} (hq : T.Compatible q)
    (hpair : ∀ i j, L.pair.Adj i j → q (L.leaf i)=q (L.leaf j)) (v w : V) :
    |q v-q w|≤(L.point v).distance (L.point w) := by
  have h := (L.point v).potential_le L.model (L.point w)
    (fun i => T.profile q (L.leaf i)) (fun i => T.profile_lipschitz q (L.leaf i))
    (L.profile_switch hq hpair)
  change |T.profile q (L.leaf (L.column v)) (T.height v)-
    T.profile q (L.leaf (L.column w)) (T.height w)|≤_ at h
  rwa [T.profile_ancestor hq (L.ancestor_column v) le_rfl,
    T.profile_ancestor hq (L.ancestor_column w) le_rfl,T.profile_at hq,T.profile_at hq] at h

lemma parent_distance_le (v : V) :
    (L.point v).distance (L.point (T.parent v))≤T.height v-T.height (T.parent v) := by
  by_cases hv : v=T.root
  · subst v
    rw [T.at_root,Model.Point.distance_self,sub_self]
  · have had : T.Ancestor (T.parent v) (L.leaf (L.column v)) :=
      (Relation.ReflTransGen.single ⟨hv,rfl⟩).trans (L.ancestor_column v)
    obtain ⟨p,hp⟩ := L.exists_prefixPath had (L.ancestor_column (T.parent v))
      (T.ancestor_height (T.root_ancestor (T.parent v))) le_rfl
    have h := (L.point v).distance_le (L.point (T.parent v)) p
    have hb := p.length_start_le (T.height v) (T.height (T.parent v)) (T.height (T.parent v))
    rw [hp,add_zero,abs_of_nonneg (sub_nonneg.mpr (T.height_mono v))] at hb
    exact h.trans hb

lemma pair_distance_zero {i j : Fin n} (h : L.pair.Adj i j) :
    (L.point (L.leaf i)).distance (L.point (L.leaf j))=0 := by
  apply le_antisymm _ (Model.Point.distance_nonneg _ _)
  let p : L.model.Path univ (L.point (L.leaf i)).column (L.point (L.leaf j)).column :=
    .cons (T.height (L.leaf i)) (mem_univ _) (by
      change T.height (L.leaf i) ∈ L.heights (L.column (L.leaf i)) (L.column (L.leaf j))
      rw [L.column_leaf,L.column_leaf]
      exact (L.mem_heights _ _ _).mpr (Or.inr ⟨h,rfl⟩)) (.nil _)
  have he : p.length (T.height (L.leaf i)) (T.height (L.leaf j))=0 := by
    simp only [p,Model.Path.length,sub_self,abs_zero,L.paired_height i j h,zero_add]
  exact ((L.point (L.leaf i)).distance_le _ p).trans_eq he

end Layout
end PlanarL1.HeightTree

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

noncomputable instance ExtraDart.fintype : Fintype (ExtraDart hc hs hl o) :=
  by unfold ExtraDart; exact Fintype.ofFinite _

namespace EnlargedTree
variable {hc hs hl o} {n : ℕ} (L : (tree hc hs hl o).Layout n)

/-- The leaf pairs are precisely the two incidences of each original non-tree
edge, not extra shortcuts. -/
def ExactPairs : Prop := ∀ i j, L.pair.Adj i j ↔ ∃ d : ExtraDart hc hs hl o,
  L.leaf i=Sum.inr d ∧ L.leaf j=Sum.inr (ExtraDart.reverse hc hs hl o d)

lemma original_distance_lower (hpair : ExactPairs L) (u v : V) :
    graphDistance G l u v ≤ (L.point (.inl u)).distance (L.point (.inl v)) := by
  have hh := L.potential_le (potential_compatible hc hs hl o u) (fun i j h => by
    obtain ⟨d,hi,hj⟩ := (hpair i j).mp h
    rw [hi,hj]
    exact (potential_reverse hc hs hl o u d).symm) (.inl u) (.inl v)
  change |graphDistance G l u u-graphDistance G l u v|≤_ at hh
  rwa [distance_self (fun u v h => (hl u v h).le),zero_sub,abs_neg,
    abs_of_nonneg (distance_nonneg (fun u v h => (hl u v h).le) (hc.preconnected u v))] at hh

lemma tip_pair (hpair : ExactPairs L) (d : ExtraDart hc hs hl o) :
    L.pair.Adj (L.column (.inr d)) (L.column (.inr (ExtraDart.reverse hc hs hl o d))) := by
  apply (hpair _ _).mpr
  exact ⟨d,L.leaf_column (extra_leaf hc hs hl o d),
    L.leaf_column (extra_leaf hc hs hl o (ExtraDart.reverse hc hs hl o d))⟩

lemma tip_distance_zero (hpair : ExactPairs L) (d : ExtraDart hc hs hl o) :
    (L.point (.inr d)).distance (L.point (.inr (ExtraDart.reverse hc hs hl o d)))=0 := by
  have h := L.pair_distance_zero (tip_pair L hpair d)
  rwa [L.leaf_column (extra_leaf hc hs hl o d),
    L.leaf_column (extra_leaf hc hs hl o (ExtraDart.reverse hc hs hl o d))] at h

lemma original_parent_distance (v : V) (hv : v≠o) :
    (L.point (.inl v)).distance (L.point (.inl ((shortestParents hc hs hl o).parent v))) ≤
      l v ((shortestParents hc hs hl o).parent v) := by
  have h := L.parent_distance_le (.inl v)
  change (L.point (.inl v)).distance (L.point (.inl ((shortestParents hc hs hl o).parent v))) ≤
    graphDistance G l o v-graphDistance G l o ((shortestParents hc hs hl o).parent v) at h
  obtain ⟨_,he⟩ := shortestParents.parent_step hc hs hl o v hv
  rw [hs v ((shortestParents hc hs hl o).parent v)]
  linarith

lemma original_edge_distance (hpair : ExactPairs L) {u v : V} (h : G.Adj u v) :
    (L.point (.inl u)).distance (L.point (.inl v))≤l u v := by
  by_cases ht : (shortestParents hc hs hl o).graph.Adj u v
  · rcases ht with ⟨hu,rfl⟩ | ⟨hv,rfl⟩
    · exact original_parent_distance L u hu
    · rw [Columns.Model.Point.distance_comm,hs]
      exact original_parent_distance L v hv
  · let d : ExtraDart hc hs hl o := ⟨⟨(u,v),h⟩,ht⟩
    have hd := L.parent_distance_le (.inr d)
    have hr := L.parent_distance_le (.inr (ExtraDart.reverse hc hs hl o d))
    have hz := tip_distance_zero L hpair d
    have h₁ := (L.point (.inl u)).distance_triangle (L.point (.inr d)) (L.point (.inl v))
    have h₂ := (L.point (.inr d)).distance_triangle
      (L.point (.inr (ExtraDart.reverse hc hs hl o d))) (L.point (.inl v))
    rw [hz,zero_add] at h₂
    change (L.point (.inr d)).distance (L.point (.inl u))≤
      ExtraDart.tipHeight hc hs hl o d-graphDistance G l o u at hd
    change (L.point (.inr (ExtraDart.reverse hc hs hl o d))).distance (L.point (.inl v))≤
      ExtraDart.tipHeight hc hs hl o (ExtraDart.reverse hc hs hl o d)-graphDistance G l o v at hr
    rw [ExtraDart.tipHeight_reverse] at hr
    rw [Columns.Model.Point.distance_comm] at hd
    have hsum : (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o u)+
        (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o v)=l u v := by
      dsimp [ExtraDart.tipHeight,d]
      ring
    linarith

lemma original_walk_distance (hpair : ExactPairs L) {u v : V} (p : G.Walk u v) :
    (L.point (.inl u)).distance (L.point (.inl v))≤walkLength l p := by
  induction p with
  | nil => rw [walkLength,Columns.Model.Point.distance_self]
  | @cons u w v h p ih =>
    exact ((L.point (.inl u)).distance_triangle (L.point (.inl w)) (L.point (.inl v))).trans
      (add_le_add (original_edge_distance L hpair h) ih)

/-- The original weighted graph embeds isometrically into the actual column
path metric. In particular all tails and zero-length branch incidences are
accounted for; the lower bound is certified by graph-distance potentials. -/
lemma original_distance (hpair : ExactPairs L) (u v : V) :
    (L.point (.inl u)).distance (L.point (.inl v))=graphDistance G l u v := by
  apply le_antisymm _ (original_distance_lower L hpair u v)
  obtain ⟨p,hp,_⟩ := distance_eq_length (fun u v h => (hl u v h).le) (hc.preconnected u v)
  rw [hp]
  exact original_walk_distance L hpair p.val

end EnlargedTree
end PlanarL1.Weighted



end

end OAI
