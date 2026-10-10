import OAI.Probability.FreeIsing.Trees.Cardinality
import OAI.Probability.FreeIsing.Trees.ClusterRestriction

namespace OAI

noncomputable section

namespace Problem367.ClusterComponentCount

variable {d : ℕ}

def openAdj (O : TreeVertex d → Bool) (u v : TreeVertex d) : Prop :=
  (u = parentVertex v ∧ v.1 ≠ [] ∧ O v = true) ∨
  (v = parentVertex u ∧ u.1 ≠ [] ∧ O u = true)

lemma openAdj_symm {O : TreeVertex d → Bool} {u v : TreeVertex d}
    (h : openAdj O u v) : openAdj O v u := h.elim Or.inr Or.inl

lemma openAdj_treeAdj {O : TreeVertex d → Bool} {u v : TreeVertex d}
    (h : openAdj O u v) : treeAdj u v := by
  rcases h with ⟨rfl, hv, _⟩ | ⟨rfl, hu, _⟩
  · exact treeAdj_parentVertex hv
  · rcases treeAdj_parentVertex hu with h | h
    · exact Or.inr h
    · exact Or.inl h

def openRoot (O : TreeVertex d → Bool) (v : TreeVertex d) : TreeVertex d :=
  if _hv : v.1 = [] then v
  else if O v = true then openRoot O (parentVertex v) else v
termination_by v.1.length
decreasing_by
  rw [parentVertex_length]
  have := List.length_pos_iff.mpr _hv
  omega

lemma openRoot_of_nil (O : TreeVertex d → Bool) {v : TreeVertex d}
    (hv : v.1 = []) : openRoot O v = v := by
  rw [openRoot, dite_eq_left hv]

lemma openRoot_of_closed (O : TreeVertex d → Bool) {v : TreeVertex d}
    (hv : O v ≠ true) : openRoot O v = v := by
  rw [openRoot]
  split_ifs <;> rfl

lemma openRoot_of_open (O : TreeVertex d → Bool) {v : TreeVertex d}
    (hv : v.1 ≠ []) (ho : O v = true) :
    openRoot O v = openRoot O (parentVertex v) := by
  rw [openRoot, dite_eq_right hv, ite_eq_left ho]

lemma openRoot_prefix (O : TreeVertex d → Bool) (v : TreeVertex d) :
    (openRoot O v).1 <+: v.1 := by
  induction hvlen : v.1.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v.1 = []
    · rw [openRoot_of_nil O hv]
    · by_cases ho : O v = true
      · rw [openRoot_of_open O hv ho]
        have hp : (parentVertex v).1.length < n := by
          rw [parentVertex_length]
          have := List.length_pos_iff.mpr hv
          omega
        exact (ih _ hp _ rfl).trans (List.dropLast_prefix v.1)
      · rw [openRoot_of_closed O ho]

lemma openRoot_length_le (O : TreeVertex d → Bool) (v : TreeVertex d) :
    (openRoot O v).1.length ≤ v.1.length := (openRoot_prefix O v).length_le

lemma openRoot_stopped (O : TreeVertex d → Bool) (v : TreeVertex d) :
    (openRoot O v).1 = [] ∨ O (openRoot O v) ≠ true := by
  induction hvlen : v.1.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v.1 = []
    · rw [openRoot_of_nil O hv]
      exact Or.inl hv
    · by_cases ho : O v = true
      · rw [openRoot_of_open O hv ho]
        apply ih _ _ _ rfl
        rw [parentVertex_length]
        have := List.length_pos_iff.mpr hv
        omega
      · rw [openRoot_of_closed O ho]
        exact Or.inr ho

lemma openRoot_idempotent (O : TreeVertex d → Bool) (v : TreeVertex d) :
    openRoot O (openRoot O v) = openRoot O v := by
  rcases openRoot_stopped O v with h | h
  · exact openRoot_of_nil O h
  · exact openRoot_of_closed O h

lemma openRoot_eq_of_openAdj {O : TreeVertex d → Bool} {u v : TreeVertex d}
    (h : openAdj O u v) : openRoot O u = openRoot O v := by
  rcases h with ⟨rfl, hv, ho⟩ | ⟨rfl, hu, ho⟩
  · exact (openRoot_of_open O hv ho).symm
  · exact openRoot_of_open O hu ho

lemma openRoot_eq_of_connected {O : TreeVertex d → Bool} {u v : TreeVertex d}
    (h : Relation.ReflTransGen (openAdj O) u v) : openRoot O u = openRoot O v := by
  induction h with
  | refl => rfl
  | tail h huv ih => exact ih.trans (openRoot_eq_of_openAdj huv)

lemma connected_openRoot (O : TreeVertex d → Bool) (v : TreeVertex d) :
    Relation.ReflTransGen (openAdj O) v (openRoot O v) := by
  induction hvlen : v.1.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v.1 = []
    · rw [openRoot_of_nil O hv]
    · by_cases ho : O v = true
      · rw [openRoot_of_open O hv ho]
        have hs : openAdj O v (parentVertex v) := Or.inr ⟨rfl, hv, ho⟩
        apply (Relation.ReflTransGen.single hs).trans
        apply ih _ _ _ rfl
        rw [parentVertex_length]
        have := List.length_pos_iff.mpr hv
        omega
      · rw [openRoot_of_closed O ho]

lemma connected_symm {O : TreeVertex d → Bool} {u v : TreeVertex d}
    (h : Relation.ReflTransGen (openAdj O) u v) :
    Relation.ReflTransGen (openAdj O) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hab ih => exact (Relation.ReflTransGen.single (openAdj_symm hab)).trans ih

lemma connected_of_openRoot_eq {O : TreeVertex d → Bool} {u v : TreeVertex d}
    (h : openRoot O u = openRoot O v) : Relation.ReflTransGen (openAdj O) u v := by
  have hu := connected_openRoot O u
  have hv := connected_openRoot O v
  rw [h] at hu
  exact hu.trans (connected_symm hv)

lemma connected_iff_openRoot_eq (O : TreeVertex d → Bool) (u v : TreeVertex d) :
    Relation.ReflTransGen (openAdj O) u v ↔ openRoot O u = openRoot O v :=
  ⟨openRoot_eq_of_connected, connected_of_openRoot_eq⟩

lemma openRoot_mem_or_eq {O : TreeVertex d → Bool}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {v : TreeVertex d} (hv : v ∈ D) :
    openRoot O v = openRoot O r ∨
      (openRoot O v ∈ D ∧ openRoot O v ≠ r ∧ O (openRoot O v) ≠ true) := by
  induction hvlen : v.1.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hvr : v = r
    · subst v
      exact Or.inl rfl
    · have hnil := ConnectedFinset.ne_nil_of_ne_min hmin hv hvr
      by_cases ho : O v = true
      · rw [openRoot_of_open O hnil ho]
        have hparent := hD.parent_mem_of_ne_min hr hmin hv hvr
        apply ih _ _ hparent rfl
        rw [parentVertex_length]
        have := List.length_pos_iff.mpr hnil
        omega
      · rw [openRoot_of_closed O ho]
        exact Or.inr ⟨hv, hvr, ho⟩

lemma image_openRoot {O : TreeVertex d → Bool}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    D.image (openRoot O) =
      insert (openRoot O r) ((D.erase r).filter (fun v => O v ≠ true)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    rcases openRoot_mem_or_eq hD hr hmin hv with h | ⟨hm, hn, ho⟩
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hn, hm⟩, ho⟩))
  · intro hx
    rcases Finset.mem_insert.mp hx with h | h
    · subst x
      exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
    · obtain ⟨hx, ho⟩ := Finset.mem_filter.mp h
      exact Finset.mem_image.mpr ⟨x, (Finset.mem_erase.mp hx).2,
        openRoot_of_closed O ho⟩

lemma openRoot_not_mem_closed {O : TreeVertex d → Bool}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    openRoot O r ∉ (D.erase r).filter (fun v => O v ≠ true) := by
  classical
  intro h
  obtain ⟨hm, _⟩ := Finset.mem_filter.mp h
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hm
  exact hne (hD.min_unique hr hmin hmem (openRoot_length_le O r))

def openEdges (O : TreeVertex d → Bool) (D : Finset (TreeVertex d)) :
    Finset (TreeVertex d × TreeVertex d) :=
  (inducedEdges D).filter (fun e => O e.2 = true)

lemma image_openEdges_snd {O : TreeVertex d → Bool}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    (openEdges O D).image Prod.snd = (D.erase r).filter (fun v => O v = true) := by
  classical
  rw [← hD.inducedEdges_image_snd hr hmin]
  ext v
  simp only [openEdges, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨e, ⟨he, ho⟩, rfl⟩
    exact ⟨⟨e, he, rfl⟩, ho⟩
  · rintro ⟨⟨e, he, rfl⟩, ho⟩
    exact ⟨e, ⟨he, ho⟩, rfl⟩

theorem card_image_openRoot (O : TreeVertex d → Bool)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (D.image (openRoot O)).card = D.card - (openEdges O D).card := by
  classical
  obtain ⟨r, hr, hmin⟩ := D.exists_min_image (fun v => v.1.length) hD.1
  rw [image_openRoot hD hr hmin,
    Finset.card_insert_of_notMem (openRoot_not_mem_closed hD hr hmin)]
  have hopen : (openEdges O D).card =
      ((D.erase r).filter (fun v => O v = true)).card := by
    rw [← image_openEdges_snd hD hr hmin]
    exact (Finset.card_image_of_injOn (fun x hx y hy hxy =>
      inducedEdges_snd_injOn D (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hy).1 hxy)).symm
  have hsplit := (D.erase r).card_filter_add_card_filter_not (fun v => O v = true)
  rw [Finset.card_erase_of_mem hr, ← hopen] at hsplit
  have hpos : 0 < D.card := Finset.card_pos.mpr hD.1
  simp only [ne_eq] at *
  omega

lemma card_image_eq_of_same_fibers {V A B : Type*} [DecidableEq A] [DecidableEq B]
    (D : Finset V)
    (f : V → A) (g : V → B)
    (h : ∀ x ∈ D, ∀ y ∈ D, f x = f y ↔ g x = g y) :
    (D.image f).card = (D.image g).card := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih =>
    have hsmall : ∀ x ∈ D, ∀ y ∈ D, f x = f y ↔ g x = g y := by
      intro x hx y hy
      exact h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    have hc := ih hsmall
    have hm : f a ∈ D.image f ↔ g a ∈ D.image g := by
      constructor
      · rintro hf
        obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hf
        exact Finset.mem_image.mpr ⟨x, hx,
          (h x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self _ _)).mp hfx⟩
      · rintro hg
        obtain ⟨x, hx, hgx⟩ := Finset.mem_image.mp hg
        exact Finset.mem_image.mpr ⟨x, hx,
          (h x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self _ _)).mpr hgx⟩
    rw [Finset.image_insert, Finset.image_insert]
    by_cases hf : f a ∈ D.image f
    · rw [Finset.card_insert_of_mem hf, Finset.card_insert_of_mem (hm.mp hf), hc]
    · rw [Finset.card_insert_of_notMem hf,
        Finset.card_insert_of_notMem (fun hg => hf (hm.mpr hg)), hc]

theorem card_image_componentLabel {A : Type*} [DecidableEq A] (O : TreeVertex d → Bool)
    (label : TreeVertex d → A)
    (hlabel : ∀ u v, label u = label v ↔ Relation.ReflTransGen (openAdj O) u v)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (D.image label).card = D.card - (openEdges O D).card := by
  classical
  calc
    (D.image label).card = (D.image (openRoot O)).card :=
      card_image_eq_of_same_fibers D label (openRoot O)
        (fun u _ v _ => (hlabel u v).trans (connected_iff_openRoot_eq O u v))
    _ = _ := card_image_openRoot O hD

theorem connected_iff_internal {O : TreeVertex d → Bool}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D) :
    Relation.ReflTransGen (openAdj O) u v ↔
      Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ openAdj O x y) u v :=
  hD.reachable_restrict_iff openAdj_treeAdj hu hv

lemma openAdj_iff_mem_openEdges {O : TreeVertex d → Bool}
    {D : Finset (TreeVertex d)} {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D) :
    openAdj O u v ↔ (u, v) ∈ openEdges O D ∨ (v, u) ∈ openEdges O D := by
  classical
  have hmem (a b : TreeVertex d) : (a,b) ∈ openEdges O D ↔
      (a ∈ D ∧ b ∈ D) ∧ (treeAdj a b ∧ a.1.length < b.1.length) ∧ O b = true := by
    simp [openEdges, inducedEdges, and_assoc]
  constructor
  · rintro (⟨rfl, hn, ho⟩ | ⟨rfl, hn, ho⟩)
    · left
      apply (hmem _ _).mpr
      refine ⟨⟨hu, hv⟩, ⟨treeAdj_parentVertex hn, ?_⟩, ho⟩
      rw [parentVertex_length]
      have := List.length_pos_iff.mpr hn
      omega
    · right
      apply (hmem _ _).mpr
      refine ⟨⟨hv, hu⟩, ⟨treeAdj_parentVertex hn, ?_⟩, ho⟩
      rw [parentVertex_length]
      have := List.length_pos_iff.mpr hn
      omega
  · rintro (h | h)
    · obtain ⟨_, ⟨hadj, hlt⟩, ho⟩ := (hmem _ _).mp h
      left
      refine ⟨(treeAdj_parent_of_length_lt hadj hlt).symm, ?_, ho⟩
      intro hn
      simp [hn] at hlt
    · obtain ⟨_, ⟨hadj, hlt⟩, ho⟩ := (hmem _ _).mp h
      right
      refine ⟨(treeAdj_parent_of_length_lt hadj hlt).symm, ?_, ho⟩
      intro hn
      simp [hn] at hlt

theorem compatible_iff_component_constant {A : Type*}
    (O : TreeVertex d → Bool) (eta : TreeVertex d → A)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (∀ e ∈ openEdges O D, eta e.1 = eta e.2) ↔
      ∀ u ∈ D, ∀ v ∈ D, Relation.ReflTransGen (openAdj O) u v → eta u = eta v := by
  classical
  constructor
  · intro he u hu v hv hc
    have hi := (connected_iff_internal hD hu hv).mp hc
    clear hu hv hc
    induction hi with
    | refl => rfl
    | tail h hab ih =>
      apply ih.trans
      rcases (openAdj_iff_mem_openEdges hab.1 hab.2.1).mp hab.2.2 with h | h
      · exact he _ h
      · exact (he _ h).symm
  · intro he e hee
    have hdata : e.1 ∈ D ∧ e.2 ∈ D := by
      have hmem := (Finset.mem_filter.mp hee).1
      exact Finset.mem_product.mp (Finset.mem_filter.mp hmem).1
    exact he e.1 hdata.1 e.2 hdata.2
      (Relation.ReflTransGen.single
        ((openAdj_iff_mem_openEdges hdata.1 hdata.2).mpr (Or.inl hee)))

theorem compatible_iff_label_constant {A B : Type*}
    (O : TreeVertex d → Bool) (label : TreeVertex d → A)
    (hlabel : ∀ u v, label u = label v ↔ Relation.ReflTransGen (openAdj O) u v)
    (eta : TreeVertex d → B) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (∀ e ∈ openEdges O D, eta e.1 = eta e.2) ↔
      ∀ u ∈ D, ∀ v ∈ D, label u = label v → eta u = eta v := by
  rw [compatible_iff_component_constant O eta hD]
  constructor
  · intro h u hu v hv heq
    exact h u hu v hv ((hlabel u v).mp heq)
  · intro h u hu v hv hconn
    exact h u hu v hv ((hlabel u v).mpr hconn)

def edgeMask (R : TreeVertex d → TreeVertex d → Prop) [DecidableRel R]
    (v : TreeVertex d) : Bool := decide (R (parentVertex v) v)

lemma openAdj_edgeMask_iff {R : TreeVertex d → TreeVertex d → Prop} [DecidableRel R]
    (hR : ∀ {u v}, R u v → treeAdj u v)
    (hsymm : ∀ {u v}, R u v → R v u) (u v : TreeVertex d) :
    openAdj (edgeMask R) u v ↔ R u v := by
  constructor
  · rintro (⟨rfl, _, ho⟩ | ⟨rfl, _, ho⟩)
    · exact of_decide_eq_true ho
    · exact hsymm (of_decide_eq_true ho)
  · intro huv
    have hadj := hR huv
    rcases treeAdj_length hadj with hlen | hlen
    · have hlt : u.1.length < v.1.length := by omega
      have hp := treeAdj_parent_of_length_lt hadj hlt
      left
      refine ⟨hp.symm, ?_, ?_⟩
      · intro hn
        simp [hn] at hlt
      · simp only [edgeMask, hp, decide_eq_true_eq]
        exact huv
    · have hlt : v.1.length < u.1.length := by omega
      have hrev : treeAdj v u := hadj.elim Or.inr Or.inl
      have hp := treeAdj_parent_of_length_lt hrev hlt
      right
      refine ⟨hp.symm, ?_, ?_⟩
      · intro hn
        simp [hn] at hlt
      · simp only [edgeMask, hp, decide_eq_true_eq]
        exact hsymm huv

lemma connected_edgeMask_iff {R : TreeVertex d → TreeVertex d → Prop} [DecidableRel R]
    (hR : ∀ {u v}, R u v → treeAdj u v)
    (hsymm : ∀ {u v}, R u v → R v u) (u v : TreeVertex d) :
    Relation.ReflTransGen (openAdj (edgeMask R)) u v ↔ Relation.ReflTransGen R u v := by
  have heq : openAdj (edgeMask R) = R := by
    funext u v
    exact propext (openAdj_edgeMask_iff hR hsymm u v)
  rw [heq]

lemma openEdges_edgeMask (R : TreeVertex d → TreeVertex d → Prop) [DecidableRel R]
    (D : Finset (TreeVertex d)) :
    openEdges (edgeMask R) D = (inducedEdges D).filter (fun e => R e.1 e.2) := by
  classical
  apply Finset.filter_congr
  intro e he
  have he' := (Finset.mem_filter.mp he).2
  have hp := treeAdj_parent_of_length_lt he'.1 he'.2
  simp only [edgeMask, hp, decide_eq_true_eq]

theorem card_image_of_relation {A : Type*} [DecidableEq A]
    {R : TreeVertex d → TreeVertex d → Prop} [DecidableRel R]
    (hR : ∀ {u v}, R u v → treeAdj u v)
    (hsymm : ∀ {u v}, R u v → R v u)
    (label : TreeVertex d → A)
    (hlabel : ∀ u v, label u = label v ↔ Relation.ReflTransGen R u v)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D) :
    (D.image label).card =
      D.card - ((inducedEdges D).filter (fun e => R e.1 e.2)).card := by
  classical
  rw [← openEdges_edgeMask R D]
  apply card_image_componentLabel (edgeMask R) label _ hD
  intro u v
  exact (hlabel u v).trans (connected_edgeMask_iff hR hsymm u v).symm

end Problem367.ClusterComponentCount

end

end OAI
