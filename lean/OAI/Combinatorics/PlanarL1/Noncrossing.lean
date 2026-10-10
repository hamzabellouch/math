import OAI.Combinatorics.PlanarL1.Order

namespace OAI

section

namespace PlanarL1
/-! ## Noncrossing column words 
These are the exact combinatorial separation tools used in the surviving-seed
packing argument. The circular set has been cut at index 0. -/

namespace ColumnOrder

/-- No two links have four alternating, distinct endpoints in cyclic order. -/
def Noncrossing {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    ¬ (G.Adj a c ∧ G.Adj b d)

lemma noncrossing_comap_rotate {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hG : Noncrossing G) : Noncrossing (G.comap (finRotate (n + 1))) := by
  intro a b c d hab hbc hcd h
  have ha : a ≠ Fin.last n := by intro he; subst a; exact (not_lt_of_ge b.le_last) hab
  have hb : b ≠ Fin.last n := by intro he; subst b; exact (not_lt_of_ge c.le_last) hbc
  have hc : c ≠ Fin.last n := by intro he; subst c; exact (not_lt_of_ge d.le_last) hcd
  have hab' : finRotate _ a < finRotate _ b := by
    rw [Fin.lt_def, coe_finRotate_of_ne_last ha, coe_finRotate_of_ne_last hb]
    exact Nat.add_lt_add_right hab 1
  have hbc' : finRotate _ b < finRotate _ c := by
    rw [Fin.lt_def, coe_finRotate_of_ne_last hb, coe_finRotate_of_ne_last hc]
    exact Nat.add_lt_add_right hbc 1
  change G.Adj (finRotate _ a) (finRotate _ c) ∧ G.Adj (finRotate _ b) (finRotate _ d) at h
  by_cases hd : d = Fin.last n
  · have hz : (0 : Fin (n + 1)) < finRotate _ a := by
      rw [Fin.lt_def, coe_finRotate_of_ne_last ha]
      exact Nat.zero_lt_succ _
    rw [hd, finRotate_last] at h
    exact hG 0 (finRotate _ a) (finRotate _ b) (finRotate _ c) hz hab' hbc' ⟨h.2.symm,h.1⟩
  · have hcd' : finRotate _ c < finRotate _ d := by
      rw [Fin.lt_def, coe_finRotate_of_ne_last hc, coe_finRotate_of_ne_last hd]
      exact Nat.add_lt_add_right hcd 1
    exact hG _ _ _ _ hab' hbc' hcd' h

lemma noncrossing_comap_iterate {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hG : Noncrossing G) (k : ℕ) : Noncrossing (G.comap ((finRotate (n + 1))^[k])) := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    have h := noncrossing_comap_rotate ih
    simpa only [Function.iterate_succ, SimpleGraph.comap_comap] using h

lemma noncrossing_comap_cycle {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hG : Noncrossing G) (a : Fin (n + 1)) : Noncrossing (G.comap (finCycle a)) := by
  rw [finCycle_eq_finRotate_iterate]
  exact noncrossing_comap_iterate hG a.val


/-- An edge cannot leave the strict interior of a chord without meeting one
of the chord endpoints. -/
theorem adj_stays_between {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b x y : Fin n} (hab : G.Adj a b)
    (hax : a < x) (hxb : x < b) (hxy : G.Adj x y)
    (hya : y ≠ a) (hyb : y ≠ b) : a < y ∧ y < b := by
  have hleft : ¬ y < a := by
    intro h
    exact hnc y a x b h hax hxb ⟨hxy.symm, hab⟩
  have hright : ¬ b < y := by
    intro h
    exact hnc a x b y hax hxb h ⟨hab, hxy⟩
  constructor <;> omega

/-- A column word avoiding the endpoints of a chord remains on its starting
strict side. This is the induction behind the chord-separation lemma. -/
theorem walk_stays_between {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b x y : Fin n} (hab : G.Adj a b)
    (p : G.Walk x y) (hx : a < x ∧ x < b)
    (ha : a ∉ p.support) (hb : b ∉ p.support) : a < y ∧ y < b := by
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih =>
    have haz : z ≠ a := by
      intro h
      apply ha
      exact List.mem_cons_of_mem x (h ▸ p.start_mem_support)
    have hbz : z ≠ b := by
      intro h
      apply hb
      exact List.mem_cons_of_mem x (h ▸ p.start_mem_support)
    have hz := adj_stays_between hnc hab hx.1 hx.2 hxz haz hbz
    exact ih hz (fun h => ha (by simp [h])) (fun h => hb (by simp [h]))

/-- Geometry, Lemma `geo:chord-separation`, with a cut in the circular order
outside the chosen strict interval. It applies to paths as well as walks. -/
theorem chord_separation {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b x y : Fin n} (hab : G.Adj a b)
    (p : G.Walk x y) (hx : a < x ∧ x < b)
    (hy : y < a ∨ b < y) : a ∈ p.support ∨ b ∈ p.support := by
  by_contra h
  push Not at h
  have hi := walk_stays_between hnc hab p hx h.1 h.2
  rcases hy with hy | hy <;> omega

/-- Occurrence of a step of the word that skips the specified index strictly. -/
def JumpsAcross {n : ℕ} {G : SimpleGraph (Fin n)} (i : Fin n)
    {x y : Fin n} (p : G.Walk x y) : Prop :=
  ∃ e ∈ p.darts, (e.fst < i ∧ i < e.snd) ∨ (e.snd < i ∧ i < e.fst)

/-- Geometry, Lemma `geo:skipping`: passage from one side of an index to the
other either visits it or has a step jumping strictly across it. -/
theorem visits_or_skips {n : ℕ} {G : SimpleGraph (Fin n)} {i x y : Fin n}
    (p : G.Walk x y) (hx : x < i) (hy : i < y) :
    i ∈ p.support ∨ JumpsAcross i p := by
  induction p with
  | nil => omega
  | @cons x z y hxz p ih =>
    by_cases hz : z = i
    · left
      exact List.mem_cons_of_mem x (hz ▸ p.start_mem_support)
    by_cases hzi : z < i
    · rcases ih hzi hy with hm | ⟨e, he, hcross⟩
      · left
        simp [hm]
      · right
        exact ⟨e, by simp [he], hcross⟩
    · right
      refine ⟨⟨(x, z), hxz⟩, ?_, Or.inl ⟨hx, ?_⟩⟩
      · simp
      · change i < z
        omega

/-- A connected set is a barrier between any two of its vertices in the
linear order. The edge and the set's connecting paths may belong to different
subgraphs; only noncrossing in the common ambient graph matters. -/
lemma adj_between_connected {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S : Set (Fin n)} (hS : (G.induce S).Preconnected)
    {a b x y : Fin n} (ha : a ∈ S) (hb : b ∈ S)
    (hx : a < x ∧ x < b) (hxy : G.Adj x y) (hxs : x ∉ S) (hys : y ∉ S) :
    a < y ∧ y < b := by
  have hya : y ≠ a := fun h => hys (h ▸ ha)
  have hyb : y ≠ b := fun h => hys (h ▸ hb)
  obtain ⟨q⟩ := hS ⟨a, ha⟩ ⟨b, hb⟩
  let p := q.map (SimpleGraph.Embedding.induce S).toHom
  have hmem : ∀ v ∈ p.support, v ∈ S := by
    intro v hv
    obtain ⟨w, _, hw⟩ := List.mem_map.mp (by simpa only [p, SimpleGraph.Walk.support_map] using hv)
    exact hw ▸ w.property
  have hpx : x ∉ p.support := fun h => hxs (hmem x h)
  have hpy : y ∉ p.support := fun h => hys (hmem y h)
  have hleft : ¬ y < a := by
    intro h
    have he := chord_separation hnc hxy.symm p ⟨h, hx.1⟩ (Or.inr hx.2)
    exact he.elim hpy hpx
  have hright : ¬ b < y := by
    intro h
    have he := chord_separation hnc hxy p.reverse ⟨hx.2, h⟩ (Or.inl hx.1)
    exact he.elim (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hpx)
      (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hpy)
  constructor <;> omega

/-- Paths avoiding a connected set have constant membership in every interval
whose endpoints belong to that set. This is the cut-independent content of
`geo:gap`: such a path stays in one open circular gap. -/
lemma walk_same_gap {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S : Set (Fin n)} (hS : (G.induce S).Preconnected)
    {x y : Fin n} (p : G.Walk x y) (hp : ∀ v ∈ p.support, v ∉ S)
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) :
    (a < x ∧ x < b) ↔ (a < y ∧ y < b) := by
  suffices ∀ {x y : Fin n} (p : G.Walk x y), (∀ v ∈ p.support, v ∉ S) →
      a < x ∧ x < b → a < y ∧ y < b by
    constructor
    · exact this p hp
    · apply this p.reverse
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hp
  intro x y p hp hx
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih =>
    have hz := adj_between_connected hnc hS ha hb hx hxz
      (hp x (by simp)) (hp z (List.mem_cons_of_mem _ p.start_mem_support))
    exact ih (fun v hv => hp v (by simp [hv])) hz

/-- Disjoint connected vertex sets cannot have representatives in alternating
circular order. This upgrades the individual-chord barrier to branch sets. -/
lemma connected_noninterleaving {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S T : Set (Fin n)}
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hdis : Disjoint S T) {a b c d : Fin n}
    (ha : a ∈ S) (hb : b ∈ T) (hc : c ∈ S) (hd : d ∈ T)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : False := by
  obtain ⟨q⟩ := hT ⟨b, hb⟩ ⟨d, hd⟩
  let p := q.map (SimpleGraph.Embedding.induce T).toHom
  have hp : ∀ v ∈ p.support, v ∉ S := by
    intro v hv hvs
    obtain ⟨w, _, hw⟩ := List.mem_map.mp (by simpa only [p, SimpleGraph.Walk.support_map] using hv)
    have hvt : v ∈ T := hw ▸ w.property
    exact Set.disjoint_left.mp hdis hvs hvt
  have hi := (walk_same_gap hnc hS p hp ha hc).mp ⟨hab, hbc⟩
  exact (not_lt_of_ge hcd.le) hi.2

/-- A genuine finite branch-set model of a graph minor. Each branch is
nonempty and connected; branches are disjoint and edges are witnessed by
actual ambient edges. No topological or minor-exclusion axiom is hidden here. -/
structure BranchModel {n : ℕ} {W : Type*} (H : SimpleGraph W)
    (G : SimpleGraph (Fin n)) where
  branch : W → Set (Fin n)
  nonempty : ∀ w, (branch w).Nonempty
  connected : ∀ w, (G.induce (branch w)).Preconnected
  disjoint : Pairwise (fun i j => Disjoint (branch i) (branch j))
  edge : ∀ {i j}, H.Adj i j → ∃ a ∈ branch i, ∃ b ∈ branch j, G.Adj a b

namespace BranchModel

variable {n : ℕ} {W : Type*} {H : SimpleGraph W} {G : SimpleGraph (Fin n)}

lemma representative_injective (B : BranchModel H G) (r : W → Fin n)
    (hr : ∀ i, r i ∈ B.branch i) : Function.Injective r := by
  intro i j hij
  by_contra h
  exact Set.disjoint_left.mp (B.disjoint h) (hr i) (hij ▸ hr j)

lemma union_connected (B : BranchModel H G) {i j : W} (h : H.Adj i j) :
    (G.induce (B.branch i ∪ B.branch j)).Connected := by
  obtain ⟨a, ha, b, hb, hab⟩ := B.edge h
  exact SimpleGraph.connected_induce_union (B.connected i) (B.connected j) ha hb hab

/-- Noncrossing is inherited by every genuine branch-set minor, using any
chosen representative of each branch. This proves the needed minor closure
directly from walk separation, without a planar cone or a Jordan-curve axiom. -/
lemma noncrossing (B : BranchModel H G) (hnc : Noncrossing G)
    (r : W ↪ Fin n) (hr : ∀ i, r i ∈ B.branch i) : Noncrossing (H.map r) := by
  intro a b c d hab hbc hcd he
  obtain ⟨i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj r H a c).mp he.1
  obtain ⟨k, l, hkl, rfl, rfl⟩ := (SimpleGraph.map_adj r H b d).mp he.2
  apply connected_noninterleaving hnc (B.union_connected hij).preconnected
    (B.union_connected hkl).preconnected _ (Or.inl (hr i)) (Or.inl (hr k))
    (Or.inr (hr j)) (Or.inr (hr l)) hab hbc hcd
  apply Set.disjoint_union_left.mpr
  constructor <;> apply Set.disjoint_union_right.mpr
  · constructor
    · exact B.disjoint (fun h => (ne_of_lt hab) (congrArg r h))
    · exact B.disjoint (fun h => (ne_of_lt (hab.trans (hbc.trans hcd))) (congrArg r h))
  · constructor
    · exact B.disjoint (fun h => (ne_of_lt hbc) (congrArg r h).symm)
    · exact B.disjoint (fun h => (ne_of_lt hcd) (congrArg r h))

end BranchModel

/-- For two fixed hubs in a noncrossing graph, two distinct common neighbors
must lie on opposite open circular arcs of the hubs. -/
lemma common_neighbors_opposite {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b c d : Fin n} (hab : a < b) (hcd : c ≠ d)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) :
    (a < c ∧ c < b) ↔ ¬ (a < d ∧ d < b) := by
  have hac' := hac.ne
  have had' := had.ne
  have hbc' := hbc.ne
  have hbd' := hbd.ne
  have h1 : ¬ (a < c ∧ c < d ∧ d < b) := fun h =>
    hnc a c d b h.1 h.2.1 h.2.2 ⟨had, hbc.symm⟩
  have h2 : ¬ (a < d ∧ d < c ∧ c < b) := fun h =>
    hnc a d c b h.1 h.2.1 h.2.2 ⟨hac, hbd.symm⟩
  have h3 : ¬ (c < d ∧ d < a) := fun h =>
    hnc c d a b h.1 h.2 hab ⟨hac.symm, hbd.symm⟩
  have h4 : ¬ (d < c ∧ c < a) := fun h =>
    hnc d c a b h.1 h.2 hab ⟨had.symm, hbc.symm⟩
  have h5 : ¬ (b < c ∧ c < d) := fun h =>
    hnc a b c d hab h.1 h.2 ⟨hac, hbd⟩
  have h6 : ¬ (b < d ∧ d < c) := fun h =>
    hnc a b d c hab h.1 h.2 ⟨had, hbc⟩
  have h7 : ¬ (c < a ∧ b < d) := fun h =>
    hnc c a b d h.1 hab h.2 ⟨hbc.symm, had⟩
  have h8 : ¬ (d < a ∧ b < c) := fun h =>
    hnc d a b c h.1 hab h.2 ⟨hbd.symm, hac⟩
  omega

lemma no_three_common_neighbors {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b c d e : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hac : G.Adj a c) (had : G.Adj a d) (hae : G.Adj a e)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hbe : G.Adj b e) : False := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · have h1 := common_neighbors_opposite hnc hab hcd hac had hbc hbd
    have h2 := common_neighbors_opposite hnc hab hce hac hae hbc hbe
    have h3 := common_neighbors_opposite hnc hab hde had hae hbd hbe
    tauto
  · have h1 := common_neighbors_opposite hnc hab hcd hbc hbd hac had
    have h2 := common_neighbors_opposite hnc hab hce hbc hbe hac hae
    have h3 := common_neighbors_opposite hnc hab hde hbd hbe had hae
    tauto

/-- Geometry `geo:outerplanar`: no noncrossing circular graph has a
branch-set minor with two hubs and three distinct common neighbors. -/
lemma BranchModel.no_three_common_neighbors {n : ℕ} {W : Type*}
    {H : SimpleGraph W} {G : SimpleGraph (Fin n)} (B : BranchModel H G)
    (hnc : Noncrossing G) {a b c d e : W} (hab : a ≠ b)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hac : H.Adj a c) (had : H.Adj a d) (hae : H.Adj a e)
    (hbc : H.Adj b c) (hbd : H.Adj b d) (hbe : H.Adj b e) : False := by
  classical
  let r : W → Fin n := fun i => (B.nonempty i).choose
  have hr : ∀ i, r i ∈ B.branch i := fun i => (B.nonempty i).choose_spec
  let f : W ↪ Fin n := ⟨r, B.representative_injective r hr⟩
  have he {i j : W} (h : H.Adj i j) : (H.map f).Adj (f i) (f j) :=
    (SimpleGraph.map_adj f H (f i) (f j)).mpr ⟨i, j, h, rfl, rfl⟩
  exact PlanarL1.ColumnOrder.no_three_common_neighbors (B.noncrossing hnc f hr)
    (fun h => hab (f.injective h)) (fun h => hcd (f.injective h))
    (fun h => hce (f.injective h)) (fun h => hde (f.injective h))
    (he hac) (he had) (he hae) (he hbc) (he hbd) (he hbe)

/-- Trimming a connector after its last visit to one set and before its first
visit to the other. The nonadjacency assumption guarantees a nonempty core.
The proof minimizes the number of edges, not the metric length. -/
lemma connector_core {V : Type*} {G : SimpleGraph V} {C L T : Set V}
    (hCL : Disjoint C L) (hno : ∀ x ∈ C, ∀ y ∈ L, ¬ G.Adj x y)
    {x y : V} (hx : x ∈ C) (hy : y ∈ L) (p : G.Walk x y)
    (hp : ∀ v ∈ p.support, v ∈ T) :
    ∃ K : Set V, K.Nonempty ∧ (G.induce K).Preconnected ∧ K ⊆ T ∧
      Disjoint K C ∧ Disjoint K L ∧
      (∃ a ∈ C, ∃ b ∈ K, G.Adj a b) ∧
      (∃ a ∈ L, ∃ b ∈ K, G.Adj a b) := by
  classical
  let P : ℕ → Prop := fun m => ∃ a ∈ C, ∃ b ∈ L, ∃ q : G.Walk a b,
    q.length = m ∧ ∀ v ∈ q.support, v ∈ T
  have hex : ∃ m, P m := ⟨p.length, x, hx, y, hy, p, rfl, hp⟩
  obtain ⟨a, ha, b, hb, q, hlen, hmem⟩ := Nat.find_spec hex
  have hmin {c d : V} (hc : c ∈ C) (hd : d ∈ L) (r : G.Walk c d)
      (hr : ∀ v ∈ r.support, v ∈ T) : q.length ≤ r.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨c, hc, d, hd, r, rfl, hr⟩
  cases q with
  | nil => exact False.elim (Set.disjoint_left.mp hCL ha hb)
  | @cons a c b hac q =>
    have hq : ¬ q.Nil := by
      intro h
      have he := h.eq
      subst b
      exact hno a ha c hb hac
    let r := q.dropLast
    have hlast : G.Adj q.penultimate b := q.adj_penultimate hq
    have hrmem : ∀ v ∈ r.support, v ∈ T := by
      intro v hv
      apply hmem v
      apply List.mem_cons_of_mem
      exact List.mem_of_mem_dropLast (by simpa only [r, q.support_dropLast hq] using hv)
    have hshort : r.length + 1 = q.length := q.length_dropLast_add_one hq
    have hout : ∀ v ∈ r.support, v ∉ C ∧ v ∉ L := by
      intro v hv
      constructor
      · intro hvC
        have hh := hmin hvC hb ((r.dropUntil v hv).concat hlast) (by
          intro z hz
          rw [SimpleGraph.Walk.support_concat] at hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hrmem z (r.support_dropUntil_subset_support hv hz)
          · have hz' : z = b := List.mem_singleton.mp hz
            subst z
            exact hmem b (SimpleGraph.Walk.cons hac q).end_mem_support)
        have hd := r.length_dropUntil_le_length hv
        simp only [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_cons] at hh
        omega
      · intro hvL
        have hh := hmin ha hvL (SimpleGraph.Walk.cons hac (r.takeUntil v hv)) (by
          intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · subst z
            exact hmem a (SimpleGraph.Walk.cons hac q).start_mem_support
          · exact hrmem z (r.support_takeUntil_subset_support hv hz))
        have hd := r.length_takeUntil_le_length hv
        simp only [SimpleGraph.Walk.length_cons] at hh
        omega
    refine ⟨{v | v ∈ r.support}, ⟨c, r.start_mem_support⟩,
      r.connected_induce_support.preconnected, hrmem, ?_, ?_,
      ⟨a, ha, c, r.start_mem_support, hac⟩,
      ⟨b, hb, q.penultimate, r.end_mem_support, hlast.symm⟩⟩
    · exact Set.disjoint_left.mpr (fun v hv hvC => (hout v hv).1 hvC)
    · exact Set.disjoint_left.mpr (fun v hv hvL => (hout v hv).2 hvL)

/-- Three disjoint connected connector cores between two disjoint connected
sets would give the forbidden `K₂,₃` minor. -/
lemma no_three_cores {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {C L : Set (Fin n)} (hC : C.Nonempty) (hL : L.Nonempty)
    (hc : (G.induce C).Preconnected) (hl : (G.induce L).Preconnected)
    (hCL : Disjoint C L) (K : Fin 3 → Set (Fin n))
    (hne : ∀ i, (K i).Nonempty) (hconn : ∀ i, (G.induce (K i)).Preconnected)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hdC : ∀ i, Disjoint (K i) C) (hdL : ∀ i, Disjoint (K i) L)
    (heC : ∀ i, ∃ a ∈ C, ∃ b ∈ K i, G.Adj a b)
    (heL : ∀ i, ∃ a ∈ L, ∃ b ∈ K i, G.Adj a b) : False := by
  let H := completeBipartiteGraph Bool (Fin 3)
  let B : BranchModel H G := {
    branch := Sum.elim (fun b : Bool => cond b C L) K
    nonempty := by
      intro i
      rcases i with i | i
      · cases i
        · exact hL
        · exact hC
      · exact hne i
    connected := by
      intro i
      rcases i with i | i
      · cases i
        · exact hl
        · exact hc
      · exact hconn i
    disjoint := by
      intro i j hij
      rcases i with i | i <;> rcases j with j | j
      · cases i <;> cases j
        · exact False.elim (hij rfl)
        · exact hCL.symm
        · exact hCL
        · exact False.elim (hij rfl)
      · cases i
        · exact (hdL j).symm
        · exact (hdC j).symm
      · cases j
        · exact hdL i
        · exact hdC i
      · exact hdis (fun h => hij (congrArg Sum.inr h))
    edge := by
      intro i j hij
      rcases i with i | i <;> rcases j with j | j
      · simp [H, completeBipartiteGraph] at hij
      · cases i
        · exact heL j
        · exact heC j
      · cases j
        · obtain ⟨a, ha, b, hb, hab⟩ := heL i
          exact ⟨b, hb, a, ha, hab.symm⟩
        · obtain ⟨a, ha, b, hb, hab⟩ := heC i
          exact ⟨b, hb, a, ha, hab.symm⟩
      · simp [H, completeBipartiteGraph] at hij }
  apply B.no_three_common_neighbors hnc
    (a := Sum.inl false) (b := Sum.inl true)
    (c := Sum.inr 0) (d := Sum.inr 1) (e := Sum.inr 2)
  all_goals simp [H, completeBipartiteGraph]

/-- The projected disjoint short portions used in the two-portals argument
cannot exist. This includes the trimming and nonempty-interior justifications. -/
lemma no_three_connectors {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {C L : Set (Fin n)} (hc : (G.induce C).Preconnected)
    (hl : (G.induce L).Preconnected) (hCL : Disjoint C L)
    (hno : ∀ x ∈ C, ∀ y ∈ L, ¬ G.Adj x y)
    (x y : Fin 3 → Fin n) (hx : ∀ i, x i ∈ C) (hy : ∀ i, y i ∈ L)
    (p : ∀ i, G.Walk (x i) (y i))
    (hdis : Pairwise (fun i j => Disjoint
      {v | v ∈ (p i).support} {v | v ∈ (p j).support})) : False := by
  classical
  have hcores := fun i => connector_core hCL hno (hx i) (hy i) (p i) (fun _ h => h)
  choose K hne hk hsub hdC hdL heC heL using hcores
  exact no_three_cores hnc ⟨x 0, hx 0⟩ ⟨y 0, hy 0⟩ hc hl hCL K hne hk
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j)) hdC hdL heC heL

/-- The vertices of an induced-graph component, as a set in the original
vertex type. Components here are Mathlib's actual reachability quotients. -/
def componentColumns {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) : Set V := Subtype.val '' C.supp

lemma componentColumns_subset {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) : componentColumns C ⊆ S := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

lemma componentColumns_connected {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) : (G.induce (componentColumns C)).Connected := by
  let f : C.toSimpleGraph →g G.induce (componentColumns C) :=
    ⟨fun v => ⟨v.val.val, ⟨v.val, v.property, rfl⟩⟩, fun h => h⟩
  have : Nonempty (componentColumns C) := by
    obtain ⟨v, hv⟩ := C.nonempty_supp
    exact ⟨⟨v.val, ⟨v, hv, rfl⟩⟩⟩
  refine ⟨?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact (C.reachable_toSimpleGraph hu hv).map f

lemma componentColumns_adj {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) {x y : V}
    (hx : x ∈ componentColumns C) (hxy : G.Adj x y) (hy : y ∈ S) :
    y ∈ componentColumns C := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, C.mem_supp_of_adj_mem_supp hu hxy, rfl⟩

/-- Any walk inside the induced vertex set propagates membership in an
actual connected component. -/
lemma componentColumns_of_walk {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) {x y : V} (p : G.Walk x y)
    (hx : x ∈ componentColumns C) (hp : ∀ v ∈ p.support, v ∈ S) :
    y ∈ componentColumns C := by
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih =>
    exact ih (componentColumns_adj C hx hxz (hp z (by simp)))
      (fun v hv => hp v (by simp [hv]))

/-- A nonempty induced-connected subset lies in one actual component of
any larger induced subgraph. -/
lemma exists_component_containing {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hne : S.Nonempty) (hS : (G.induce S).Preconnected) (hST : S ⊆ T) :
    ∃ C : (G.induce T).ConnectedComponent, S ⊆ componentColumns C := by
  obtain ⟨x, hx⟩ := hne
  let C := (G.induce T).connectedComponentMk ⟨x, hST hx⟩
  refine ⟨C, ?_⟩
  intro y hy
  obtain ⟨w⟩ := hS ⟨x, hx⟩ ⟨y, hy⟩
  let p := w.map (SimpleGraph.Embedding.induce S).toHom
  apply componentColumns_of_walk C p
  · exact ⟨⟨x, hST hx⟩, rfl, rfl⟩
  · intro v hv
    obtain ⟨z, _, hz⟩ := List.mem_map.mp
      (by simpa only [p, SimpleGraph.Walk.support_map] using hv)
    exact hz ▸ hST z.property

/-- Components of one induced graph sharing an original vertex are equal. -/
lemma component_eq_of_column {V : Type*} {G : SimpleGraph V} {S : Set V}
    {C D : (G.induce S).ConnectedComponent} {i : V}
    (hC : i ∈ componentColumns C) (hD : i ∈ componentColumns D) : C = D := by
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨y, hy, hyx⟩ := hD
  have he : y = x := Subtype.ext hyx
  subst y
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hx hy

/-- The parent component under inclusion of vertex sets. -/
def componentAbove {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hST : S ⊆ T) (C : (G.induce S).ConnectedComponent) :
    (G.induce T).ConnectedComponent :=
  C.map ⟨fun x => ⟨x.val, hST x.property⟩, fun h => h⟩

lemma componentColumns_above {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hST : S ⊆ T) (C : (G.induce S).ConnectedComponent) :
    componentColumns C ⊆ componentColumns (componentAbove hST C) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨x.val, hST x.property⟩, ?_, rfl⟩
  change (G.induce T).connectedComponentMk _ = componentAbove hST C
  change (G.induce S).connectedComponentMk x = C at hx
  rw [← hx]
  rfl

/-- A discrete connected union of two metric balls has controlled diameter.
The single edge allowance avoids assuming any continuous realization of the
column graph. It will be absorbed by the source's 10D constant. -/
lemma connected_two_balls {V X : Type*} [PseudoMetricSpace X] {G : SimpleGraph V}
    (hG : G.Preconnected) (f : V → X) (p q : X) {R a : ℝ} (hR : 0 ≤ R)
    (ha : 0 ≤ a) (hedge : ∀ i j, G.Adj i j → dist (f i) (f j) ≤ a)
    (hcover : ∀ i, dist (f i) p ≤ R ∨ dist (f i) q ≤ R) (x y : V) :
    dist (f x) (f y) ≤ 4 * R + a := by
  have near : ∀ i j, dist (f i) p ≤ R → dist (f j) q ≤ R →
      dist p q ≤ 2 * R + a → dist (f i) (f j) ≤ 4 * R + a := by
    intro i j hi hj hpq
    have h₁ := dist_triangle (f i) p (f j)
    have h₂ := dist_triangle p q (f j)
    rw [dist_comm q (f j)] at h₂
    linarith
  by_cases hpq : dist p q ≤ 2 * R + a
  · rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
    · have h := dist_triangle (f x) p (f y)
      rw [dist_comm p (f y)] at h
      linarith
    · exact near x y hx hy hpq
    · rw [dist_comm]
      exact near y x hy hx hpq
    · have h := dist_triangle (f x) q (f y)
      rw [dist_comm q (f y)] at h
      linarith
  · have stay : ∀ {i j} (w : G.Walk i j), dist (f i) p ≤ R → dist (f j) p ≤ R := by
      intro i j w
      induction w with
      | nil => exact id
      | @cons i z j hiz w ih =>
        intro hi
        apply ih
        rcases hcover z with hz | hz
        · exact hz
        · exfalso
          apply hpq
          have h₁ := dist_triangle p (f i) q
          have h₂ := dist_triangle (f i) (f z) q
          rw [dist_comm p (f i)] at h₁
          linarith [hedge i z hiz]
    rcases hcover x with hx | hx
    · obtain ⟨w⟩ := hG x y
      have hy := stay w hx
      have h := dist_triangle (f x) p (f y)
      rw [dist_comm p (f y)] at h
      linarith
    · rcases hcover y with hy | hy
      · obtain ⟨w⟩ := hG y x
        have hx' := stay w hy
        have h := dist_triangle (f x) p (f y)
        rw [dist_comm p (f y)] at h
        linarith
      · have h := dist_triangle (f x) q (f y)
        rw [dist_comm q (f y)] at h
        linarith

/-- Walks transport through a relabelling without introducing any new visited
columns. This is used to cut the circular order at a chosen root. -/
lemma walk_comap_equiv {n : ℕ} {G : SimpleGraph (Fin n)} (e : Fin n ≃ Fin n)
    {i j : Fin n} (w : G.Walk (e i) (e j)) :
    ∃ p : (G.comap e).Walk i j, ∀ z ∈ p.support, e z ∈ w.support := by
  let f := (SimpleGraph.Iso.comap e G).symm.toHom
  have hi : f (e i) = i := e.symm_apply_apply i
  have hj : f (e j) = j := e.symm_apply_apply j
  refine ⟨(w.map f).copy hi hj, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨v,hv,hvz⟩ := hz
  have he : e.symm v = z := hvz
  rw [← he, e.apply_symm_apply]
  exact hv

/-- Collision inequality for a profile whose strict sublevels connect back to
zero. The ceiling is kept explicit: only thresholds at or below it are used. -/
lemma collision {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hnc : Noncrossing G) (f : Fin (n + 1) → ℝ) (D : ℝ)
    (hbound : ∀ i, f i ≤ D)
    (hpath : ∀ t ≤ D, ∀ i, f i < t →
      ∃ w : G.Walk i 0, ∀ z ∈ w.support, f z < t)
    {p q : Fin (n + 1)} (_hpq : p < q) (hadj : G.Adj p q) (heq : f p = f q)
    (hp : p ≠ 0) (z : Fin (n + 1)) (hpz : p ≤ z) (hzq : z ≤ q) : f p ≤ f z := by
  by_contra hn
  have hz : f z < f p := lt_of_not_ge hn
  have hpz' : p < z := lt_of_le_of_ne hpz (by intro he; subst z; exact (lt_irrefl _) hz)
  have hzq' : z < q := lt_of_le_of_ne hzq (by intro he; subst z; exact (not_lt_of_ge heq.le) hz)
  obtain ⟨w,hw⟩ := hpath _ (hbound p) z hz
  have h0 : (0 : Fin (n + 1)) < p := lt_of_le_of_ne (Fin.zero_le p) (Ne.symm hp)
  rcases chord_separation hnc hadj w ⟨hpz',hzq'⟩ (Or.inl h0) with hpw | hqw
  · exact (lt_irrefl _) (hw p hpw)
  · exact (not_lt_of_ge heq.le) (hw q hqw)

end ColumnOrder

end PlanarL1

end

end OAI
