import OAI.Combinatorics.PlanarL1.Fields

namespace OAI

section

namespace PlanarL1.ColumnOrder

/-- The combinatorial core of overlapping traversals: a path reaching a
middle profile value intersects any path crossing that value if each switch
has small profile error. Monotonicity is needed only on their common arc. -/
lemma overlapping_words {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S : Set (Fin n)} {q : Fin n → ℝ}
    (hq : MonotoneOn q S) {x x' y y' i : Fin n}
    (p : G.Walk x x') (r : G.Walk y y')
    (hp : ∀ v ∈ p.support, v ∈ S) (hr : ∀ v ∈ r.support, v ∈ S)
    (hi : i ∈ p.support) {δ : ℝ}
    (hx : q x + δ < q i) (hy : q y < q i) (hy' : q i < q y')
    (hs : ∀ e ∈ r.darts, |q e.fst - q e.snd| ≤ δ) :
    ∃ v, v ∈ p.support ∧ v ∈ r.support := by
  have order {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (h : q u < q v) : u < v := by
    by_contra hn
    have := hq hv hu (le_of_not_gt hn)
    linarith
  have hiy : y < i := order (hr y r.start_mem_support) (hp i hi) hy
  have hiy' : i < y' := order (hp i hi) (hr y' r.end_mem_support) hy'
  rcases visits_or_skips r hiy hiy' with hm | ⟨e,he,hea⟩
  · exact ⟨i,hi,hm⟩
  have hef : e.fst ∈ r.support := r.dart_fst_mem_support_of_mem_darts he
  have hes : e.snd ∈ r.support := r.dart_snd_mem_support_of_mem_darts he
  have core (a b : Fin n) (hab : G.Adj a b)
      (ha : a ∈ r.support) (hb : b ∈ r.support)
      (hai : a < i) (hib : i < b) (hgap : |q a - q b| ≤ δ) :
      ∃ v, v ∈ p.support ∧ v ∈ r.support := by
    have hibq := hq (hp i hi) (hr b hb) hib.le
    have hxa : q x < q a := by
      have hh := (abs_le.mp hgap).1
      linarith
    have hxa' := order (hp x p.start_mem_support) (hr a ha) hxa
    let t := (p.takeUntil i hi).reverse
    have hmem : ∀ v ∈ t.support, v ∈ p.support := by
      intro v hv
      apply (p.isSubwalk_takeUntil hi).support_subset
      simpa only [t,SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
    rcases chord_separation hnc hab t ⟨hai,hib⟩ (Or.inl hxa') with hm | hm
    · exact ⟨a,hmem a hm,ha⟩
    · exact ⟨b,hmem b hm,hb⟩
  rcases hea with hea | hea
  · exact core e.fst e.snd e.adj hef hes hea.1 hea.2 (hs e he)
  · exact core e.snd e.fst e.adj.symm hes hef hea.1 hea.2
      (by simpa only [abs_sub_comm] using hs e he)

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model

namespace Path

variable {n : ℕ} {M : Model n} {J : Set ℝ}

lemma exists_trace_of_mem_support {i j v : Fin n} (p : M.Path J i j)
    {a b : ℝ} (hv : v ∈ p.word.support) : ∃ T, (v,T) ∈ p.trace a b := by
  induction p generalizing a with
  | nil i =>
    have he : v = i := by simpa only [word,SimpleGraph.Walk.support_nil,List.mem_singleton] using hv
    subst v
    exact ⟨a,rfl,Set.left_mem_uIcc⟩
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp hv with hv | hv
    · subst v
      exact ⟨a,Or.inl ⟨rfl,Set.left_mem_uIcc⟩⟩
    · obtain ⟨T,hT⟩ := ih hv (a := H)
      exact ⟨T,Or.inr hT⟩

end Path

namespace Field

variable {n : ℕ} {M : Model n} {J : Set ℝ} {L : NNReal}

lemma profile_error (F : M.Field J L) {η : ℝ}
    (hw : ∀ a ∈ J, ∀ b ∈ J, |a-b| ≤ η) (i : Fin n) (H T : J) :
    |F.value i H - F.value i T| ≤ L*η := by
  have he := (F.vertical i).dist_le_mul H T
  simp only [Real.dist_eq,Subtype.dist_eq] at he
  exact he.trans (mul_le_mul_of_nonneg_left (hw _ H.property _ T.property) L.coe_nonneg)

lemma profile_switch_error (F : M.Field J L) {η : ℝ}
    (hw : ∀ a ∈ J, ∀ b ∈ J, |a-b| ≤ η) (H : J) {i j : Fin n}
    (hij : (M.activeGraph J).Adj i j) :
    |F.value i H - F.value j H| ≤ 2*(L*η) := by
  obtain ⟨T,hT,hs⟩ := hij
  have hi := F.profile_error hw i H ⟨T,hT⟩
  have hj := F.profile_error hw j ⟨T,hT⟩ H
  rw [← F.switch i j ⟨T,hT⟩ hs] at hj
  have ht := abs_sub_le (F.value i H) (F.value i ⟨T,hT⟩) (F.value j H)
  linarith

/-- Ordered overlap with an arbitrary cut of the circular order. The same
proof applies to the other arc by negating the field and reversing paths.
Its conclusion is actual shared-column support, prior to metric estimates. -/
lemma overlap_columns (F : M.Field J L) (hJ : Set.OrdConnected J)
    (e : Fin n ≃ Fin n) (hnc : ColumnOrder.Noncrossing ((M.activeGraph J).comap e))
    (S : Set (Fin n)) (T : J)
    (ho : MonotoneOn (fun i => F.value (e i) T) S)
    {η u v : ℝ} (hw : ∀ a ∈ J, ∀ b ∈ J, |a-b| ≤ η)
    (hgap : 8*(L*η) < v-u)
    {i j k l : Fin n} (p : M.Path J i j) (r : M.Path J k l)
    (a b c d : J)
    (hp : ∀ z ∈ p.word.support, e.symm z ∈ S)
    (hr : ∀ z ∈ r.word.support, e.symm z ∈ S)
    (ha : F.value i a ≤ u) (hb : v ≤ F.value j b)
    (hc : F.value k c ≤ u) (hd : v ≤ F.value l d) :
    ∃ z, z ∈ p.word.support ∧ z ∈ r.word.support := by
  have hη : 0 ≤ η := by simpa using hw T.val T.property T.val T.property
  have hε : 0 ≤ (L : ℝ)*η := mul_nonneg L.coe_nonneg hη
  have huv : u ≤ v := by linarith
  obtain ⟨z,H,htrace,hmid⟩ := F.path_intermediate hJ p a b
    (c := (u+v)/2) (by linarith) (by linarith)
  have hz := p.trace_column htrace
  let f := (SimpleGraph.Iso.comap e (M.activeGraph J)).symm.toHom
  let P := p.word.map f
  let Q := r.word.map f
  have mem {x y : Fin n} (w : (M.activeGraph J).Walk x y) {z : Fin n}
      (hz : z ∈ (w.map f).support) : e z ∈ w.support := by
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (by simpa only [SimpleGraph.Walk.support_map] using hz)
    change e.symm t = z at he
    simpa only [← he,e.apply_symm_apply] using ht
  have hpS : ∀ z ∈ P.support, z ∈ S := by
    intro z hz
    have := hp (e z) (mem p.word hz)
    simpa only [e.symm_apply_apply] using this
  have hrS : ∀ z ∈ Q.support, z ∈ S := by
    intro z hz
    have := hr (e z) (mem r.word hz)
    simpa only [e.symm_apply_apply] using this
  have hzP : e.symm z ∈ P.support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have ep := F.profile_error hw i a T
  have ez := F.profile_error hw z H T
  have er := F.profile_error hw k c T
  have er' := F.profile_error hw l d T
  rw [hmid] at ez
  obtain ⟨t,htP,htQ⟩ := ColumnOrder.overlapping_words hnc ho P Q hpS hrS hzP
    (δ := 2*(L*η))
    (by change F.value (e (e.symm i)) T + _ < F.value (e (e.symm z)) T
        simp only [e.apply_symm_apply]; have := (abs_le.mp ep).1
        have := (abs_le.mp ez).2; linarith)
    (by change F.value (e (e.symm k)) T < F.value (e (e.symm z)) T
        simp only [e.apply_symm_apply]; have := (abs_le.mp er).1
        have := (abs_le.mp ez).2; linarith)
    (by change F.value (e (e.symm z)) T < F.value (e (e.symm l)) T
        simp only [e.apply_symm_apply]; have := (abs_le.mp er').2
        have := (abs_le.mp ez).1; linarith)
    (by intro edge _; exact F.profile_switch_error hw T edge.adj)
  exact ⟨e t,mem p.word htP,mem r.word htQ⟩

end Field
end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

/-- Stop at the first vertex outside a set. The constructed walk consists
only of original visited columns, and its last step crosses the set boundary. -/
lemma first_exit {V : Type*} {G : SimpleGraph V} {S : Set V} {x y : V}
    (p : G.Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ a b, G.Adj a b ∧ a ∈ S ∧ b ∉ S ∧
      ∃ r : G.Walk x b,
        (∀ v ∈ r.support, v ∈ p.support) ∧
        (∀ v ∈ r.support, v ∈ S ∨ v = b) := by
  induction p with
  | nil => exact False.elim (hy hx)
  | @cons x z y hxz p ih =>
    by_cases hz : z ∈ S
    · obtain ⟨a,b,hab,ha,hb,r,hr,hS⟩ := ih hz hy
      refine ⟨a,b,hab,ha,hb,r.cons hxz,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons_of_mem _ (hr v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact Or.inl (hv ▸ hx)
        · exact hS v hv
    · refine ⟨x,z,hxz,hx,hz,(.nil : G.Walk z z).cons hxz,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · have he : v = z := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hv
          exact List.mem_cons_of_mem _ (he ▸ p.start_mem_support)
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact Or.inl (hv ▸ hx)
        · right
          simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hv

/-- A discrete traversal of a value band. Every visited column lies in the
band enlarged by one switch error; no continuous path-parameter choice or
first/last hitting time is postulated. -/
lemma traverse_band {V : Type*} {G : SimpleGraph V} (q : V → ℝ) {δ u v : ℝ}
    (hδ : 0 ≤ δ) (huv : u < v) (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x y : V} (p : G.Walk x y) (hx : q x ≤ u) (hy : v ≤ q y) :
    ∃ a b, ∃ r : G.Walk a b,
      q a ≤ u ∧ v ≤ q b ∧
      (∀ z ∈ r.support, z ∈ p.support) ∧
      (∀ z ∈ r.support, u-δ ≤ q z ∧ q z ≤ v+δ) := by
  obtain ⟨a,b,hab,ha,hb,s,hs,hS⟩ := first_exit p
    (S := {z | q z < v}) (by dsimp; linarith) (by dsimp; linarith)
  change q a < v at ha
  change ¬q b < v at hb
  have hb' : v ≤ q b := le_of_not_gt hb
  have hbup : q b ≤ v+δ := by
    have := (abs_le.mp (hedge hab)).1
    linarith
  have hsupper (z) (hz : z ∈ s.support) : q z ≤ v+δ := by
    rcases hS z hz with hz | rfl
    · change q z < v at hz
      linarith
    · exact hbup
  obtain ⟨c,d,hcd,hc,hd,t,ht,hT⟩ := first_exit s.reverse
    (S := {z | u < q z}) (by dsimp; linarith) (by dsimp; linarith)
  change u < q c at hc
  change ¬u < q d at hd
  have hd' : q d ≤ u := le_of_not_gt hd
  have hdlow : u-δ ≤ q d := by
    have := (abs_le.mp (hedge hcd)).2
    linarith
  refine ⟨d,b,t.reverse,hd',hb',?_,?_⟩
  · intro z hz
    have hzt : z ∈ t.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
    have hzs : z ∈ s.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ht z hzt
    exact hs z hzs
  · intro z hz
    have hzt : z ∈ t.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
    have hzs : z ∈ s.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ht z hzt
    refine ⟨?_,hsupper z hzs⟩
    rcases hT z hzt with hz | rfl
    · change u < q z at hz
      linarith
    · exact hdlow

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model

namespace Path

variable {n : ℕ} {M : Model n} {I J : Set ℝ}

/-- The same finite path is permitted in a larger band. -/
def widen (hJI : J ⊆ I) {i j : Fin n} : M.Path J i j → M.Path I i j
  | .nil i => .nil i
  | .cons H hH hs p => .cons H (hJI hH) hs (widen hJI p)

lemma length_widen (hJI : J ⊆ I) {i j : Fin n} (p : M.Path J i j) (a b : ℝ) :
    (p.widen hJI).length a b = p.length a b := by
  induction p generalizing a with
  | nil => rfl
  | cons H hH hs p ih => simp only [widen,length,ih]

end Path

namespace Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Geometric control of visits to a set of columns. The witnesses are actual
points at heights in J and actual ambient-band distances from the center. -/
def NearColumns (x : M.Point I root) (J : Set ℝ) (A : ℝ) (S : Set (Fin n)) : Prop :=
  ∀ v ∈ S, ∃ z : M.Point I root, z.column = v ∧ z.height ∈ J ∧ dist x z ≤ A

lemma NearColumns.mono {x : M.Point I root} {A : ℝ} {S T : Set (Fin n)}
    (h : x.NearColumns J A S) (hTS : T ⊆ S) : x.NearColumns J A T :=
  fun v hv => h v (hTS hv)

lemma NearColumns.union {x : M.Point I root} {A : ℝ} {S T : Set (Fin n)}
    (hS : x.NearColumns J A S) (hT : x.NearColumns J A T) :
    x.NearColumns J A (S ∪ T) := fun v hv => hv.elim (hS v) (hT v)

/-- Every visited column of a path of length A from x has a point genuinely
reachable within A, even when the ambient metric permits leaving J. -/
lemma near_path (hJI : J ⊆ I) (x : M.Point I root) (hx : x.height ∈ J)
    {j : Fin n} (p : M.Path J x.column j) {H A : ℝ} (hH : H ∈ J)
    (hA : p.length x.height H ≤ A) :
    x.NearColumns J A {v | v ∈ p.word.support} := by
  intro v hv
  obtain ⟨T,hT,q,r,hqr⟩ := p.split_at_column hx hH hv
  let z : M.Point I root := ⟨v,T,hJI hT,x.reachable.trans (q.widen hJI).word.reachable⟩
  refine ⟨z,rfl,hT,?_⟩
  have hd := x.distance_le z (q.widen hJI)
  rw [Path.length_widen] at hd
  have hn := r.length_nonneg T H
  change x.distance z ≤ A
  dsimp only [z] at hd
  linarith

/-- Metric completion of the overlapping-traversal argument. Only one
vertical transfer is needed, hence eta rather than the source's 2 eta. -/
lemma dist_le_of_near_intersection (x y : M.Point I root) {A B η : ℝ}
    {S T : Set (Fin n)} (hx : x.NearColumns J A S) (hy : y.NearColumns J B T)
    (hw : ∀ a ∈ J, ∀ b ∈ J, |a-b| ≤ η) {v : Fin n} (hvS : v ∈ S) (hvT : v ∈ T) :
    dist x y ≤ A+B+η := by
  obtain ⟨z,hz,hzJ,hxz⟩ := hx v hvS
  obtain ⟨w,hwv,hwJ,hyw⟩ := hy v hvT
  have he := Point.dist_same_column z w (hz.trans hwv.symm)
  have hd := hw z.height hzJ w.height hwJ
  have h₁ := dist_triangle x z y
  have h₂ := dist_triangle z w y
  rw [dist_comm w y] at h₂
  linarith

end Point
end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

/-- A crosslink joining the two monotone arcs separates all strict lower
profile values from all strict upper values. This uses noncrossing of the
ambient graph, not an assumed connectivity of a scalar level set. -/
lemma ordered_chord_barrier {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) (f : Fin n → ℝ) (m : Fin n)
    (hleft : ∀ i j, i ≤ j → j ≤ m → f i ≤ f j)
    (hright : ∀ i j, m ≤ i → i ≤ j → f j ≤ f i)
    {a b x y : Fin n} (ham : a ≤ m) (hmb : m ≤ b)
    (hab : G.Adj a b) (heq : f a = f b)
    (p : G.Walk x y) (hx : f x < f a) (hy : f a < f y) :
    a ∈ p.support ∨ b ∈ p.support := by
  have hay : a < y := by
    by_contra hn
    have := hleft y a (le_of_not_gt hn) ham
    linarith
  have hyb : y < b := by
    by_contra hn
    have := hright b y hmb (le_of_not_gt hn)
    linarith
  have hside : x < a ∨ b < x := by
    by_cases hxm : x ≤ m
    · left
      by_contra hn
      have := hleft a x (le_of_not_gt hn) hxm
      linarith
    · right
      by_contra hn
      have := hright x b (le_of_not_ge hxm) (le_of_not_gt hn)
      linarith
  have hc := chord_separation hnc hab p.reverse ⟨hay,hyb⟩ hside
  simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hc

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k + 1)} {I J : Set ℝ} {L : NNReal}

lemma ordered_maximum (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (H : I) (i : Fin (k+1)) : F.value i H ≤ F.value b H := by
  let e := finCycle a
  rcases le_total (e.symm i) (e.symm b) with hi | hi
  · simpa only [e,Equiv.apply_symm_apply] using ho.2.1 H (e.symm i) (e.symm b) hi le_rfl
  · simpa only [e,Equiv.apply_symm_apply] using ho.2.2 H (e.symm b) (e.symm i) le_rfl hi

lemma arcSign_one_lt {a b i : Fin (k+1)} (h : arcSign a b i = 1) :
    (finCycle a).symm i < (finCycle a).symm b := by
  unfold arcSign at h
  split_ifs at h with hbd hlt
  · norm_num at h
  · exact hlt
  · norm_num at h

lemma arcSign_neg_one_gt {a b i : Fin (k+1)} (h : arcSign a b i = -1) :
    (finCycle a).symm b < (finCycle a).symm i := by
  unfold arcSign at h
  split_ifs at h with hbd hlt
  · norm_num at h
  · norm_num at h
  · have hib : i ≠ b := fun he => hbd (Or.inr he)
    have he : (finCycle a).symm i ≠ (finCycle a).symm b := fun he => hib ((finCycle a).symm.injective he)
    exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)

/-- Actual crosslink barrier for arbitrary finite paths in any band. The
crosslink itself may be outside that band, as required by the empty-wall
rectangle argument. -/
lemma crosslink_barrier (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (H : I) {u v : Fin (k+1)} (hs : H.val ∈ M.heights u v)
    (hu : arcSign a b u = 1) (hv : arcSign a b v = -1)
    {x y : Fin (k+1)} (p : (M.activeGraph J).Walk x y)
    (hx : F.value x H < F.value u H) (hy : F.value u H < F.value y H) :
    u ∈ p.support ∨ v ∈ p.support := by
  let e := finCycle a
  let f := (SimpleGraph.Iso.comap e M.link).symm.toHom
  let q := (p.mapLe (M.active_subgraph J)).map f
  have hnc := ColumnOrder.noncrossing_comap_cycle M.noncrossing a
  have heq : F.value (e (e.symm u)) H = F.value (e (e.symm v)) H := by
    simpa only [e.apply_symm_apply] using F.switch u v H hs
  have hc := ColumnOrder.ordered_chord_barrier hnc (fun i => F.value (e i) H) (e.symm b)
    (ho.2.1 H) (ho.2.2 H) (arcSign_one_lt hu).le (arcSign_neg_one_gt hv).le
    (a := e.symm u) (b := e.symm v) (by change M.link.Adj (e (e.symm u)) (e (e.symm v)); simpa only [e.apply_symm_apply] using M.permitted u v H.val hs)
    heq q
    (by change F.value (e (e.symm x)) H < F.value (e (e.symm u)) H; simpa only [e.apply_symm_apply] using hx)
    (by change F.value (e (e.symm u)) H < F.value (e (e.symm y)) H; simpa only [e.apply_symm_apply] using hy)
  have mem (z : Fin (k+1)) (hz : e.symm z ∈ q.support) : z ∈ p.support := by
    rw [SimpleGraph.Walk.support_map,SimpleGraph.Walk.support_mapLe_eq_support,List.mem_map] at hz
    obtain ⟨w,hw,he⟩ := hz
    have hwe : w = z := e.symm.injective he
    exact hwe ▸ hw
  exact hc.elim (fun h => Or.inl (mem u h)) (fun h => Or.inr (mem v h))

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Two controlled column sets each hitting an endpoint of the same actual
link can be joined through that link at its prescribed height. -/
lemma dist_le_of_near_link (x y : M.Point I root) {A B D H : ℝ}
    {S T : Set (Fin n)} (hx : x.NearColumns J A S) (hy : y.NearColumns J B T)
    (hD : ∀ t ∈ J, |t-H| ≤ D) (hH : H ∈ I)
    {u v : Fin n} (hlink : H ∈ M.heights u v)
    (hp : u ∈ S ∨ v ∈ S) (hq : u ∈ T ∨ v ∈ T) :
    dist x y ≤ A+B+2*D := by
  have core (z w : M.Point I root) (hz : z.height ∈ J) (hw : w.height ∈ J)
      (hxz : dist x z ≤ A) (hyw : dist y w ≤ B)
      (hzw : z.column = w.column ∨ H ∈ M.heights z.column w.column) :
      dist x y ≤ A+B+2*D := by
    have hd : dist z w ≤ 2*D := by
      rcases hzw with hzw | hzw
      · rw [Point.dist_same_column z w hzw]
        have he := abs_sub_le z.height H w.height
        have hzD := hD z.height hz
        have hwD := hD w.height hw
        rw [abs_sub_comm H w.height] at he
        linarith
      · have he := z.dist_le_switch w hH hzw
        have hzD := hD z.height hz
        have hwD := hD w.height hw
        rw [abs_sub_comm H w.height] at he
        linarith
    have ht := dist_triangle x z y
    have ht' := dist_triangle z w y
    rw [dist_comm w y] at ht'
    linarith
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx u hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy u hq
    exact core z w hzJ hwJ hxz hyw (Or.inl (hz.trans hw.symm))
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx u hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy v hq
    exact core z w hzJ hwJ hxz hyw (Or.inr (by simpa only [hz,hw] using hlink))
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx v hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy u hq
    exact core z w hzJ hwJ hxz hyw (Or.inr (by simpa only [hz,hw,M.symm v u] using hlink))
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx v hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy v hq
    exact core z w hzJ hwJ hxz hyw (Or.inl (hz.trans hw.symm))

end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {L : NNReal} {root : Fin (k+1)}

/-- Empty-wall rectangle, in its geometric form before inserting the source
constants. A hypothetical wall point between both controlled traversals
creates a quantitatively short ambient path. -/
lemma wall_traversal_distance (F : M.Field I L) {a b : Fin (k+1)}
    (ho : F.OrderedFrom a b) (H : I) {c A B D : ℝ}
    (hw : (c,H.val) ∈ F.wall a b)
    (x y : M.Point I root) {x₀ x₁ y₀ y₁ : Fin (k+1)}
    (p : (M.activeGraph J).Walk x₀ x₁) (q : (M.activeGraph J).Walk y₀ y₁)
    (hp : x.NearColumns J A {v | v ∈ p.support})
    (hq : y.NearColumns J B {v | v ∈ q.support})
    (hD : ∀ t ∈ J, |t-H.val| ≤ D)
    (hx₀ : F.value x₀ H < c) (hx₁ : c < F.value x₁ H)
    (hy₀ : F.value y₀ H < c) (hy₁ : c < F.value y₁ H) :
    dist x y ≤ A+B+2*D := by
  rcases hw with ⟨T,he⟩ | ⟨T,he⟩ | ⟨u,v,T,hs,hu,hv,he⟩
  · have hT : T = H := Subtype.ext (congrArg Prod.snd he).symm
    subst T
    have hc : c = F.value a H := congrArg Prod.fst he
    have := ho.1 H x₀
    exfalso
    linarith
  · have hT : T = H := Subtype.ext (congrArg Prod.snd he).symm
    subst T
    have hc : c = F.value b H := congrArg Prod.fst he
    have := F.ordered_maximum ho H x₁
    exfalso
    linarith
  · have hT : T = H := Subtype.ext (congrArg Prod.snd he).symm
    subst T
    have hc : c = F.value u H := congrArg Prod.fst he
    have hpu := F.crosslink_barrier ho H hs hu hv p (by rwa [← hc]) (by rwa [← hc])
    have hqu := F.crosslink_barrier ho H hs hu hv q (by rwa [← hc]) (by rwa [← hc])
    exact x.dist_le_of_near_link y hp hq hD H.property hs hpu hqu

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Field

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {L : NNReal} {root : Fin n}

abbrev eval (F : M.Field I L) (z : M.Point I root) : ℝ :=
  F.value z.column ⟨z.height,z.inBand⟩

/-- The genuine pair of short low/high paths in : no scalar
separation or arc conclusion is included as an assumption. -/
structure Excursions (F : M.Field I L) (hJI : J ⊆ I) (z : M.Point I root) (A ε : ℝ) where
  inBand : z.height ∈ J
  lowColumn : Fin n
  highColumn : Fin n
  lowHeight : J
  highHeight : J
  lowPath : M.Path J z.column lowColumn
  highPath : M.Path J z.column highColumn
  lowLength : lowPath.length z.height lowHeight.val ≤ A
  highLength : highPath.length z.height highHeight.val ≤ A
  lowValue : F.value lowColumn ⟨lowHeight.val,hJI lowHeight.property⟩ < F.eval z - ε
  highValue : F.eval z + ε < F.value highColumn ⟨highHeight.val,hJI highHeight.property⟩

namespace Excursions

variable {F : M.Field I L} {hJI : J ⊆ I} {z : M.Point I root} {A ε : ℝ}

def traversal (E : F.Excursions hJI z A ε) :
    (M.activeGraph J).Walk E.lowColumn E.highColumn :=
  E.lowPath.word.reverse.append E.highPath.word

lemma near_traversal (E : F.Excursions hJI z A ε) :
    z.NearColumns J A {v | v ∈ E.traversal.support} := by
  have hlo := z.near_path hJI E.inBand E.lowPath E.lowHeight.property E.lowLength
  have hhi := z.near_path hJI E.inBand E.highPath E.highHeight.property E.highLength
  intro v hv
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
  · exact hlo v (by
      change v ∈ E.lowPath.word.support
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv)
  · exact hhi v hv

lemma low_profile (E : F.Excursions hJI z A ε) (H : I) {D : ℝ}
    (hD : ∀ t ∈ J, |t-H.val| ≤ D) :
    F.value E.lowColumn H < F.eval z - ε + L*D := by
  have h := (F.vertical E.lowColumn).dist_le_mul
    (⟨E.lowHeight.val,hJI E.lowHeight.property⟩ : I) H
  simp only [Real.dist_eq,Subtype.dist_eq] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left (hD _ E.lowHeight.property) L.coe_nonneg)
  have h'' := (abs_le.mp h').1
  linarith [E.lowValue]

lemma high_profile (E : F.Excursions hJI z A ε) (H : I) {D : ℝ}
    (hD : ∀ t ∈ J, |t-H.val| ≤ D) :
    F.eval z + ε - L*D < F.value E.highColumn H := by
  have h := (F.vertical E.highColumn).dist_le_mul
    (⟨E.highHeight.val,hJI E.highHeight.property⟩ : I) H
  simp only [Real.dist_eq,Subtype.dist_eq] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left (hD _ E.highHeight.property) L.coe_nonneg)
  have h'' := (abs_le.mp h').2
  linarith [E.highValue]

end Excursions

/-- The closed wall-free rectangle with the manuscript's exact numerical
margins, uniform in every field, every finite column model and every size. -/
lemma empty_rectangle {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {root : Fin (k+1)}
    (F : M.Field I 4) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    {R η : ℝ} (hR : 0 < R) (hη : η ≤ R/1000000)
    (hJI : J ⊆ I) (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ η)
    (x y : M.Point I root)
    (Ex : F.Excursions hJI x (2*R) (2*R/5))
    (Ey : F.Excursions hJI y (2*R) (2*R/5))
    (hclose : |F.eval x-F.eval y| ≤ R/1000)
    (hfar : 4*R+2*(R/50+η) < dist x y)
    (H : I) {c : ℝ} (hc : |c-F.eval x| ≤ R/5) (hH : |H.val-x.height| ≤ R/50) :
    (c,H.val) ∉ F.wall a b := by
  intro hwall
  have hD : ∀ t ∈ J, |t-H.val| ≤ R/50+η := by
    intro t ht
    have h := abs_sub_le t x.height H.val
    have h' := hw t ht x.height Ex.inBand
    rw [abs_sub_comm x.height H.val] at h
    linarith
  have hxlo := Ex.low_profile H hD
  have hxhi := Ex.high_profile H hD
  have hylo := Ey.low_profile H hD
  have hyhi := Ey.high_profile H hD
  have hcv := abs_le.mp hc
  have hxy := abs_le.mp hclose
  norm_num only [NNReal.coe_ofNat] at hxlo hxhi hylo hyhi
  have hd := F.wall_traversal_distance ho H hwall x y Ex.traversal Ey.traversal
    Ex.near_traversal Ey.near_traversal hD
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- Quantitative wall avoidance implies an infimum-distance bound at any
center whose max-norm ball fits into the verified empty rectangle. -/
lemma infDist_lower_of_rectangle {k : ℕ} {M : Model (k+1)} {I : Set ℝ} {L : NNReal}
    (F : M.Field I L) (a b : Fin (k+1)) (T : I)
    {s h U V r : ℝ}
    (hempty : ∀ (c : ℝ) (H : I), |c-s| ≤ U → |H.val-h| ≤ V → (c,H.val) ∉ F.wall a b)
    (i : Fin (k+1)) (hU : |F.value i T-s|+r ≤ U) (hV : |T.val-h|+r ≤ V) :
    r ≤ Metric.infDist (F.value i T,T.val) (F.wall a b) := by
  apply (Metric.le_infDist (F.wall_nonempty a b T)).mpr
  intro z hz
  by_contra hn
  have hd : dist (F.value i T,T.val) z < r := lt_of_not_ge hn
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff] at hd
  have hzu : |z.1-s| ≤ U := by
    have ht := abs_sub_le z.1 (F.value i T) s
    rw [abs_sub_comm z.1 (F.value i T)] at ht
    linarith
  have hzv : |z.2-h| ≤ V := by
    have ht := abs_sub_le z.2 T.val h
    rw [abs_sub_comm z.2 T.val] at ht
    linarith
  have hzI : z.2 ∈ I := by
    rcases hz with ⟨H,rfl⟩ | ⟨H,rfl⟩ | ⟨u,v,H,_,_,_,rfl⟩ <;> exact H.property
  exact hempty z.1 ⟨z.2,hzI⟩ hzu hzv hz

end PlanarL1.Columns.Model.Field

namespace PlanarL1.ColumnOrder

/-- Discrete profile intervals suffice for overlap. The midpoint visit is
constructed by stopping at the first exiting column, including its switch error. -/
lemma overlapping_ranges {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {S : Set (Fin n)} {q : Fin n → ℝ} (hq : MonotoneOn q S)
    {δ u v : ℝ} (hgap : 2*δ < v-u)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x x' y y' : Fin n} (p : G.Walk x x') (r : G.Walk y y')
    (hp : ∀ z ∈ p.support, z ∈ S) (hr : ∀ z ∈ r.support, z ∈ S)
    (hx : q x ≤ u) (hx' : v ≤ q x') (hy : q y ≤ u) (hy' : v ≤ q y')
    (hδ : 0 ≤ δ) : ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  obtain ⟨a,b,hab,ha,hb,t,ht,_⟩ := first_exit p
    (S := {z | q z < (u+v)/2}) (by dsimp; linarith) (by dsimp; linarith)
  change q a < (u+v)/2 at ha
  change ¬q b < (u+v)/2 at hb
  have hb' : (u+v)/2 ≤ q b := le_of_not_gt hb
  have hbup : q b < (u+v)/2+δ := by
    have := (abs_le.mp (hedge hab)).1
    linarith
  exact overlapping_words hnc hq p r hp hr (ht b t.end_mem_support)
    (by linarith) (by linarith) (by linarith) (fun e _ => hedge e.adj)

lemma overlapping_ranges_anti {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {S : Set (Fin n)} {q : Fin n → ℝ} (hq : AntitoneOn q S)
    {δ u v : ℝ} (hgap : 2*δ < v-u)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x x' y y' : Fin n} (p : G.Walk x x') (r : G.Walk y y')
    (hp : ∀ z ∈ p.support, z ∈ S) (hr : ∀ z ∈ r.support, z ∈ S)
    (hx : q x ≤ u) (hx' : v ≤ q x') (hy : q y ≤ u) (hy' : v ≤ q y')
    (hδ : 0 ≤ δ) : ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  have hmono : MonotoneOn (fun z => -q z) S := by
    intro i hi j hj hij
    exact neg_le_neg (hq hi hj hij)
  have he {a b} (h : G.Adj a b) : |(-q a)-(-q b)| ≤ δ := by
    simpa only [neg_sub_neg,abs_sub_comm] using hedge h
  have hp' : ∀ z ∈ p.reverse.support, z ∈ S := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse]
  have hr' : ∀ z ∈ r.reverse.support, z ∈ S := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse]
  obtain ⟨z,hz,hz'⟩ := overlapping_ranges hnc hmono (u := -v) (v := -u)
    (by linarith) he p.reverse r.reverse hp' hr'
    (by linarith) (by linarith) (by linarith) (by linarith) hδ
  exact ⟨z,by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz,
    by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz'⟩

lemma walk_label_const {V K : Type*} {G : SimpleGraph V} {S : Set V} (label : V → K)
    (hedge : ∀ {a b}, G.Adj a b → a ∈ S → b ∈ S → label a = label b)
    {x y : V} (p : G.Walk x y) (hp : ∀ v ∈ p.support, v ∈ S) :
    ∀ v ∈ p.support, label v = label x := by
  induction p with
  | @nil x =>
    intro v hv
    have hv' : v = x := by simpa using hv
    subst v
    rfl
  | @cons x z y hxz p ih =>
    have hp' : ∀ v ∈ p.support, v ∈ S := fun v hv => hp v (List.mem_cons_of_mem x hv)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rfl
    · exact (ih hp' v hv).trans (hedge hxz (hp x (List.mem_cons_self ..))
        (hp' z p.start_mem_support)).symm

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {L : NNReal}

/-- Profile overlap on either open arc; the cyclic relabelling and the
antitone second arc are both explicit. -/
lemma same_arc_overlap (F : M.Field I L) {a b : Fin (k+1)}
    (ho : F.OrderedFrom a b) (H : I) {δ u v σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hδ : 0 ≤ δ) (hgap : 2*δ < v-u)
    (hedge : ∀ {i j}, (M.activeGraph J).Adj i j → |F.value i H-F.value j H| ≤ δ)
    {x x' y y' : Fin (k+1)} (p : (M.activeGraph J).Walk x x')
    (r : (M.activeGraph J).Walk y y')
    (hp : ∀ z ∈ p.support, arcSign a b z = σ)
    (hr : ∀ z ∈ r.support, arcSign a b z = σ)
    (hx : F.value x H ≤ u) (hx' : v ≤ F.value x' H)
    (hy : F.value y H ≤ u) (hy' : v ≤ F.value y' H) :
    ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  let e := finCycle a
  let f := (SimpleGraph.Iso.comap e (M.activeGraph J)).symm.toHom
  let P := p.map f
  let Q := r.map f
  let S : Set (Fin (k+1)) := {i | arcSign a b (e i) = σ}
  have mem {i j : Fin (k+1)} (t : (M.activeGraph J).Walk i j) {z}
      (hz : z ∈ (t.map f).support) : e z ∈ t.support := by
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    change e (e.symm w) ∈ t.support
    simpa only [e.apply_symm_apply] using hw
  have hP : ∀ z ∈ P.support, z ∈ S := fun z hz => hp _ (mem p hz)
  have hQ : ∀ z ∈ Q.support, z ∈ S := fun z hz => hr _ (mem r hz)
  have he {i j} (h : ((M.activeGraph J).comap e).Adj i j) :
      |F.value (e i) H-F.value (e j) H| ≤ δ := hedge h
  have hx0 : F.value (e (e.symm x)) H ≤ u := by simpa only [e.apply_symm_apply] using hx
  have hx1 : v ≤ F.value (e (e.symm x')) H := by simpa only [e.apply_symm_apply] using hx'
  have hy0 : F.value (e (e.symm y)) H ≤ u := by simpa only [e.apply_symm_apply] using hy
  have hy1 : v ≤ F.value (e (e.symm y')) H := by simpa only [e.apply_symm_apply] using hy'
  have hnc := ColumnOrder.noncrossing_comap_cycle (M.active_noncrossing J) a
  have hit : ∃ z, z ∈ P.support ∧ z ∈ Q.support := by
    rcases hσ with rfl | rfl
    · have hmono : MonotoneOn (fun i => F.value (e i) H) S := by
        intro i hi j hj hij
        have hjb := arcSign_one_lt hj
        simp only [e,Equiv.symm_apply_apply] at hjb
        exact ho.2.1 H i j hij hjb.le
      exact ColumnOrder.overlapping_ranges hnc hmono hgap he P Q hP hQ hx0 hx1 hy0 hy1 hδ
    · have hanti : AntitoneOn (fun i => F.value (e i) H) S := by
        intro i hi j hj hij
        have hib := arcSign_neg_one_gt hi
        simp only [e,Equiv.symm_apply_apply] at hib
        exact ho.2.2 H i j hib.le hij
      exact ColumnOrder.overlapping_ranges_anti hnc hanti hgap he P Q hP hQ hx0 hx1 hy0 hy1 hδ
  obtain ⟨z,hz,hz'⟩ := hit
  exact ⟨e z,mem p hz,mem r hz'⟩

/-- An empty wall rectangle rules out every boundary column and every
side-changing active switch in a slightly narrower reference-profile strip. -/
lemma strip_arc_const (F : M.Field I L) (a b : Fin (k+1)) (T : I)
    (hJI : J ⊆ I) {s h U V W D : ℝ}
    (hempty : ∀ (c : ℝ) (H : I), |c-s| ≤ U → |H.val-h| ≤ V → (c,H.val) ∉ F.wall a b)
    (hT : |T.val-h| ≤ V) (hD : ∀ t ∈ J, |t-T.val| ≤ D)
    (hV : ∀ t ∈ J, |t-h| ≤ V) (hW : W+L*D ≤ U) (hD0 : 0 ≤ D) :
    (∀ i, |F.value i T-s| ≤ W → arcSign a b i ≠ 0) ∧
    (∀ {i j}, (M.activeGraph J).Adj i j → |F.value i T-s| ≤ W →
      |F.value j T-s| ≤ W → arcSign a b i = arcSign a b j) := by
  constructor
  · intro i hi hz
    exact hempty _ T (by nlinarith [L.coe_nonneg]) hT (F.wall_of_boundary a b i T hz)
  · intro i j hij hi _
    by_contra hne
    obtain ⟨t,ht,hs⟩ := hij
    let H : I := ⟨t,hJI ht⟩
    have hlip := (F.vertical i).dist_le_mul H T
    simp only [Real.dist_eq,Subtype.dist_eq] at hlip
    have he : |F.value i H-F.value i T| ≤ L*D := hlip.trans
      (mul_le_mul_of_nonneg_left (hD t ht) L.coe_nonneg)
    have hc : |F.value i H-s| ≤ U :=
      (abs_sub_le _ _ _).trans (by linarith)
    exact hempty _ H hc (hV t ht) (F.wall_of_switch a b i j H hs hne)

end PlanarL1.Columns.Model.Field

namespace PlanarL1.ColumnOrder

/-- A center-to-exit traversal of a scalar strip, with the visited center
retained and the support enlarged by only one edge error. -/
lemma center_exit_band {V : Type*} {G : SimpleGraph V} (q : V → ℝ)
    {s r c δ : ℝ} (hcr : c < r) (hδ : 0 ≤ δ)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x y : V} (p : G.Walk x y) (hx : |q x-s| ≤ c) (hy : s+r ≤ q y) :
    ∃ a b, ∃ t : G.Walk a b,
      (∀ z ∈ t.support, z ∈ p.support) ∧ x ∈ t.support ∧
      (∀ z ∈ t.support, |q z-s| ≤ r+δ) ∧
      ((q a ≤ s+c ∧ s+r ≤ q b) ∨ (q a ≤ s-r ∧ s-c ≤ q b)) := by
  obtain ⟨a,b,hab,ha,hb,t,ht,hT⟩ := first_exit p
    (S := {z | |q z-s| < r}) (lt_of_le_of_lt hx hcr)
    (by intro h; change |q y-s| < r at h; have := (abs_lt.mp h).2; linarith)
  change |q a-s| < r at ha
  change ¬|q b-s| < r at hb
  have hbabs : |q b-s| ≤ r+δ := by
    have hed := hedge hab
    rw [abs_sub_comm] at hed
    exact (abs_sub_le _ _ _).trans (by linarith)
  have hband : ∀ z ∈ t.support, |q z-s| ≤ r+δ := by
    intro z hz
    rcases hT z hz with hz | rfl
    · change |q z-s| < r at hz
      linarith
    · exact hbabs
  have hout : q b ≤ s-r ∨ s+r ≤ q b := by
    by_contra hn
    push Not at hn
    exact hb (abs_lt.mpr ⟨by linarith,by linarith⟩)
  rcases hout with hlo | hhi
  · refine ⟨b,x,t.reverse,?_,?_,?_,Or.inr ⟨hlo,?_⟩⟩
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ht
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using t.start_mem_support
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hband
    · have := (abs_le.mp hx).1; linarith
  · refine ⟨x,b,t,ht,t.start_mem_support,hband,Or.inl ⟨?_,hhi⟩⟩
    have := (abs_le.mp hx).2; linarith

end PlanarL1.ColumnOrder

namespace PlanarL1.ColumnOrder

/-- Two disjoint low-to-high traversals, each issuing from a central column,
must have opposite central labels when the strip has precisely two lanes and
same-lane overlapping ranges intersect. This is the finite-word form of the
last two paragraphs of 's two-side argument. -/
lemma two_lane_centers {V : Type*} {G : SimpleGraph V} (q label : V → ℝ)
    {s r c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hgap : 2*δ < r-c)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    (hlabels : ∀ z, |q z-s| ≤ r+δ → label z = 1 ∨ label z = -1)
    (hconstant : ∀ {a b}, G.Adj a b → |q a-s| ≤ r+δ → |q b-s| ≤ r+δ → label a = label b)
    (hover : ∀ {a b d e : V} (p : G.Walk a b) (t : G.Walk d e) {u v σ : ℝ},
      σ = 1 ∨ σ = -1 → 2*δ < v-u →
      (∀ z ∈ p.support, label z = σ) → (∀ z ∈ t.support, label z = σ) →
      q a ≤ u → v ≤ q b → q d ≤ u → v ≤ q e →
      ∃ z, z ∈ p.support ∧ z ∈ t.support)
    {x₀ x₁ y₀ y₁ x y : V} (P : G.Walk x₀ x₁) (Q : G.Walk y₀ y₁)
    (U : G.Walk x x₁) (Vw : G.Walk y y₁)
    (hU : ∀ z ∈ U.support, z ∈ P.support) (hV : ∀ z ∈ Vw.support, z ∈ Q.support)
    (hx₀ : q x₀ ≤ s-r) (hx₁ : s+r ≤ q x₁)
    (hy₀ : q y₀ ≤ s-r) (hy₁ : s+r ≤ q y₁)
    (hx : |q x-s| ≤ c) (hy : |q y-s| ≤ c)
    (hdisj : ∀ z ∈ P.support, z ∉ Q.support) : label x ≠ label y := by
  have hr : 0 < r := by linarith
  have hcr : c < r := by linarith
  have fullgap : 2*δ < (s+r)-(s-r) := by linarith
  have band {z : V} (hz : s-r-δ ≤ q z ∧ q z ≤ s+r+δ) : |q z-s| ≤ r+δ :=
    abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
  obtain ⟨a,b,p,ha,hb,hp,hpb⟩ := traverse_band q hδ (by linarith : s-r < s+r) hedge P hx₀ hx₁
  obtain ⟨d,e,t,hd,he,ht,htb⟩ := traverse_band q hδ (by linarith : s-r < s+r) hedge Q hy₀ hy₁
  have hpa : ∀ z ∈ p.support, label z = label a :=
    walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant p (fun z hz => band (hpb z hz))
  have htd : ∀ z ∈ t.support, label z = label d :=
    walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant t (fun z hz => band (htb z hz))
  have hα := hlabels a (band (hpb a p.start_mem_support))
  have hβ := hlabels d (band (htb d t.start_mem_support))
  have hαβ : label a ≠ label d := by
    intro heq
    obtain ⟨z,hz,hz'⟩ := hover p t hα fullgap hpa
      (fun z hz => (htd z hz).trans heq.symm) ha hb hd he
    exact hdisj z (hp z hz) (ht z hz')
  obtain ⟨a',b',p',hp',hxp',hp'b,hprange⟩ := center_exit_band q hcr hδ hedge U hx hx₁
  obtain ⟨d',e',t',ht',hyt',ht'b,htrange⟩ := center_exit_band q hcr hδ hedge Vw hy hy₁
  have hpx : ∀ z ∈ p'.support, label z = label x := by
    have hl := walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant p' hp'b
    intro z hz
    exact (hl z hz).trans (hl x hxp').symm
  have hty : ∀ z ∈ t'.support, label z = label y := by
    have hl := walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant t' ht'b
    intro z hz
    exact (hl z hz).trans (hl y hyt').symm
  have hγ := hlabels x (by linarith : |q x-s| ≤ r+δ)
  intro hxy
  by_cases hαx : label a = label x
  · have htt : ∀ z ∈ t'.support, label z = label a :=
      fun z hz => (hty z hz).trans (hxy.symm.trans hαx.symm)
    have hit : ∃ z, z ∈ p.support ∧ z ∈ t'.support := by
      rcases htrange with hl | hl
      · exact hover p t' hα (by linarith : 2*δ < (s+r)-(s+c)) hpa htt
          (by linarith) hb hl.1 hl.2
      · exact hover p t' hα (by linarith : 2*δ < (s-c)-(s-r)) hpa htt
          ha (by linarith) hl.1 hl.2
    obtain ⟨z,hz,hz'⟩ := hit
    exact hdisj z (hp z hz) (hV z (ht' z hz'))
  · have hβx : label d = label x := by
      rcases hα with hα | hα
      · rcases hβ with hβ | hβ
        · exact False.elim (hαβ (hα.trans hβ.symm))
        · rcases hγ with hγ | hγ
          · exact False.elim (hαx (hα.trans hγ.symm))
          · exact hβ.trans hγ.symm
      · rcases hβ with hβ | hβ
        · rcases hγ with hγ | hγ
          · exact hβ.trans hγ.symm
          · exact False.elim (hαx (hα.trans hγ.symm))
        · exact False.elim (hαβ (hα.trans hβ.symm))
    have hpp : ∀ z ∈ p'.support, label z = label d := fun z hz => (hpx z hz).trans hβx.symm
    have hit : ∃ z, z ∈ p'.support ∧ z ∈ t.support := by
      rcases hprange with hl | hl
      · exact hover p' t hβ (by linarith : 2*δ < (s+r)-(s+c)) hpp htd
          hl.1 hl.2 (by linarith) he
      · exact hover p' t hβ (by linarith : 2*δ < (s-c)-(s-r)) hpp htd
          hl.1 hl.2 hd (by linarith)
    obtain ⟨z,hz,hz'⟩ := hit
    exact hdisj z (hU z (hp' z hz)) (ht z hz')

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {L : NNReal}

def restrict (F : M.Field I L) (hJI : J ⊆ I) : M.Field J L where
  value i H := F.value i ⟨H.val,hJI H.property⟩
  vertical i := by
    apply LipschitzWith.of_dist_le_mul
    intro H T
    exact (F.vertical i).dist_le_mul ⟨H.val,hJI H.property⟩ ⟨T.val,hJI T.property⟩
  switch i j H hs := F.switch i j ⟨H.val,hJI H.property⟩ hs

/-- Quantitative opposite-arc conclusion from genuine short excursions. The
only extra displayed inequality says exactly that the constructed short join
would contradict the given separation; at R=10^-8 it follows from d≥1. -/
lemma two_side_arcs (F : M.Field I 4) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    {root : Fin (k+1)} {R η : ℝ} (hR : 0 < R) (hη : η ≤ R/1000000)
    (hJI : J ⊆ I) (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ η)
    (x y : M.Point I root)
    (Ex : F.Excursions hJI x (2*R) (2*R/5))
    (Ey : F.Excursions hJI y (2*R) (2*R/5))
    (hclose : |F.eval x-F.eval y| ≤ R/1000)
    (hfar : 4*R+2*(R/50+η) < dist x y) :
    arcSign a b x.column ≠ 0 ∧ arcSign a b y.column ≠ 0 ∧
    arcSign a b x.column ≠ arcSign a b y.column ∧
    R/100 ≤ Metric.infDist (F.eval x,x.height) (F.wall a b) ∧
    R/100 ≤ Metric.infDist (F.eval y,y.height) (F.wall a b) := by
  let T : I := ⟨x.height,x.inBand⟩
  let s := F.eval x
  let q : Fin (k+1) → ℝ := fun i => F.value i T
  have hη0 : 0 ≤ η := by simpa using hw x.height Ex.inBand x.height Ex.inBand
  have hD : ∀ t ∈ J, |t-T.val| ≤ η := fun t ht => hw t ht x.height Ex.inBand
  have hempty : ∀ (c : ℝ) (H : I), |c-s| ≤ R/5 → |H.val-x.height| ≤ R/50 →
      (c,H.val) ∉ F.wall a b := fun c H hc hH =>
    F.empty_rectangle ho hR hη hJI hw x y Ex Ey hclose hfar H hc hH
  have hstrip := F.strip_arc_const a b T hJI (s := s) (h := x.height)
    (U := R/5) (V := R/50) (W := R/6+8*η) (D := η) hempty
    (by dsimp [T]; rw [sub_self,abs_zero]; linarith) hD
    (fun t ht => (hD t ht).trans (by linarith))
    (by norm_num; linarith) hη0
  have he {i j} (hij : (M.activeGraph J).Adj i j) : |q i-q j| ≤ 8*η := by
    have hh := (F.restrict hJI).profile_switch_error hw (⟨x.height,Ex.inBand⟩ : J) hij
    change |q i-q j| ≤ 2*(4*η) at hh
    linarith
  have hlabels (z) (hz : |q z-s| ≤ R/6+8*η) : arcSign a b z = 1 ∨ arcSign a b z = -1 := by
    rcases arcSign_cases a b z with hz0 | hz1 | hz1
    · exact False.elim (hstrip.1 z hz hz0)
    · exact Or.inl hz1
    · exact Or.inr hz1
  have hqx : |q x.column-s| ≤ R/100 := by simp only [q,T,s,eval,sub_self,abs_zero]; linarith
  have hqy : |q y.column-s| ≤ R/100 := by
    have hp := (F.restrict hJI).profile_error hw y.column
      (⟨x.height,Ex.inBand⟩ : J) ⟨y.height,Ey.inBand⟩
    change |q y.column-F.eval y| ≤ 4*η at hp
    have hh := abs_sub_le (q y.column) (F.eval y) s
    have hcl : |F.eval y-s| ≤ R/1000 := by simpa only [s,abs_sub_comm] using hclose
    linarith
  have hxl := Ex.low_profile T hD
  have hxh := Ex.high_profile T hD
  have hyl := Ey.low_profile T hD
  have hyh := Ey.high_profile T hD
  norm_num only [NNReal.coe_ofNat] at hxl hxh hyl hyh
  have hcl := abs_le.mp hclose
  have disj : ∀ z ∈ Ex.traversal.support, z ∉ Ey.traversal.support := by
    intro z hz hz'
    have hd := x.dist_le_of_near_intersection y Ex.near_traversal Ey.near_traversal hw hz hz'
    linarith
  have hU : ∀ z ∈ Ex.highPath.word.support, z ∈ Ex.traversal.support := by
    intro z hz
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inr hz)
  have hV : ∀ z ∈ Ey.highPath.word.support, z ∈ Ey.traversal.support := by
    intro z hz
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inr hz)
  have hneq := ColumnOrder.two_lane_centers q (arcSign a b) (s := s)
    (r := R/6) (c := R/100) (δ := 8*η) (by linarith) (by linarith) (by linarith)
    he hlabels hstrip.2
    (fun {i j l m} p t {u v σ} hσ hg hp ht hl hh hl' hh' => F.same_arc_overlap ho T hσ
      (by linarith) hg he p t hp ht hl hh hl' hh')
    Ex.traversal Ey.traversal Ex.highPath.word Ey.highPath.word hU hV
    (by change F.value Ex.lowColumn T ≤ F.eval x-R/6; linarith)
    (by change F.eval x+R/6 ≤ F.value Ex.highColumn T; linarith)
    (by change F.value Ey.lowColumn T ≤ F.eval x-R/6; linarith)
    (by change F.eval x+R/6 ≤ F.value Ey.highColumn T; linarith)
    hqx hqy disj
  refine ⟨hstrip.1 x.column (by linarith),hstrip.1 y.column (by linarith),hneq,?_,?_⟩
  · exact F.infDist_lower_of_rectangle a b T hempty x.column
      (by change |F.eval x-F.eval x|+R/100 ≤ R/5; rw [sub_self,abs_zero]; linarith)
      (by change |x.height-x.height|+R/100 ≤ R/50; rw [sub_self,abs_zero]; linarith)
  · exact F.infDist_lower_of_rectangle a b ⟨y.height,y.inBand⟩ hempty y.column
      (by change |F.eval y-F.eval x|+R/100 ≤ R/5; rw [abs_sub_comm]; linarith)
      (by have hh := hw y.height Ey.inBand x.height Ex.inBand; dsimp; linarith)

lemma abs_add_eq_abs_sub_of_opposite {u v : ℝ} (huv : u*v < 0) : |u|+|v| = |u-v| := by
  by_cases hu : 0 ≤ u
  · have hv : v < 0 := by nlinarith
    rw [abs_of_nonneg hu,abs_of_neg hv,abs_of_nonneg (by linarith : 0 ≤ u-v)]
    ring
  · have hu' : u < 0 := lt_of_not_ge hu
    have hv : 0 < v := by nlinarith
    rw [abs_of_neg hu',abs_of_pos hv,abs_of_neg (by linarith : u-v < 0)]
    ring

/-- Full quantitative two-side lemma (, ord:two-side) in intrinsic
band coordinates. An ambient application uses the source hypothesis d_I=d. -/
theorem two_side (F : M.Field I 4) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (hI : IsClosed I) {root : Fin (k+1)} {η : ℝ}
    (hη : η ≤ (1:ℝ)/100000000/1000000)
    (hJI : J ⊆ I) (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ η)
    (x y : M.Point I root) (hlo : 1 ≤ dist x y) (hhi : dist x y ≤ 2)
    (Ex : F.Excursions hJI x (2*((1:ℝ)/100000000)) (2*((1:ℝ)/100000000)/5))
    (Ey : F.Excursions hJI y (2*((1:ℝ)/100000000)) (2*((1:ℝ)/100000000)/5))
    (hclose : |F.eval x-F.eval y| ≤ (1:ℝ)/100000000/1000) :
    (F.transverse (by norm_num) a b).eval x * (F.transverse (by norm_num) a b).eval y < 0 ∧
    (1:ℝ)/100000000/100 ≤ |(F.transverse (by norm_num) a b).eval x| ∧
    (1:ℝ)/100000000/100 ≤ |(F.transverse (by norm_num) a b).eval y| ∧
    |(F.transverse (by norm_num) a b).eval x| ≤ 8 ∧
    |(F.transverse (by norm_num) a b).eval y| ≤ 8 := by
  obtain ⟨hx,hy,hneq,hDx,hDy⟩ := F.two_side_arcs ho (by norm_num) hη hJI hw x y Ex Ey hclose (by linarith)
  let tx := (F.transverse (by norm_num) a b).eval x
  let ty := (F.transverse (by norm_num) a b).eval y
  have hax : |tx| = Metric.infDist (F.eval x,x.height) (F.wall a b) :=
    F.transverse_abs a b x.column ⟨x.height,x.inBand⟩ hx
  have hay : |ty| = Metric.infDist (F.eval y,y.height) (F.wall a b) :=
    F.transverse_abs a b y.column ⟨y.height,y.inBand⟩ hy
  have hDx0 : 0 < Metric.infDist (F.eval x,x.height) (F.wall a b) := lt_of_lt_of_le (by norm_num) hDx
  have hDy0 : 0 < Metric.infDist (F.eval y,y.height) (F.wall a b) := lt_of_lt_of_le (by norm_num) hDy
  have hprod : tx*ty < 0 := by
    change (arcSign a b x.column * _) * (arcSign a b y.column * _) < 0
    rcases arcSign_cases a b x.column with hx0 | hx1 | hx1
    · exact False.elim (hx hx0)
    · rcases arcSign_cases a b y.column with hy0 | hy1 | hy1
      · exact False.elim (hy hy0)
      · exact False.elim (hneq (hx1.trans hy1.symm))
      · rw [hx1,hy1,one_mul,neg_one_mul,mul_neg]
        exact neg_neg_of_pos (mul_pos hDx0 hDy0)
    · rcases arcSign_cases a b y.column with hy0 | hy1 | hy1
      · exact False.elim (hy hy0)
      · rw [hx1,hy1,one_mul,neg_one_mul,neg_mul]
        exact neg_neg_of_pos (mul_pos hDx0 hDy0)
      · exact False.elim (hneq (hx1.trans hy1.symm))
  have hd := ((F.transverse (by norm_num) a b).lipschitz hI root).dist_le_mul x y
  change dist tx ty ≤ (4:NNReal)*dist x y at hd
  rw [Real.dist_eq] at hd
  norm_num only [NNReal.coe_ofNat] at hd
  have hsum := abs_add_eq_abs_sub_of_opposite hprod
  refine ⟨hprod,by rwa [hax],by rwa [hay],?_,?_⟩ <;> linarith [abs_nonneg tx,abs_nonneg ty]

end PlanarL1.Columns.Model.Field


end

end OAI
