import OAI.Computability.WLIdentification.LinearExtensions

namespace OAI

namespace WLIdentification

/-- Characteristic-two rearrangement, stated without an arithmetic oracle. -/
theorem bit_eq_add_of_add_eq {x y z : Bit} (h : x + y = z) : x = z + y := by
  calc
    x = x + (y + y) := by rw [CharTwo.add_self_eq_zero, add_zero]
    _ = z + y := by rw [← add_assoc, h]

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

/-- Image consistency for every link. Only scalar image sets are equated;
no common vector choice is silently imposed on distinct comparisons. -/
theorem imageSet_link (hr : 2 ≤ r) (beta : R.Block → Bit) (e : L) (a : R.MatchAddress e) :
    (R.firstForm e) '' R.ImageSet hr beta (R.first e) (R.leftAddress e a) =
      (fun y => R.linkShift beta e a + R.secondForm e y) ''
        R.ImageSet hr beta (R.second e) (R.rightAddress e a) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := R.imageSet_left_support hr e a hx
    exact ⟨y, hy, (bit_eq_add_of_add_eq he).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, he⟩ := R.imageSet_right_support hr e a hy
    exact ⟨x, hx, bit_eq_add_of_add_eq he⟩

end RingLayout

namespace WireAlgebra

def shiftSet (c : Bit) (X : Set Bit) : Set Bit := (fun x => c + x) '' X

@[simp]
theorem shiftSet_zero (X : Set Bit) : shiftSet 0 X = X := by
  simp [shiftSet]

@[simp]
theorem shiftSet_shiftSet (c d : Bit) (X : Set Bit) :
    shiftSet c (shiftSet d X) = shiftSet (c + d) X := by
  simp only [shiftSet, Set.image_image, add_assoc]

/-- Private internal scalar image sets telescope by translations. This does not
cancel Minkowski sums or select a common endpoint vector across comparisons. -/
theorem chain_sets {n : ℕ} (left right : Set Bit) (q : Fin (n + 1) → Set Bit)
    (first last : Bit) (middle : Fin n → Bit)
    (hfirst : left = shiftSet first (q 0))
    (hmiddle : ∀ i, q i.castSucc = shiftSet (middle i) (q i.succ))
    (hlast : q (Fin.last n) = shiftSet last right) :
    left = shiftSet (first + (∑ i, middle i) + last) right := by
  have hj (j : Fin (n + 1)) : left = shiftSet (first + prefixSum middle j) (q j) := by
    induction j using Fin.induction with
    | zero => simpa only [prefix_zero, add_zero] using hfirst
    | succ i ih =>
      rw [hmiddle i, shiftSet_shiftSet] at ih
      simpa only [prefix_succ, add_assoc] using ih
  have hh := hj (Fin.last n)
  rw [hlast, shiftSet_shiftSet, prefix_last] at hh
  exact hh

end WireAlgebra

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} [Fintype P] [Fintype E] (S : ComparisonSchemas r P E)

noncomputable def responseImages (hr : 2 ≤ r) (n : ℕ) (beta : (S.layout n).Block → Bit)
    (p : P) (a : S.Address) : Set (Fin (S.dimension p) → Bit) :=
  (S.layout n).ImageSet hr beta (.inl p) a

theorem image_consistency (hr : 32 ≤ r) (n : ℕ) (beta : (S.layout n).Block → Bit)
    (h : Equivalent r (((S.layout n).affine (by omega)).graph 0)
      (((S.layout n).affine (by omega)).graph beta)) :
    (∀ p a, (S.responseImages (by omega) n beta p a).Nonempty) ∧
    ∀ e (a : S.DomainAddress e),
      (S.left e) '' S.responseImages (by omega) n beta (S.source e) (S.sourceAddress e a) =
        (fun y => S.wireShift n beta e a + S.right e y) ''
          S.responseImages (by omega) n beta (S.target e) (S.targetAddress e a) := by
  have hr2 : 2 ≤ r := by omega
  constructor
  · intro p a
    exact (S.layout n).imageSet_nonempty hr2 h (.inl p) a
  · intro e a
    let q (j : Fin (n + 1)) : Set Bit :=
      (fun v : Fin 1 → Bit => v 0) '' (S.layout n).ImageSet hr2 beta (.inr (e, j)) a
    have hf : (S.left e) '' S.responseImages hr2 n beta (S.source e) (S.sourceAddress e a) =
        WireAlgebra.shiftSet (S.firstShift n beta e a) (q 0) := by
      have hh := (S.layout n).imageSet_link hr2 beta (.inl e) a
      change (S.left e) '' S.responseImages hr2 n beta (S.source e) (S.sourceAddress e a) =
        (fun v : Fin 1 → Bit => S.firstShift n beta e a + v 0) ''
          (S.layout n).ImageSet hr2 beta (.inr (e, 0)) a at hh
      exact hh.trans (Set.image_image _ _ _).symm
    have hm (j : Fin n) : q j.castSucc = WireAlgebra.shiftSet (S.middleShift n beta e j a) (q j.succ) := by
      have hh := (S.layout n).imageSet_link hr2 beta (.inr (.inl (e, j))) a
      change q j.castSucc =
        (fun v : Fin 1 → Bit => S.middleShift n beta e j a + v 0) ''
          (S.layout n).ImageSet hr2 beta (.inr (e, j.succ)) a at hh
      exact hh.trans (Set.image_image _ _ _).symm
    have hl : q (Fin.last n) = WireAlgebra.shiftSet (S.lastShift n beta e a)
        ((S.right e) '' S.responseImages hr2 n beta (S.target e) (S.targetAddress e a)) := by
      have hh := (S.layout n).imageSet_link hr2 beta (.inr (.inr e)) a
      change q (Fin.last n) =
        (fun v => S.lastShift n beta e a + S.right e v) ''
          S.responseImages hr2 n beta (S.target e) (S.targetAddress e a) at hh
      simpa only [WireAlgebra.shiftSet, Set.image_image] using hh
    simpa only [WireAlgebra.shiftSet, Set.image_image, Function.comp_def, wireShift] using
      WireAlgebra.chain_sets _ _ q _ _ _ hf hm hl

end ComparisonSchemas

namespace Marker
variable {V : Type} {G : SimpleGraph V}

def walkSum (m : V → V → Bit) {u v : V} : G.Walk u v → Bit
  | .nil => 0
  | .cons (u := u) (v := v) _ p => m u v + walkSum m p

@[simp] theorem walkSum_nil (m : V → V → Bit) (u : V) :
    walkSum m (.nil : G.Walk u u) = 0 := rfl

@[simp] theorem walkSum_cons (m : V → V → Bit) {u v w : V} (h : G.Adj u v)
    (p : G.Walk v w) : walkSum m (.cons h p) = m u v + walkSum m p := rfl

@[simp] theorem walkSum_append (m : V → V → Bit) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkSum m (p.append q) = walkSum m p + walkSum m q := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [SimpleGraph.Walk.cons_append, walkSum_cons, ih, add_assoc]

@[simp] theorem walkSum_reverse (m : V → V → Bit)
    (hm : ∀ u v, G.Adj u v → m u v = m v u) {u v : V} (p : G.Walk u v) :
    walkSum m p.reverse = walkSum m p := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkSum_append, walkSum_cons, walkSum_nil, ih,
      ← hm u v h, add_zero, add_comm, walkSum_cons]

theorem walkSum_cast_left (m : V → V → Bit) {u u' v : V}
    (h : u = u') (p : G.Walk u v) : walkSum m (h ▸ p) = walkSum m p := by
  subst u'
  rfl

/-- A nonwrapping marker is an exact coboundary. No finiteness or connectedness
assumption is needed; roots are chosen separately in actual graph components. -/
theorem exact_of_closed_zero (m : V → V → Bit)
    (hm : ∀ u v, G.Adj u v → m u v = m v u)
    (hc : ∀ u (p : G.Walk u u), walkSum m p = 0) :
    ∃ s : V → Bit, ∀ u v, G.Adj u v → m u v = s u + s v := by
  classical
  let root (v : V) : V := (G.connectedComponentMk v).out
  have hr (v : V) : G.Reachable (root v) v := @Quotient.mk_out V G.reachableSetoid v
  let path (v : V) : G.Walk (root v) v := (hr v).some
  refine ⟨fun v => walkSum m (path v), ?_⟩
  intro u v huv
  have he : root u = root v := congrArg (fun c : G.ConnectedComponent => c.out) (SimpleGraph.ConnectedComponent.sound huv.reachable)
  let q : G.Walk (root u) v := he.symm ▸ path v
  have hq : walkSum m q = walkSum m (path v) := by exact walkSum_cast_left m he.symm (path v)
  have hz := hc (root u) ((path u).append (huv.toWalk.append q.reverse))
  simp only [walkSum_append, walkSum_cons, walkSum_nil, add_zero,
    walkSum_reverse m hm, hq] at hz
  calc
    m u v = m u v + (walkSum m (path u) + (m u v + walkSum m (path v))) := by rw [hz, add_zero]
    _ = (m u v + m u v) + (walkSum m (path u) + walkSum m (path v)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- Conversely, a potential cancels around every closed walk. -/
theorem walkSum_of_exact (s : V → Bit) (m : V → V → Bit)
    (hm : ∀ u v, G.Adj u v → m u v = s u + s v)
    {u v : V} (p : G.Walk u v) : walkSum m p = s u + s v := by
  induction p with
  | nil => rw [walkSum_nil, CharTwo.add_self_eq_zero]
  | @cons u v w h p ih =>
    rw [walkSum_cons, hm u v h, ih]
    calc
      _ = (s v + s v) + (s u + s w) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

@[simp] theorem walkSum_add (m n : V → V → Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun u v => m u v + n u v) p = walkSum m p + walkSum n p := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [walkSum_cons, ih]; abel

@[simp] theorem walkSum_smul (a : Bit) (m : V → V → Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun u v => a * m u v) p = a * walkSum m p := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [walkSum_cons, ih, mul_add]

def cut {r : ℕ} (j i : Fin r) : Bit := if j.val < i.val then 1 else 0

def delta {r : ℕ} (i : Fin r) : Bit := if i.val + 1 = r then 1 else 0

/-- Moving the marked row to any other cut changes the marker by a boundary
potential, including for singleton coordinate domains. -/
theorem cut_toggle {r : ℕ} (j i : Fin r) :
    cut j i + cut j (finRotate r i) = delta i + (if i = j then 1 else 0) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
    dsimp only [cut, delta]
    rw [coe_finRotate]
    by_cases hl : i = Fin.last n
    · subst i
      by_cases hj : j = Fin.last n
      · subst j; simp [CharTwo.add_self_eq_zero]
      · have hj' : j.val < n := Fin.val_lt_last hj
        simp [hj', Ne.symm hj]
    · have hi : i.val + 1 ≠ n + 1 := by
        intro hh
        apply hl
        apply Fin.ext
        exact Nat.add_right_cancel hh
      rw [ite_eq_right hl, ite_eq_right hi]
      by_cases he : i = j
      · subst j; simp
      · have he' : i.val ≠ j.val := fun hh => he (Fin.ext hh)
        by_cases hlt : j.val < i.val
        · simp [he, hlt, show j.val < i.val + 1 by omega, CharTwo.add_self_eq_zero]
        · have hgt : ¬j.val < i.val + 1 := by omega
          simp [he, hlt, hgt]

/-- If one row is absent, the ring marker is a boundary potential. This is
valid on an arbitrary corner subgraph and uses no assumption on label factors. -/
theorem closed_zero_of_missing_row {r : ℕ} (row : V → Fin r) (j : Fin r)
    (m : V → V → Bit)
    (he : ∀ u v, G.Adj u v →
      (row u = row v ∧ m u v = 0) ∨
      ∃ i : Fin r, i ≠ j ∧ m u v = delta i ∧
        ((row u = i ∧ row v = finRotate r i) ∨
         (row v = i ∧ row u = finRotate r i))) :
    ∀ u (p : G.Walk u u), walkSum m p = 0 := by
  have hm : ∀ u v, G.Adj u v → m u v = cut j (row u) + cut j (row v) := by
    intro u v huv
    rcases he u v huv with ⟨hr, hm⟩ | ⟨i, hij, hm, hh⟩
    · rw [hm, hr, CharTwo.add_self_eq_zero]
    · have hi := cut_toggle j i
      rw [ite_eq_right hij, add_zero] at hi
      rcases hh with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [hu, hv, hm, hi]
      · rw [hu, hv, hm, add_comm, hi]
  intro u p
  rw [walkSum_of_exact (fun v => cut j (row v)) m hm p, CharTwo.add_self_eq_zero]

/-- The potential adjustment in the exact-projection argument, at a horizontal
readout. Vector coordinates are adjusted together, not independently chosen. -/
theorem horizontal_adjust {W : Type} [AddCommGroup W] [Module Bit W]
    (M N old new : W) (s t d : Bit) (hd : s + t = d) :
    (M + s • (new + old)) + (N + t • (new + old)) + d • new = M + N + d • old := by
  calc
    _ = M + N + ((s + t) • (new + old) + d • new) := by rw [add_smul]; abel
    _ = M + N + (d • (new + new) + d • old) := by rw [hd, smul_add, smul_add]; abel
    _ = _ := by
      have hz : new + new = 0 := by
        have hh : ((1 : Bit) + 1) • new = (0 : Bit) • new := by congr 1
        simpa only [add_smul, one_smul, zero_smul] using hh
      rw [hz, smul_zero, zero_add]

/-- Vertical readouts survive the same adjustment because the difference of
the two affine component shifts solves the homogeneous link equation. -/
theorem vertical_adjust {W X : Type} [AddCommGroup W] [AddCommGroup X]
    [Module Bit W] [Module Bit X] (L : W →ₗ[Bit] Bit) (R : X →ₗ[Bit] Bit)
    (M : W) (N : X) (g : W) (h : X) (s t : Bit)
    (hst : s = t) (he : L g + R h = 0) :
    L (M + s • g) + R (N + t • h) = L M + R N := by
  subst t
  rw [map_add, map_add, map_smul, map_smul]
  calc
    _ = L M + R N + s * (L g + R h) := by simp only [smul_eq_mul]; ring
    _ = _ := by rw [he, mul_zero, add_zero]

end Marker

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

abbrev Corner := Σ t : T, Σ i : Fin r, R.Label t i
abbrev Name := R.HName ⊕ R.VName

noncomputable instance nameDecidableEq : DecidableEq R.Name := Classical.decEq _

def nameFirst : R.Name → R.Corner
  | .inl h => ⟨h.1, h.2.1, h.2.2.1⟩
  | .inr v => ⟨R.first v.1, v.2.1, R.firstLabel v.1 v.2.1 v.2.2⟩

def nameSecond : R.Name → R.Corner
  | .inl h => ⟨h.1, finRotate r h.2.1, h.2.2.2⟩
  | .inr v => ⟨R.second v.1, v.2.1, R.secondLabel v.1 v.2.1 v.2.2⟩

theorem name_endpoints_ne (hr : 2 ≤ r) (n : R.Name) : R.nameFirst n ≠ R.nameSecond n := by
  intro h
  cases n with
  | inl n =>
    exact CycleRows.rotate_ne_self hr n.2.1
      (congrArg (fun c : R.Corner => c.2.1) h).symm
  | inr n => exact R.endpoints_ne n.1 (congrArg Sigma.fst h)

noncomputable def blockNames : R.Block → Finset R.Name
  | .inl h => {Sum.inl h}
  | .inr b => {Sum.inl (R.leftH b), Sum.inl (R.rightH b), Sum.inr (R.topV b), Sum.inr (R.bottomV b)}

noncomputable def names (U : Finset R.Block) : Finset R.Name := by
  classical
  exact U.biUnion R.blockNames

def blockRow : R.Block → Fin r
  | .inl h => h.2.1
  | .inr b => b.2.1

/-- Shared names give a single edge. Vector bit coordinates are not counted as
separate horizontal edges in the corner graph. -/
noncomputable def cornerGraph (hr : 2 ≤ r) (U : Finset R.Block) : SimpleGraph R.Corner where
  Adj u v := ∃ n ∈ R.names U,
    (R.nameFirst n = u ∧ R.nameSecond n = v) ∨ (R.nameFirst n = v ∧ R.nameSecond n = u)
  symm := ⟨by
    intro u v
    rintro ⟨n, hn, h⟩
    exact ⟨n, hn, h.symm⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨n, _, h⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact R.name_endpoints_ne hr n (h1.trans h2.symm)⟩

def cornerMarker (u v : R.Corner) : Bit :=
  if u.2.1 = v.2.1 then 0 else
    if v.2.1 = finRotate r u.2.1 then Marker.delta u.2.1 else Marker.delta v.2.1

theorem cornerMarker_horizontal (hr : 3 ≤ r) (h : R.HName) :
    R.cornerMarker (R.nameFirst (.inl h)) (R.nameSecond (.inl h)) = Marker.delta h.2.1 ∧
    R.cornerMarker (R.nameSecond (.inl h)) (R.nameFirst (.inl h)) = Marker.delta h.2.1 := by
  have h1 := CycleRows.rotate_ne_self (show 2 ≤ r by omega) h.2.1
  have h2 := CycleRows.rotate_twice_ne_self hr h.2.1
  dsimp only [cornerMarker, nameFirst, nameSecond]
  constructor
  · rw [ite_eq_right (Ne.symm h1), ite_eq_left rfl]
  · rw [ite_eq_right h1, ite_eq_right (Ne.symm h2)]

theorem cornerMarker_vertical (v : R.VName) :
    R.cornerMarker (R.nameFirst (.inr v)) (R.nameSecond (.inr v)) = 0 ∧
    R.cornerMarker (R.nameSecond (.inr v)) (R.nameFirst (.inr v)) = 0 := by
  simp [cornerMarker, nameFirst, nameSecond]

theorem horizontal_row_mem {U : Finset R.Block} {h : R.HName}
    (hh : Sum.inl h ∈ R.names U) : h.2.1 ∈ U.image R.blockRow := by
  classical
  obtain ⟨b, hb, hm⟩ := Finset.mem_biUnion.mp hh
  refine Finset.mem_image.mpr ⟨b, hb, ?_⟩
  cases b with
  | inl b =>
    have he : h = b := Sum.inl.inj (Finset.mem_singleton.mp hm)
    subst h
    rfl
  | inr b =>
    simp only [blockNames, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Sum.inl_ne_inr, or_false] at hm
    rcases hm with rfl | rfl <;> rfl

/-- Every horizontal edge in the support comes from a block in its own row;
vertical edges preserve the boundary index and have marker zero. -/
theorem cornerGraph_row_edge (hr : 3 ≤ r) {U : Finset R.Block} {u v : R.Corner}
    (h : (R.cornerGraph (by omega) U).Adj u v) :
    (u.2.1 = v.2.1 ∧ R.cornerMarker u v = 0) ∨
    ∃ i ∈ U.image R.blockRow, R.cornerMarker u v = Marker.delta i ∧
      ((u.2.1 = i ∧ v.2.1 = finRotate r i) ∨
       (v.2.1 = i ∧ u.2.1 = finRotate r i)) := by
  classical
  obtain ⟨n, hn, h⟩ := h
  cases n with
  | inl n =>
    refine Or.inr ⟨n.2.1, R.horizontal_row_mem hn, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(R.cornerMarker_horizontal hr n).1, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(R.cornerMarker_horizontal hr n).2, Or.inr ⟨rfl, rfl⟩⟩
  | inr n =>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, (R.cornerMarker_vertical n).1⟩
    · exact Or.inl ⟨rfl, (R.cornerMarker_vertical n).2⟩

def Wrapping (hr : 2 ≤ r) (U : Finset R.Block) : Prop :=
  ∃ (u : R.Corner) (p : (R.cornerGraph hr U).Walk u u), Marker.walkSum R.cornerMarker p = 1

/-- A closed walk of odd marker forces every row to be represented. -/
theorem wrapping_rows (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) (j : Fin r) : j ∈ U.image R.blockRow := by
  classical
  by_contra hj
  have hz := Marker.closed_zero_of_missing_row (G := R.cornerGraph (by omega) U)
    (fun c : R.Corner => c.2.1) j R.cornerMarker ?_
  · obtain ⟨u, p, hp⟩ := h
    have := hz u p
    rw [hp] at this
    exact one_ne_zero this
  · intro u v huv
    rcases R.cornerGraph_row_edge hr huv with hh | ⟨i, hi, hm, hh⟩
    · exact Or.inl hh
    · exact Or.inr ⟨i, fun he => hj (he ▸ hi), hm, hh⟩

/-- A wrapping family has at least one block per row. The count is blocks, not
readout names and not vertices; a square still supplies only one row. -/
theorem wrapping_card (hr : 3 ≤ r) {U : Finset R.Block}
    (h : R.Wrapping (by omega) U) : r ≤ U.card := by
  classical
  have hs : (Finset.univ : Finset (Fin r)) ⊆ U.image R.blockRow :=
    fun j _ => R.wrapping_rows hr h j
  have hc := Finset.card_le_card hs
  simpa only [Finset.card_univ, Fintype.card_fin] using hc.trans (Finset.card_image_le)

end RingLayout

end WLIdentification

end OAI
