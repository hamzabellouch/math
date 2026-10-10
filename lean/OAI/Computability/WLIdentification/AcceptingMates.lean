import OAI.Computability.WLIdentification.GlobalSolvability

namespace OAI

namespace WLIdentification

namespace SimpleGraph

theorem reachable_propagate {V : Type} {G : SimpleGraph V} {a b : V} {P : V → Prop}
    (hab : G.Reachable a b) (ha : P a)
    (step : ∀ {u v}, G.Reachable a u → G.Adj u v → P u → P v) : P b := by
  obtain ⟨p⟩ := hab
  have aux : ∀ {u v} (p : G.Walk u v), G.Reachable a u → P u → P v := by
    intro u v p
    induction p with
    | nil => exact fun _ h => h
    | cons h p ih =>
      intro hu hp
      exact ih (hu.trans h.reachable) (step hu h hp)
  exact aux p (.refl a) ha

end SimpleGraph

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem shift_link_forward {n : ℕ} (h h' : (S.layout n).Shift) (l : S.Link n)
    (he : (S.layout n).firstForm l (h ((S.layout n).first l)) +
        (S.layout n).secondForm l (h ((S.layout n).second l)) =
      (S.layout n).firstForm l (h' ((S.layout n).first l)) +
        (S.layout n).secondForm l (h' ((S.layout n).second l)))
    (hreal : ∀ p, (S.layout n).second l = Sum.inl p → h (.inl p) = h' (.inl p))
    (hh : h ((S.layout n).first l) = h' ((S.layout n).first l)) :
    h ((S.layout n).second l) = h' ((S.layout n).second l) := by
  rw [hh] at he
  have hv := add_left_cancel he
  cases l with
  | inl e =>
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst j
    exact hv
  | inr l => cases l with
    | inl ei =>
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst j
      exact hv
    | inr e => exact hreal (S.target e) rfl

theorem shift_link_backward {n : ℕ} (h h' : (S.layout n).Shift) (l : S.Link n)
    (he : (S.layout n).firstForm l (h ((S.layout n).first l)) +
        (S.layout n).secondForm l (h ((S.layout n).second l)) =
      (S.layout n).firstForm l (h' ((S.layout n).first l)) +
        (S.layout n).secondForm l (h' ((S.layout n).second l)))
    (hreal : ∀ p, (S.layout n).first l = Sum.inl p → h (.inl p) = h' (.inl p))
    (hh : h ((S.layout n).second l) = h' ((S.layout n).second l)) :
    h ((S.layout n).first l) = h' ((S.layout n).first l) := by
  rw [hh] at he
  have hv := add_right_cancel he
  cases l with
  | inl e => exact hreal (S.source e) rfl
  | inr l => cases l with
    | inl ei =>
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst j
      exact hv
    | inr e =>
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst j
      exact hv

theorem shift_agreement_reachable {n : ℕ} {U : Finset (S.layout n).Block}
    (hr : 2 ≤ r) (old new : (S.layout n).Shift) {a c : (S.layout n).Corner}
    (he : ∀ l ∈ (S.layout n).usedLinks U,
      (S.layout n).firstForm l (old ((S.layout n).first l)) +
        (S.layout n).secondForm l (old ((S.layout n).second l)) =
      (S.layout n).firstForm l (new ((S.layout n).first l)) +
        (S.layout n).secondForm l (new ((S.layout n).second l)))
    (hreal : ∀ d, ((S.layout n).cornerGraph hr U).Reachable a d →
      ∀ p, d.1 = Sum.inl p → old (.inl p) = new (.inl p))
    (ha : old a.1 = new a.1)
    (hc : ((S.layout n).cornerGraph hr U).Reachable a c) : old c.1 = new c.1 := by
  apply SimpleGraph.reachable_propagate hc ha
  intro u v hu huv hh
  have hv := hu.trans huv.reachable
  obtain ⟨x, hx, hd⟩ := huv
  cases x with
  | inl x => rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hh
  | inr x =>
    have hl := he x.1 ((S.layout n).vertical_usedLink hx)
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.shift_link_forward old new x.1 hl (hreal _ hv) hh
    · exact S.shift_link_backward old new x.1 hl (hreal _ hv) hh

def SameAlignment (n : ℕ) (cut cut' : E → Fin n) (t : S.InternalType n) : Prop :=
  ∀ i (a : (S.layout n).Label t i),
    S.align n cut ⟨t, i, a⟩ = S.align n cut' ⟨t, i, a⟩

theorem alignment_link_forward {n : ℕ} {U : Finset (S.layout n).Block}
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (hh : S.SameAlignment n cut cut' ((S.layout n).first l)) :
    S.SameAlignment n cut cut' ((S.layout n).second l) := by
  have step (i : Fin r) (a : (S.layout n).Match l i) :=
    (S.align_link hc hl i a).symm.trans ((hh i _).trans (S.align_link hc' hl i a))
  cases l with
  | inl e => exact step
  | inr l => cases l with
    | inl ei => exact step
    | inr e => exact fun _ _ => rfl

theorem alignment_link_backward {n : ℕ} {U : Finset (S.layout n).Block}
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (hh : S.SameAlignment n cut cut' ((S.layout n).second l)) :
    S.SameAlignment n cut cut' ((S.layout n).first l) := by
  have step (i : Fin r) (a : (S.layout n).Match l i) :=
    (S.align_link hc hl i a).trans ((hh i _).trans (S.align_link hc' hl i a).symm)
  cases l with
  | inl e => exact fun _ _ => rfl
  | inr l => cases l with
    | inl ei => exact step
    | inr e => exact step

theorem alignment_agreement_reachable {n : ℕ} {U : Finset (S.layout n).Block}
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    (hr : 2 ≤ r) {a c : (S.layout n).Corner}
    (ha : S.SameAlignment n cut cut' a.1)
    (h : ((S.layout n).cornerGraph hr U).Reachable a c) :
    S.SameAlignment n cut cut' c.1 := by
  apply SimpleGraph.reachable_propagate h ha
  intro u v _ huv hh
  obtain ⟨x, hx, hd⟩ := huv
  cases x with
  | inl x => rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hh
  | inr x =>
    have hl := (S.layout n).vertical_usedLink hx
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.alignment_link_forward hc hc' hl hh
    · exact S.alignment_link_backward hc hc' hl hh

end ComparisonSchemas

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

def arm (n : ℕ) (cut : E → Fin n) : S.InternalType n → Option (E × Bool)
  | .inl _ => none
  | .inr (e, j) => some (e, decide (S.onLeft n cut e j))

def NoRealFrom (n : ℕ) (hr : 2 ≤ r) (U : Finset (S.layout n).Block)
    (a : (S.layout n).Corner) : Prop :=
  ∀ c, ((S.layout n).cornerGraph hr U).Reachable a c → ∀ p, c.1 ≠ Sum.inl p

theorem arm_link {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) {l : S.Link n} (hl : l ∈ (S.layout n).usedLinks U)
    (hf : ∀ p, (S.layout n).first l ≠ Sum.inl p)
    (hs : ∀ p, (S.layout n).second l ≠ Sum.inl p) :
    S.arm n cut ((S.layout n).first l) = S.arm n cut ((S.layout n).second l) := by
  cases l with
  | inl e => exact (hf (S.source e) rfl).elim
  | inr l => cases l with
    | inl ei =>
      obtain ⟨e, j⟩ := ei
      have hj : j ≠ cut e := fun h => hc e (h ▸ hl)
      change some (e, decide (S.onLeft n cut e j.castSucc)) =
        some (e, decide (S.onLeft n cut e j.succ))
      simp only [S.cut_middle hj]
    | inr e => exact (hs (S.target e) rfl).elim

theorem arm_reachable {n : ℕ} {U : Finset (S.layout n).Block} {cut : E → Fin n}
    (hc : S.Avoids n U cut) (hr : 2 ≤ r) {a c : (S.layout n).Corner}
    (hn : S.NoRealFrom n hr U a)
    (hh : ((S.layout n).cornerGraph hr U).Reachable a c) :
    S.arm n cut c.1 = S.arm n cut a.1 := by
  apply SimpleGraph.reachable_propagate (P := fun d => S.arm n cut d.1 = S.arm n cut a.1) hh rfl
  intro u v hu huv ih
  have hv := hu.trans huv.reachable
  obtain ⟨x, hx, hd⟩ := huv
  cases x with
  | inl x => rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ih
  | inr x =>
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (S.arm_link hc ((S.layout n).vertical_usedLink hx) (hn _ hu) (hn _ hv)).symm.trans ih
    · exact (S.arm_link hc ((S.layout n).vertical_usedLink hx) (hn _ hv) (hn _ hu)).trans ih

theorem arm_label {n : ℕ} {cut : E → Fin n} {c : (S.layout n).Corner}
    {e : E} {side : Bool} (h : S.arm n cut c.1 = some (e, side)) :
    c.2.2.val ∈ S.domain e c.2.1 ∧
      S.align n cut c = if side then c.2.2.val else S.permutation e c.2.1 c.2.2.val := by
  obtain ⟨t, i, a⟩ := c
  cases t with
  | inl p => cases h
  | inr ej =>
    obtain ⟨f, j⟩ := ej
    have he := (Prod.mk.inj (Option.some.inj h)).1
    have hs := (Prod.mk.inj (Option.some.inj h)).2
    subst f
    refine ⟨a.property, ?_⟩
    change (if S.onLeft n cut e j then a.val else S.permutation e i a.val) = _
    rw [← hs]
    simp only [decide_eq_true_eq]

theorem arm_shift {n : ℕ} {cut : E → Fin n} {t : S.InternalType n}
    {e : E} {side : Bool} (b : E → Bit) (q : S.RealShift)
    (h : S.arm n cut t = some (e, side)) :
    ∃ j : Fin (n + 1), t = Sum.inr (e, j) ∧ ∀ k : Fin 1,
      S.starShift n cut b q (.inr (e, j)) k =
        if side then S.left e (q (S.source e)) else b e + S.right e (q (S.target e)) := by
  cases t with
  | inl p => cases h
  | inr fj =>
    obtain ⟨f, j⟩ := fj
    have he := (Prod.mk.inj (Option.some.inj h)).1
    have hs := (Prod.mk.inj (Option.some.inj h)).2
    subst f
    refine ⟨j, rfl, ?_⟩
    intro k
    change (if S.onLeft n cut e j then _ else _) = _
    rw [← hs]
    simp only [decide_eq_true_eq]

end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem blockStart_eq (a : R.Corner → Bool) (b : R.Block) :
    R.blockStart a b = a (R.blockRepresentative b) := by cases b <;> rfl

theorem representative_row (b : R.Block) : (R.blockRepresentative b).2.1 = R.blockRow b := by
  cases b <;> rfl

theorem wrapping_names_reachable (hr : 3 ≤ r) {U : Finset R.Block}
    (hu : U.card ≤ r) (hw : R.Wrapping (by omega) U) {b : R.Block} (hb : b ∈ U)
    {x : R.Name} (hx : x ∈ R.names U) :
    (R.cornerGraph (by omega) U).Reachable (R.blockRepresentative b) (R.nameFirst x) ∧
    (R.cornerGraph (by omega) U).Reachable (R.blockRepresentative b) (R.nameSecond x) := by
  classical
  obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
  have hbc := R.wrapping_blocks_reachable hr hu hw hb hc
  have hc' := R.block_reachable (by omega) hc hxc
  exact ⟨hbc.trans hc'.1, hbc.trans hc'.2⟩

end RingLayout

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

theorem wrapping_real_addresses {n : ℕ} (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r) (hw : (S.layout n).Wrapping (by omega) U)
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {A A' : Fin r → Bool}
    (hA : (S.layout n).IsWrappingAddress U (S.align n cut) A)
    (hA' : (S.layout n).IsWrappingAddress U (S.align n cut') A')
    {b : (S.layout n).Block} (hb : b ∈ U)
    {d : (S.layout n).Corner} {p : P} (hd : d.1 = Sum.inl p)
    (hbd : ((S.layout n).cornerGraph (by omega) U).Reachable ((S.layout n).blockRepresentative b) d) :
    A = A' := by
  funext i
  obtain ⟨c, hcu, hci⟩ := Finset.mem_image.mp ((S.layout n).wrapping_rows hr hw i)
  have hdc := hbd.symm.trans ((S.layout n).wrapping_blocks_reachable hr hu hw hb hcu)
  have hd' : S.SameAlignment n cut cut' d.1 := by rw [hd]; exact fun _ _ => rfl
  have he := S.alignment_agreement_reachable hc hc' (by omega) hd' hdc
  have he' : (S.layout n).blockStart (S.align n cut) c =
      (S.layout n).blockStart (S.align n cut') c := by
    rw [RingLayout.blockStart_eq, RingLayout.blockStart_eq]
    exact he _ _
  rw [(hA c hcu).1, (hA' c hcu).1, hci] at he'
  exact he'

def expressAddress (e : E) (side : Bool) (a : S.DomainAddress e) : Fin r → Bool :=
  fun i => if side then (a i).val else S.mapping e i (a i)

theorem wrapping_internal_addresses {n : ℕ} (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r) (hw : (S.layout n).Wrapping (by omega) U)
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {A A' : Fin r → Bool}
    (hA : (S.layout n).IsWrappingAddress U (S.align n cut) A)
    (hA' : (S.layout n).IsWrappingAddress U (S.align n cut') A')
    {b : (S.layout n).Block} (hb : b ∈ U)
    (hn : S.NoRealFrom n (by omega) U ((S.layout n).blockRepresentative b))
    {e : E} {side side' : Bool}
    (ha : S.arm n cut ((S.layout n).blockRepresentative b).1 = some (e, side))
    (ha' : S.arm n cut' ((S.layout n).blockRepresentative b).1 = some (e, side')) :
    ∃ a : S.DomainAddress e, A = S.expressAddress e side a ∧ A' = S.expressAddress e side' a := by
  classical
  have hex (i : Fin r) : ∃ c ∈ U, (S.layout n).blockRow c = i :=
    Finset.mem_image.mp ((S.layout n).wrapping_rows hr hw i)
  choose c hcu hci using hex
  have harm (i : Fin r) := (S.arm_reachable hc (by omega) hn
    ((S.layout n).wrapping_blocks_reachable hr hu hw hb (hcu i))).trans ha
  have harm' (i : Fin r) := (S.arm_reachable hc' (by omega) hn
    ((S.layout n).wrapping_blocks_reachable hr hu hw hb (hcu i))).trans ha'
  have hrow (i : Fin r) : ((S.layout n).blockRepresentative (c i)).2.1 = i :=
    ((S.layout n).representative_row (c i)).trans (hci i)
  let a : S.DomainAddress e := fun i => ⟨((S.layout n).blockRepresentative (c i)).2.2.val,
    by simpa only [hrow i] using (S.arm_label (harm i)).1⟩
  refine ⟨a, ?_, ?_⟩
  · funext i
    have he := (S.arm_label (harm i)).2
    change S.align n cut ((S.layout n).blockRepresentative (c i)) =
      (if side then (a i).val else S.permutation e ((S.layout n).blockRepresentative (c i)).2.1 (a i).val) at he
    rw [hrow i] at he
    have hs := (hA (c i) (hcu i)).1
    rw [RingLayout.blockStart_eq, hci i] at hs
    rw [← hs, he]
    change (if side then (a i).val else S.permutation e i (a i).val) = _
    rw [S.permutation_apply]
    rfl
  · funext i
    have he := (S.arm_label (harm' i)).2
    change S.align n cut' ((S.layout n).blockRepresentative (c i)) =
      (if side' then (a i).val else S.permutation e ((S.layout n).blockRepresentative (c i)).2.1 (a i).val) at he
    rw [hrow i] at he
    have hs := (hA' (c i) (hcu i)).1
    rw [RingLayout.blockStart_eq, hci i] at hs
    rw [← hs, he]
    change (if side' then (a i).val else S.permutation e i (a i).val) = _
    rw [S.permutation_apply]
    rfl

end ComparisonSchemas

end WLIdentification

end OAI
