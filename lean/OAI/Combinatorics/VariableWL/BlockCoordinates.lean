import OAI.Combinatorics.VariableWL.BlockImages

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19 uVariable20 uVariable21

namespace VariableWL.Subdivision
variable {P : Type uVariable1} {E : Type uVariable2} {n : ℕ}

theorem realFree_reachable_wire (hn : 0 < n) (src dst : E → P)
    (S : Set (Link E n)) (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn src dst S).Reachable (.inr q) (.inl p))
    {v : Vertex P E n} (hr : (supportGraph hn src dst S).Reachable (.inr q) v) :
    ∃ j, v = .inr (q.1,j) := by
  have aux {u v : Vertex P E n} (p : (supportGraph hn src dst S).Walk u v)
      (hu : ∃ j, u = .inr (q.1,j))
      (hreach : (supportGraph hn src dst S).Reachable (.inr q) u) :
      ∃ j, v = .inr (q.1,j) := by
    induction p with
    | nil => exact hu
    | @cons u v w ha p ih =>
      obtain ⟨i,rfl⟩ := hu
      have hv := hreach.trans ha.reachable
      obtain ⟨q',rfl⟩ : ∃ q', v = .inr q' := by
        cases v with
        | inl real => exact (hnr real hv).elim
        | inr q' => exact ⟨q',rfl⟩
      have hw := internal_adj_wire hn src dst S ha
      exact ih ⟨q'.2, by rw [hw]⟩ hv
  exact aux hr.some ⟨q.2,rfl⟩ (.refl _)
end VariableWL.Subdivision

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable3} {G H : SimpleGraph V}

theorem walkSum_mapLe (ω : V → V → Bit) (h : G ≤ H) {u v : V} (p : G.Walk u v) :
    walkSum ω (p.mapLe h) = walkSum ω p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact congrArg (_ + ·) ih

theorem exists_nonzero_edge (ω : V → V → Bit) {u v : V} (p : G.Walk u v)
    (hp : walkSum ω p ≠ 0) :
    ∃ x y, G.Reachable u x ∧ G.Adj x y ∧ ω x y ≠ 0 := by
  induction p with
  | nil => exact (hp rfl).elim
  | @cons u v w ha p ih =>
    by_cases he : ω u v = 0
    · obtain ⟨x,y,hx,hy,hh⟩ := ih (by simpa only [walkSum_cons, he, zero_add] using hp)
      exact ⟨x,y,ha.reachable.trans hx,hy,hh⟩
    · exact ⟨u,v,.refl _,ha,he⟩
end VariableWL.Markers

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable4} {E : Type uVariable5} (J : ProductImages.Instance r P E)

def anchor : RawBlock r n P E → Corner r n P E
  | .inl h => end0 J (.inl h)
  | .inr s => end0 J (.inl (squareLeft J s))

theorem readout_reachable (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J))
    {b : Block (n := n) J} (hb : b ∈ U) {a : Readout r n P E}
    (ha : HasReadout J b.val a) :
    (diagram J hr hn U).Reachable (anchor J b.val) (end0 J a) ∧
      (diagram J hr hn U).Reachable (anchor J b.val) (end1 J a) := by
  obtain ⟨b,hb'⟩ := b
  cases b with
  | inl h =>
    cases ha
    exact ⟨.refl _, (readout_adj J hr hn U hb rfl).reachable⟩
  | inr s =>
    have hL := (readout_adj J hr hn U hb (Or.inl rfl)).reachable
    have hR := (readout_adj J hr hn U hb (Or.inr (Or.inl rfl))).reachable
    have hB := (readout_adj J hr hn U hb (Or.inr (Or.inr (Or.inl rfl)))).reachable
    have hT := (readout_adj J hr hn U hb (Or.inr (Or.inr (Or.inr rfl)))).reachable
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨.refl _,hL⟩
    · exact ⟨hB,hB.trans hR⟩
    · exact ⟨.refl _,hB⟩
    · exact ⟨hL,hL.trans hT⟩

theorem wrapping_mono (hr : 3 ≤ r) (hn : 0 < n)
    {U V : Set (Block (n := n) J)} (h : U ⊆ V) {marked : Fin r}
    (hw : (rowDiagram J hr hn U).Wraps marked) : (rowDiagram J hr hn V).Wraps marked := by
  obtain ⟨v,p,hp⟩ := hw
  exact ⟨v,p.mapLe (diagram_mono J (by omega) hn h),
    (Markers.walkSum_mapLe _ _ p).trans hp⟩

theorem wrapping_connected (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) {marked : Fin r}
    (hw : (rowDiagram J hr hn U).Wraps marked) (hc : U.card = r) :
    ∃ root : Corner r n P E, ∀ b ∈ U,
      (diagram J (by omega) hn U).Reachable root (anchor J b.val) := by
  classical
  have : NeZero r := ⟨by omega⟩
  have hi := wrapping_row_injective J hr hn U hw hc
  obtain ⟨root,p,hp⟩ := hw
  refine ⟨root, ?_⟩
  intro b hb
  have hpar := (rowDiagram J hr hn U).row_parity_all
    Wrapping.RowDiagram.finRotate_orbit p (row b.val) marked
  obtain ⟨u,v,hu,hv,he⟩ := Markers.exists_nonzero_edge _ p
    (show Markers.walkSum ((rowDiagram J hr hn U).rowWeight (row b.val)) p ≠ 0 by
      rw [hpar,hp]; exact one_ne_zero)
  have htag : horizontalTag u v = some (row b.val) := by
    by_contra hh
    exact he (ite_eq_right hh)
  obtain ⟨b',hb',a,ha,heq⟩ := hv
  have haRow : row b'.val = row b.val := by
    have ht : Sum.elim (fun h => some h.row) (fun _ => none) a = some (row b.val) := by
      rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hh := (horizontalTag_readout J hr a).1.symm.trans htag
        cases a <;> exact hh
      · have hh := (horizontalTag_readout J hr a).2.symm.trans htag
        cases a <;> exact hh
    cases a with
    | inr a => cases ht
    | inl a => exact (hasReadout_horizontal_row J ha).symm.trans (Option.some.inj ht)
  have hbb : b' = b := hi hb' hb haRow
  subst b'
  obtain ⟨h0,h1⟩ := readout_reachable J (by omega) hn U hb ha
  rcases heq with ⟨rfl,_⟩ | ⟨rfl,_⟩
  · exact hu.trans h0.symm
  · exact hu.trans h1.symm
end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable6} {E : Type uVariable7} (J : ProductImages.Instance r P E)

theorem lift_scalar_to_cut (hn : 0 < n) (Q : J.Witness)
    (S : Set (Link E n)) (cut : E → Fin (n+1))
    (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (q : E × Fin n)
    (a : Address r) (ha : J.Allowed q.1 a) {b : Bit}
    (hb : b ∈ Q.wireValues q.1 a) :
    ∃ g : J.Shifts n, J.ShiftSystem S g ∧ g.2 q = b ∧
      ∀ p, (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p) →
        g.1 p ∈ Q.values p (fun i => J.alignment cut (.inr q) i (a i)) := by
  classical
  by_cases hj : q.2.val < (cut q.1).val
  · obtain ⟨v,hv,hvb⟩ := Q.lift_left q.1 a hb
    let values : ∀ p, Vec (J.dimension p) := Function.update (fun _ => 0) (J.source q.1) v
    have hval : values (J.source q.1) = v := Function.update_self _ _ _
    refine ⟨J.cutShifts cut values, fun l hl => J.cutShifts_equation hn cut values l (hc l hl), ?_, ?_⟩
    · simpa only [cutShifts, ite_eq_left hj, hval] using hvb
    · intro p hp
      have ho := owner_walk hn J.source J.target S cut hc hp.some
      have he : J.source q.1 = p := by simpa only [owner, ite_eq_left hj] using ho
      subst p
      simpa only [cutShifts, hval, alignment, ite_eq_left hj, Equiv.refl_apply] using hv
  · obtain ⟨v,hv,hvb⟩ := Q.lift_right q.1 a ha hb
    let values : ∀ p, Vec (J.dimension p) := Function.update (fun _ => 0) (J.target q.1) v
    have hval : values (J.target q.1) = v := Function.update_self _ _ _
    refine ⟨J.cutShifts cut values, fun l hl => J.cutShifts_equation hn cut values l (hc l hl), ?_, ?_⟩
    · simpa only [cutShifts, ite_eq_right hj, hval] using hvb
    · intro p hp
      have ho := owner_walk hn J.source J.target S cut hc hp.some
      have he : J.target q.1 = p := by simpa only [owner, ite_eq_right hj] using ho
      subst p
      have had : (fun i => J.alignment cut (.inr q) i (a i)) = J.mapAddress q.1 a := by
        funext i
        simp only [alignment, ite_eq_right hj, mapAddress, J.ambient_on_domain _ _ _ (ha i)]
      simpa only [cutShifts, hval, had] using hv

theorem agree_from_real [DecidableEq E] (hn : 0 < n)
    (S : Finset (Link E n)) (hS : S.card < n+1) {h g : J.Shifts n}
    (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g) (p : P)
    (he : h.1 p = g.1 p) {v : Vertex P E n}
    (hv : (supportGraph hn J.source J.target S).Reachable (.inl p) v) :
    J.AgreeAt h g v := by
  apply J.agree_reachable hn S hh hg (.inl p) he _ hv
  intro p' hp'
  have hpp := at_most_one_real hn J.source J.target S hS hp'
  subst p'
  exact he

theorem agree_from_internal (hn : 0 < n) (S : Set (Link E n))
    {h g : J.Shifts n} (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g)
    (q : E × Fin n) (he : h.2 q = g.2 q)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    {v : Vertex P E n} (hv : (supportGraph hn J.source J.target S).Reachable (.inr q) v) :
    J.AgreeAt h g v :=
  J.agree_reachable hn S hh hg (.inr q) he (fun p hp => (hnr p hp).elim) hv
end VariableWL.ProductImages.Instance

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable8} {E : Type uVariable9} (J : ProductImages.Instance r P E)

noncomputable def componentBlocks (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent) :
    Finset (Block (n := n) J) := by
  classical
  exact U.filter fun b => (diagram J hr hn U).connectedComponentMk (anchor J b.val) = c

theorem mem_componentBlocks (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    (b : Block (n := n) J) : b ∈ componentBlocks J hr hn U c ↔
      b ∈ U ∧ (diagram J hr hn U).connectedComponentMk (anchor J b.val) = c := by
  classical
  exact Finset.mem_filter

theorem componentBlocks_subset (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent) :
    componentBlocks J hr hn U c ⊆ U := by
  intro b hb
  exact ((mem_componentBlocks J hr hn U c b).mp hb).1

theorem readout_component (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J))
    {b : Block (n := n) J} (hb : b ∈ U) {a : Readout r n P E}
    (ha : HasReadout J b.val a) :
    (diagram J hr hn U).connectedComponentMk (anchor J b.val) =
      (diagram J hr hn U).connectedComponentMk (end0 J a) ∧
    (diagram J hr hn U).connectedComponentMk (anchor J b.val) =
      (diagram J hr hn U).connectedComponentMk (end1 J a) := by
  obtain ⟨h0,h1⟩ := readout_reachable J hr hn U hb ha
  exact ⟨SimpleGraph.ConnectedComponent.sound h0, SimpleGraph.ConnectedComponent.sound h1⟩

theorem component_adj (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    {v w : Corner r n P E} (hv : (diagram J hr hn U).connectedComponentMk v = c)
    (ha : (diagram J hr hn U).Adj v w) :
    (diagram J hr hn (componentBlocks J hr hn U c)).Adj v w := by
  obtain ⟨b,hb,a,hb',he⟩ := ha
  have hc : (diagram J hr hn U).connectedComponentMk (anchor J b.val) = c := by
    obtain ⟨h0,h1⟩ := readout_component J hr hn U hb hb'
    rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact h0.trans hv
    · exact h1.trans hv
  exact ⟨b, (mem_componentBlocks J hr hn U c b).mpr ⟨hb,hc⟩,a,hb',he⟩

theorem component_reachable (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    {v w : Corner r n P E} (hv : (diagram J hr hn U).connectedComponentMk v = c)
    (hw : (diagram J hr hn U).Reachable v w) :
    (diagram J hr hn (componentBlocks J hr hn U c)).Reachable v w := by
  obtain ⟨p⟩ := hw
  induction p with
  | nil => exact .refl _
  | cons ha p ih =>
    have hv' := (SimpleGraph.ConnectedComponent.sound ha.reachable).symm.trans hv
    exact (component_adj J hr hn U c hv ha).reachable.trans (ih hv')

theorem component_anchors_connected (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    {b b' : Block (n := n) J} (hb : b ∈ componentBlocks J hr hn U c)
    (hb' : b' ∈ componentBlocks J hr hn U c) :
    (diagram J hr hn (componentBlocks J hr hn U c)).Reachable
      (anchor J b.val) (anchor J b'.val) := by
  have hb0 := ((mem_componentBlocks J hr hn U c b).mp hb).2
  have hb1 := ((mem_componentBlocks J hr hn U c b').mp hb').2
  exact component_reachable J hr hn U c hb0 (SimpleGraph.ConnectedComponent.exact (hb0.trans hb1.symm))

end VariableWL.Blocks

namespace VariableWL.Subdivision
variable {P : Type uVariable10} {E : Type uVariable11} {A : Type uVariable12} {n : ℕ}

theorem internal_reachable_invariant (hn : 0 < n) (src dst : E → P)
    (S : Set (Link E n)) (F : E × Fin n → A)
    (hF : ∀ q q', (supportGraph hn src dst S).Adj (.inr q) (.inr q') → F q = F q')
    (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn src dst S).Reachable (.inr q) (.inl p))
    {q' : E × Fin n} (hr : (supportGraph hn src dst S).Reachable (.inr q) (.inr q')) :
    F q = F q' := by
  have aux {u v : Vertex P E n} (p : (supportGraph hn src dst S).Walk u v)
      (hu : ∃ qu, u = .inr qu ∧ F q = F qu)
      (hreach : (supportGraph hn src dst S).Reachable (.inr q) u) :
      ∃ qv, v = .inr qv ∧ F q = F qv := by
    induction p with
    | nil => exact hu
    | @cons u v w ha p ih =>
      obtain ⟨qu,rfl,hu⟩ := hu
      have hv := hreach.trans ha.reachable
      obtain ⟨qv,rfl⟩ : ∃ qv, v = .inr qv := by
        cases v with
        | inl real => exact (hnr real hv).elim
        | inr qv => exact ⟨qv,rfl⟩
      exact ih ⟨qv,rfl,hu.trans (hF qu qv ha)⟩ hv
  obtain ⟨qv,he,hh⟩ := aux hr.some ⟨q,rfl,rfl⟩ (.refl _)
  cases Sum.inr.inj he
  exact hh
end VariableWL.Subdivision

namespace VariableWL.ProductImages.Instance
open Subdivision
variable {r n : ℕ} {P : Type uVariable13} {E : Type uVariable14} (J : ProductImages.Instance r P E)

theorem alignment_internal_adj (hn : 0 < n) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1)
    {q q' : E × Fin n} (ha : (supportGraph hn J.source J.target S).Adj (.inr q) (.inr q'))
    (i : Fin r) : J.alignment cut (.inr q) i = J.alignment cut (.inr q') i := by
  obtain ⟨l,hl,⟨he,he'⟩ | ⟨he,he'⟩⟩ := ha
  · have hlast : l.2.val ≠ n := by
      intro h; simp only [right, dite_eq_left h] at he'; cases he'
    have h := J.alignment_link hn cut l (hc l hl) i
    simpa only [← he, ← he', transport, ite_eq_right hlast,
      show Equiv.refl Bool = (1 : Equiv.Perm Bool) from rfl, mul_one] using h
  · have hlast : l.2.val ≠ n := by
      intro h; simp only [right, dite_eq_left h] at he; cases he
    have h := J.alignment_link hn cut l (hc l hl) i
    simpa only [← he, ← he', transport, ite_eq_right hlast,
      show Equiv.refl Bool = (1 : Equiv.Perm Bool) from rfl, mul_one] using h.symm

theorem alignment_internal_reachable (hn : 0 < n) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    {q' : E × Fin n} (hr : (supportGraph hn J.source J.target S).Reachable (.inr q) (.inr q'))
    (i : Fin r) : J.alignment cut (.inr q) i = J.alignment cut (.inr q') i :=
  internal_reachable_invariant hn J.source J.target S (fun q => J.alignment cut (.inr q) i)
    (fun _ _ h => J.alignment_internal_adj hn S cut hc h i) q hnr hr
end VariableWL.ProductImages.Instance

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable15} {E : Type uVariable16} (J : ProductImages.Instance r P E)

noncomputable def typesOf : RawBlock r n P E → Finset (Vertex P E n) := by
  classical
  exact fun b => match b with
    | .inl h => {h.type}
    | .inr s => {left J.source s.link, right J.target s.link}

noncomputable def supportTypes (U : Finset (Block (n := n) J)) : Finset (Vertex P E n) := by
  classical
  exact U.biUnion fun b => typesOf J b.val

theorem type_has_horizontal (b : RawBlock r n P E) {t : Vertex P E n}
    (ht : t ∈ typesOf J b) : ∃ h : Horizontal r n P E,
      HasReadout J b (.inl h) ∧ h.type = t := by
  classical
  cases b with
  | inl h =>
    have he : t = h.type := by simpa only [typesOf, Finset.mem_singleton] using ht
    exact ⟨h,rfl,he.symm⟩
  | inr s =>
    simp only [typesOf, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ⟨squareLeft J s,Or.inl rfl,rfl⟩
    · exact ⟨squareRight J s,Or.inr (Or.inl rfl),rfl⟩

theorem anchor_mem_types (b : RawBlock r n P E) : (anchor J b).2.1 ∈ typesOf J b := by
  classical
  cases b <;> simp [anchor, typesOf, end0, squareLeft]

theorem supportLinks_endpoints (U : Finset (Block (n := n) J)) {l : Link E n}
    (hl : l ∈ supportLinks J U) :
    left J.source l ∈ supportTypes J U ∧ right J.target l ∈ supportTypes J U := by
  classical
  obtain ⟨b,hb,hl⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨b,hvalid⟩ := b
  cases b with
  | inl h => simp [linksOf] at hl
  | inr s =>
    have he : l = s.link := by simpa only [linksOf, Finset.mem_singleton] using hl
    subst l
    constructor <;> apply Finset.mem_biUnion.mpr ⟨⟨.inr s,hvalid⟩,hb,?_⟩ <;> simp [typesOf]

theorem support_reachable_mem (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Vertex P E n} (hv : v ∈ supportTypes J U)
    (hw : (supportGraph hn J.source J.target (supportLinks J U)).Reachable v w) :
    w ∈ supportTypes J U := by
  obtain ⟨p⟩ := hw
  induction p with
  | nil => exact hv
  | cons ha p ih =>
    apply ih
    obtain ⟨l,hl,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ := ha
    · exact (supportLinks_endpoints J U hl).2
    · exact (supportLinks_endpoints J U hl).1

theorem support_types_connected (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J))
    (hconn : ∀ b ∈ U, ∀ b' ∈ U, (diagram J hr hn U).Reachable (anchor J b.val) (anchor J b'.val))
    {v w : Vertex P E n} (hv : v ∈ supportTypes J U) (hw : w ∈ supportTypes J U) :
    (supportGraph hn J.source J.target (supportLinks J U)).Reachable v w := by
  classical
  obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨b',hb',hw⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨h,hh,rfl⟩ := type_has_horizontal J b.val hv
  obtain ⟨h',hh',rfl⟩ := type_has_horizontal J b'.val hw
  have h0 := (readout_reachable J hr hn U hb hh).1
  have h1 := (readout_reachable J hr hn U hb' hh').1
  exact projection_reachable J hr hn U ((h0.symm.trans (hconn b hb b' hb')).trans h1)

noncomputable def addressAt (cut : E → Fin (n+1)) (a : Fin r → Bool)
    (t : Vertex P E n) : Fin r → Bool := fun i => (J.alignment cut t i).symm (a i)

def Recovers (cut : E → Fin (n+1)) (U : Finset (Block (n := n) J))
    (a : Fin r → Bool) : Prop := ∀ b ∈ U,
    firstLabel J cut b.val = a (row b.val) ∧
      lastLabel J cut b.val = a (finRotate r (row b.val))

theorem anchor_label_allowed (b : Block (n := n) J) :
    (anchor J b.val).2.2 ∈ J.labels (anchor J b.val).2.1 (row b.val) := by
  obtain ⟨b,hb⟩ := b
  cases b with
  | inl h => exact hb.1
  | inr s => exact J.matches_left s.link s.row ⟨hb.1,rfl⟩

theorem firstLabel_anchor (cut : E → Fin (n+1)) (b : RawBlock r n P E) :
    firstLabel J cut b = J.alignment cut (anchor J b).2.1 (row b) (anchor J b).2.2 := by
  cases b <;> rfl

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable17} {E : Type uVariable18} (J : ProductImages.Instance r P E)

theorem recovers_unique (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (cut : E → Fin (n+1))
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked)
    {a a' : Fin r → Bool} (ha : Recovers J cut U a) (ha' : Recovers J cut U a') : a = a' := by
  classical
  have : NeZero r := ⟨by omega⟩
  funext i
  obtain ⟨b,hb,hi⟩ := Finset.mem_image.mp ((rowDiagram J hr hn U).covers_rows U
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw i)
  rw [← hi, ← (ha b hb).1, (ha' b hb).1]

theorem wrapping_address_allowed (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (cut : E → Fin (n+1))
    (hc : ∀ l ∈ supportLinks J U, l.2 ≠ cut l.1)
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) (hcard : U.card = r)
    (q : E × Fin n) (hq : (.inr q : Vertex P E n) ∈ supportTypes J U)
    (hnr : ∀ p, (.inl p : Vertex P E n) ∉ supportTypes J U)
    {a : Fin r → Bool} (ha : Recovers J cut U a) :
    J.Allowed q.1 (addressAt J cut a (.inr q)) := by
  classical
  have : NeZero r := ⟨by omega⟩
  obtain ⟨root,hroot⟩ := wrapping_connected J hr hn U hw hcard
  have hconn : ∀ b ∈ U, ∀ b' ∈ U,
      (diagram J (by omega) hn U).Reachable (anchor J b.val) (anchor J b'.val) :=
    fun b hb b' hb' => (hroot b hb).symm.trans (hroot b' hb')
  have hnr' : ∀ p, ¬ (supportGraph hn J.source J.target (supportLinks J U)).Reachable
      (.inr q) (.inl p) := fun p hp => hnr p (support_reachable_mem J hn U hq hp)
  intro i
  obtain ⟨b,hb,hi⟩ := Finset.mem_image.mp ((rowDiagram J hr hn U).covers_rows U
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw i)
  have ht : (anchor J b.val).2.1 ∈ supportTypes J U :=
    Finset.mem_biUnion.mpr ⟨b,hb,anchor_mem_types J b.val⟩
  have hreach := support_types_connected J (by omega) hn U hconn hq ht
  obtain ⟨j,he⟩ := realFree_reachable_wire hn J.source J.target (supportLinks J U) q hnr' hreach
  have hal := J.alignment_internal_reachable hn (supportLinks J U) cut hc q hnr'
    (he ▸ hreach) i
  have hal' : J.alignment cut (.inr q) i = J.alignment cut (anchor J b.val).2.1 i := by
    simpa only [he] using hal
  have hlabel := anchor_label_allowed J b
  rw [hi, he] at hlabel
  change (J.alignment cut (.inr q) i).symm (a i) ∈ J.domain q.1 i
  rw [hal', ← hi, ← (ha b hb).1, firstLabel_anchor, Equiv.symm_apply_apply]
  simpa only [hi, ProductImages.Instance.labels] using hlabel

theorem permutation_coordinates {A : Type uVariable19} (f g f' g' : Equiv.Perm A)
    (h : f * g⁻¹ = f' * g'⁻¹) (x : A) : f.symm (f' x) = g.symm (g' x) := by
  have he := congrArg (fun p : Equiv.Perm A => f⁻¹ * p * g') h
  have hfg : g⁻¹ * g' = f⁻¹ * f' := by simpa only [mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one] using he
  exact congrArg (fun e : Equiv.Perm A => e x) hfg.symm

theorem addressAt_cut_independent (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (cut cut' : E → Fin (n+1))
    (hc : ∀ l ∈ supportLinks J U, l.2 ≠ cut l.1)
    (hc' : ∀ l ∈ supportLinks J U, l.2 ≠ cut' l.1)
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked)
    {a a' : Fin r → Bool} (ha : Recovers J cut U a) (ha' : Recovers J cut' U a')
    (t : Vertex P E n)
    (hconn : ∀ b ∈ U, (supportGraph hn J.source J.target (supportLinks J U)).Reachable
      t (anchor J b.val).2.1) : addressAt J cut a t = addressAt J cut' a' t := by
  classical
  have : NeZero r := ⟨by omega⟩
  funext i
  obtain ⟨b,hb,hi⟩ := Finset.mem_image.mp ((rowDiagram J hr hn U).covers_rows U
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw i)
  have hrel := J.relativeAlignment_reachable hn (supportLinks J U) cut cut' hc hc' (hconn b hb) i
  have hp := permutation_coordinates (J.alignment cut t i) (J.alignment cut' t i)
    (J.alignment cut (anchor J b.val).2.1 i) (J.alignment cut' (anchor J b.val).2.1 i)
    hrel (anchor J b.val).2.2
  change (J.alignment cut t i).symm (a i) = (J.alignment cut' t i).symm (a' i)
  rw [← hi, ← (ha b hb).1, ← (ha' b hb).1, firstLabel_anchor, firstLabel_anchor]
  simpa only [hi] using hp

theorem recovered_overlap (hr : 3 ≤ r) (hn : 0 < n)
    (U W W' : Finset (Block (n := n) J)) (cut : E → Fin (n+1))
    (hW : W ⊆ U) (hW' : W' ⊆ U) (hU : U.card ≤ r+1)
    (hcW : W.card = r) (hcW' : W'.card = r)
    {marked : Fin r} (hw : (rowDiagram J hr hn W).Wraps marked)
    {a a' : Fin r → Bool} (ha : Recovers J cut W a) (ha' : Recovers J cut W' a') : a = a' := by
  classical
  apply Wrapping.overlap_address_unique (finRotate r) (Wrapping.finRotate_no_fixed (by omega))
    U W W' (fun b => row b.val) hW hW' (by simpa using hU)
    (by simpa using hcW) (by simpa using hcW')
    (wrapping_row_injective J hr hn W hw hcW) a a'
  intro b hb
  obtain ⟨hb,hb'⟩ := Finset.mem_inter.mp hb
  exact ⟨(ha b hb).1.symm.trans (ha' b hb').1, (ha b hb).2.symm.trans (ha' b hb').2⟩
end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable20} {E : Type uVariable21} (J : ProductImages.Instance r P E)

theorem scalar_image_of_real (hn : 0 < n) (Q : J.Witness)
    (S : Finset (Link E n)) (hS : S.card < n+1) (cut : E → Fin (n+1))
    (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (h : J.Shifts n) (hh : J.ShiftSystem S h)
    (q : E × Fin n) (p : P)
    (hp : (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    (a : Address r) (ha : J.Allowed q.1 a)
    (hreal : h.1 p ∈ Q.values p (fun i => J.alignment cut (.inr q) i (a i))) :
    h.2 q ∈ Q.wireValues q.1 a := by
  classical
  have hg : J.ShiftSystem S (J.cutShifts cut h.1) := fun l hl =>
    J.cutShifts_equation hn cut h.1 l (hc l hl)
  have he := J.agree_from_real hn S hS hh hg p rfl hp.symm
  change h.2 q = (J.cutShifts cut h.1).2 q at he
  rw [he]
  have ho := owner_walk hn J.source J.target S cut hc hp.some
  by_cases hj : q.2.val < (cut q.1).val
  · have hpe : J.source q.1 = p := by simpa only [owner, ite_eq_left hj] using ho
    subst p
    have hmem : h.1 (J.source q.1) ∈ Q.values (J.source q.1) a := by
      simpa only [alignment, ite_eq_left hj, Equiv.refl_apply] using hreal
    exact ⟨h.1 (J.source q.1),hmem, by simp only [cutShifts, ite_eq_left hj]⟩
  · have hpe : J.target q.1 = p := by simpa only [owner, ite_eq_right hj] using ho
    subst p
    have had : (fun i => J.alignment cut (.inr q) i (a i)) = J.mapAddress q.1 a := by
      funext i
      simp only [alignment, ite_eq_right hj, mapAddress, J.ambient_on_domain _ _ _ (ha i)]
    rw [had] at hreal
    rw [← Q.right_image q.1 a ha]
    exact ⟨h.1 (J.target q.1),hreal, by simp only [cutShifts, ite_eq_right hj]⟩
end VariableWL.ProductImages.Instance

end OAI
