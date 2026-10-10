import Mathlib
import OAI.Algebra.GroupRing.BallCount
import OAI.Algebra.GroupRing.PortSubdivision

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- All degrees are controlled by the fixed port fibers. -/
theorem subdivision_degree (Γ : PortGraph V D) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d) (a : V ⊕ D) :
    (graphNeighbors Γ.subdivision a).card ≤ d := by
  classical
  rw [card_graphNeighbors]
  cases a with
  | inl v => rw [Γ.card_original_neighbors]; exact hd v
  | inr e => rw [Γ.card_port_neighbors]; exact h2

/-- Uniformly many ports of one label lie outside both endpoint neighborhoods. -/
theorem exists_far_port (Γ : PortGraph V D) (label : D → T)
    (d R : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d)
    (x : D) (hbig : 4*d^(R+1) < Nat.card {e : D // label e = label x}) :
    ∃ e : D, label e = label x ∧
      ∀ a ∈ ({Sum.inr x,Sum.inr (Γ.reverse x)} : Set (V ⊕ D)),
      ∀ b ∈ ({Sum.inr e,Sum.inr (Γ.reverse e)} : Set (V ⊕ D)),
      ∀ p : Γ.subdivision.Walk a b, R < p.length := by
  classical
  let X := {e : D // label e = label x}
  let locX : X → V ⊕ D := fun e => .inr e.val
  let locY : X → V ⊕ D := fun e => .inr (Γ.reverse e.val)
  have hX : Function.Injective locX := by
    intro a b h; exact Subtype.ext (Sum.inr.inj h)
  have hY : Function.Injective locY := by
    intro a b h
    exact Subtype.ext (Γ.reverse_reverse.injective (Sum.inr.inj h))
  let B := ball (graphNeighbors Γ.subdivision) (Sum.inr x) R ∪
    ball (graphNeighbors Γ.subdivision) (Sum.inr (Γ.reverse x)) R
  have hB : B.card ≤ 2*d^(R+1) := by
    have ha := card_ball_le (graphNeighbors Γ.subdivision) d h2
      (subdivision_degree Γ d h2 hd) (Sum.inr x) R
    have hb := card_ball_le (graphNeighbors Γ.subdivision) d h2
      (subdivision_degree Γ d h2 hd) (Sum.inr (Γ.reverse x)) R
    exact (Finset.card_union_le _ _).trans (by omega)
  have hbad := matching_bad_card (Equiv.refl X) locX locY hX hY B
  have hlt : (Finset.univ.filter (fun e : X => locX e ∈ B ∨ locY e ∈ B)).card <
      Fintype.card X := by
    rw [Nat.card_eq_fintype_card] at hbig
    change _ < Fintype.card X at hbig
    exact lt_of_le_of_lt (hbad.trans (by omega)) hbig
  obtain ⟨e,he,hebad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Finset.univ.filter (fun e : X => locX e ∈ B ∨ locY e ∈ B))
    (t := (Finset.univ : Finset X)) (by simpa only [Finset.card_univ] using hlt)
  have he' : locX e ∉ B ∧ locY e ∉ B := by simpa only [Finset.mem_filter,
    Finset.mem_univ,true_and,not_or] using hebad
  refine ⟨e.val,e.property,?_⟩
  intro a ha b hb p
  have hn : b ∉ ball (graphNeighbors Γ.subdivision) a R := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun h => he'.1 (Finset.mem_union_left _ h)
    · exact fun h => he'.2 (Finset.mem_union_left _ h)
    · exact fun h => he'.1 (Finset.mem_union_right _ h)
    · exact fun h => he'.2 (Finset.mem_union_right _ h)
  exact far_of_not_mem_ball Γ.subdivision R hn p

omit [Fintype V] [Fintype D] in
/-- The conjugation switch is exactly the graph two-switch used in girth repair. -/
theorem subdivision_switch (Γ : PortGraph V D) (x e : D)
    (hxe : x ≠ e) (hxr : x ≠ Γ.reverse e) :
    (Γ.switch x e).subdivision =
      addEdge (addEdge (Γ.subdivision.deleteEdges
        {s(Sum.inr x,Sum.inr (Γ.reverse x)),s(Sum.inr e,Sum.inr (Γ.reverse e))})
        (Sum.inr x) (Sum.inr (Γ.reverse e))) (Sum.inr e) (Sum.inr (Γ.reverse x)) := by
  ext a b
  rw [Γ.switch_adj x e hxe hxr]
  simp only [addEdge_adj,SimpleGraph.deleteEdges_adj,Set.mem_insert_iff,
    Set.mem_singleton_iff,not_or]
  have her : e ≠ Γ.reverse x := by
    intro h
    apply hxr
    rw [h,Γ.reverse_reverse]
  have h1 : s(a,b) = s(Sum.inr x,Sum.inr (Γ.reverse e)) → a ≠ b := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using hxr
    · simpa using Ne.symm hxr
  have h2 : s(a,b) = s(Sum.inr e,Sum.inr (Γ.reverse x)) → a ≠ b := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using her
    · simpa using Ne.symm her
  tauto

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.ConditionedMatchings
open PortSubdivision BallCount GirthSwitch MatchingGraphs
variable {V D T : Type*}

/-- A matching on the signed labelled port set; inverse labels have no fixed
points. Keeping the origin function separate fixes the vertex types. -/
abbrev Matching (label : D → T) (bar : T → T) :=
  {r : Equiv.Perm D // Function.Involutive r ∧
    (∀ x, r x ≠ x) ∧ ∀ x, label (r x) = bar (label x)}

namespace Matching
variable {label : D → T} {bar : T → T}
instance : CoeFun (Matching label bar) (fun _ => D → D) := ⟨fun r => r.val⟩
instance [Fintype D] : Fintype (Matching label bar) := by
  classical
  unfold Matching
  infer_instance
instance : DecidableEq (Matching label bar) := Classical.decEq _

def graph (r : Matching label bar) (origin : D → V) : PortGraph V D :=
  ⟨origin,r,r.property.1,r.property.2.1⟩

@[simp] theorem reverse_reverse (r : Matching label bar) (x : D) : r (r x) = x := r.property.1 x
theorem label_reverse (r : Matching label bar) (x : D) :
    label (r x) = bar (label x) := r.property.2.2 x

@[ext] theorem ext {r s : Matching label bar} (h : ∀ x, r x = s x) : r = s :=
  Subtype.ext (Equiv.ext h)

variable [DecidableEq D]

/-- Conjugating by the transposition of equally labelled ports. -/
def switch (r : Matching label bar) (x e : D) (he : label x = label e) : Matching label bar :=
  ⟨(Equiv.swap x e).trans (r.val.trans (Equiv.swap x e)),by
    constructor
    · intro f; simp
    constructor
    · intro f h
      have h' := congrArg (Equiv.swap x e) h
      simp only [Equiv.trans_apply,Equiv.swap_apply_self] at h'
      exact r.property.2.1 ((Equiv.swap x e) f) h'
    · intro f
      change label ((Equiv.swap x e) (r ((Equiv.swap x e) f))) = bar (label f)
      rw [PortGraph.label_swap label x e he, r.label_reverse,PortGraph.label_swap label x e he]⟩

@[simp] theorem switch_apply (r : Matching label bar) (x e : D) (he : label x = label e) (f : D) :
    r.switch x e he f = (Equiv.swap x e) (r ((Equiv.swap x e) f)) := rfl

@[simp] theorem switch_switch (r : Matching label bar) (x e : D) (he : label x = label e) :
    (r.switch x e he).switch x e he = r := by
  ext f
  simp

theorem graph_switch (r : Matching label bar) (origin : D → V)
    (x e : D) (he : label x = label e) :
    (r.switch x e he).graph origin = (r.graph origin).switch x e := rfl

/-- Given the new matching and the fixed old pair x,y, the auxiliary port
is forced. This is the reconstructibility behind the conditional estimate. -/
theorem switch_recover (r : Matching label bar) (x y e : D)
    (he : label x = label e) (hxy : r x = y)
    (hbar : ∀ t, bar t ≠ t) : r.switch x e he y = e := by
  have hyx : y ≠ x := hxy ▸ r.property.2.1 x
  have hye : y ≠ e := by
    intro h
    have hl := r.label_reverse x
    rw [hxy,h,← he] at hl
    exact hbar (label x) hl.symm
  simp only [switch_apply,Equiv.swap_apply_of_ne_of_ne hyx hye]
  rw [← hxy,r.reverse_reverse,Equiv.swap_apply_left]

/-- Distinct input-matching/auxiliary-port pairs always give distinct outputs. -/
theorem switch_injective (x y : D) (hbar : ∀ t, bar t ≠ t) :
    Function.Injective (fun p : {r : Matching label bar // r x = y} ×
      {e : D // label x = label e} => p.1.val.switch x p.2.val p.2.property) := by
  rintro ⟨⟨r,hr⟩,⟨e,he⟩⟩ ⟨⟨s,hs⟩,⟨f,hf⟩⟩ h
  have hef : e = f := by
    simpa only [switch_recover r x y e he hr hbar,switch_recover s x y f hf hs hbar]
      using congrArg (fun r : Matching label bar => r y) h
  subst f
  have hrs : r = s := by
    simpa only [switch_switch] using congrArg (fun r : Matching label bar => r.switch x e he) h
  subst s
  rfl

/-- Prior prescriptions are undirected matching edges, counted once. -/
def Contains (r : Matching label bar) (C : Finset (Sym2 D)) : Prop :=
  ∀ a b, s(a,b) ∈ C → r a = b

omit [DecidableEq D] in
/-- A signed label chooses a unique orientation of each matching edge. -/
theorem edge_name_injective (r : Matching label bar) (x : D)
    (hbar : ∀ t, bar t ≠ t) :
    Function.Injective (fun e : {e : D // label e = label x} => s(e.val,r e.val)) := by
  rintro ⟨e,he⟩ ⟨f,hf⟩ h
  rcases Sym2.eq_iff.mp h with ⟨hef,_⟩ | ⟨hef,_⟩
  · exact Subtype.ext hef
  · have hh := congrArg label hef
    rw [r.label_reverse,he,hf] at hh
    exact False.elim (hbar (label x) hh.symm)

/-- Switching two edges disjoint from the prior prescriptions preserves them. -/
theorem switch_contains (r : Matching label bar) (C : Finset (Sym2 D))
    (hC : r.Contains C) (x e : D) (he : label x = label e)
    (hxC : s(x,r x) ∉ C) (heC : s(e,r e) ∉ C) : (r.switch x e he).Contains C := by
  intro a b hab
  have hr := hC a b hab
  have hax : a ≠ x := by intro h; subst a; exact hxC (hr ▸ hab)
  have hae : a ≠ e := by intro h; subst a; exact heC (hr ▸ hab)
  have hbx : b ≠ x := by
    intro h
    have hra : r x = a := by rw [← h,← hr,r.reverse_reverse]
    exact hxC (by simpa only [hra,h,Sym2.eq_swap] using hab)
  have hbe : b ≠ e := by
    intro h
    have hra : r e = a := by rw [← h,← hr,r.reverse_reverse]
    exact heC (by simpa only [hra,h,Sym2.eq_swap] using hab)
  simp only [switch_apply,Equiv.swap_apply_of_ne_of_ne hax hae,hr,
    Equiv.swap_apply_of_ne_of_ne hbx hbe]

variable [Fintype V] [Fintype D]

/-- All allowed transpositions for the distinguished port, omitting prior
edges and both radius-R endpoint balls. -/
def admissible (r : Matching label bar) (origin : D → V) (x : D)
    (R : ℕ) (C : Finset (Sym2 D)) : Finset {e : D // label e = label x} := by
  classical
  let Γ := r.graph origin
  let B := ball (graphNeighbors Γ.subdivision) (Sum.inr x) R ∪
    ball (graphNeighbors Γ.subdivision) (Sum.inr (r x)) R
  exact Finset.univ.filter fun e => s(e.val,r e.val) ∉ C ∧
    Sum.inr e.val ∉ B ∧ Sum.inr (r e.val) ∉ B

/-- The excluded prior set costs exactly one port per prior edge, not two. -/
theorem admissible_card (r : Matching label bar) (origin : D → V)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (x : D) (R : ℕ) (C : Finset (Sym2 D)) :
    Nat.card {e : D // label e = label x} - C.card - 4*d^(R+1) ≤
      (r.admissible origin x R C).card := by
  classical
  let X := {e : D // label e = label x}
  let P : Finset X := Finset.univ.filter fun e => s(e.val,r e.val) ∈ C
  have hP : P.card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun e : X => s(e.val,r e.val))
    · intro e he; exact (Finset.mem_filter.mp he).2
    · exact (r.edge_name_injective x hbar).injOn
  have hbound := BallCount.admissible_card (Equiv.refl X)
    (fun e : X => (Sum.inr e.val : V ⊕ D)) (fun e : X => (Sum.inr (r e.val) : V ⊕ D))
    (by intro a b h; exact Subtype.ext (Sum.inr.inj h))
    (by intro a b h; exact Subtype.ext (r.val.injective (Sum.inr.inj h)))
    (graphNeighbors (r.graph origin).subdivision) d h2
    (subdivision_degree (r.graph origin) d h2 hd) (Sum.inr x) (Sum.inr (r x)) R P
  have ht : Fintype.card X - P.card - 4*d^(R+1) ≤
      (r.admissible origin x R C).card := by
    convert hbound using 1
    congr 1
    ext e
    simp [admissible,P]
  rw [Nat.card_eq_fintype_card]
  exact (Nat.sub_le_sub_right (Nat.sub_le_sub_left hP _) _).trans ht

/-- The girth condition is preserved by each counted auxiliary port. -/
theorem admissible_preserves (r : Matching label bar) (origin : D → V)
    (x : D) (N : ℕ) (C : Finset (Sym2 D))
    (hC : r.Contains C) (hxC : s(x,r x) ∉ C)
    (hg : (N : ℕ∞) ≤ (r.graph origin).subdivision.egirth)
    (e : {e : D // label e = label x}) (he : e ∈ r.admissible origin x (2*N) C) :
    (r.switch x e.val e.property.symm).Contains C ∧
      (N : ℕ∞) ≤ ((r.switch x e.val e.property.symm).graph origin).subdivision.egirth := by
  classical
  have he' := Finset.mem_filter.mp he |>.2
  change s(e.val,r e.val) ∉ C ∧ _ at he'
  have hfar : ∀ a ∈ ({Sum.inr x,Sum.inr (r x)} : Set (V ⊕ D)),
      ∀ b ∈ ({Sum.inr e.val,Sum.inr (r e.val)} : Set (V ⊕ D)),
      ∀ p : (r.graph origin).subdivision.Walk a b, 2*N < p.length := by
    intro a ha b hb p
    apply far_of_not_mem_ball (r.graph origin).subdivision (2*N) _ p
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun h => he'.2.1 (Finset.mem_union_left _ h)
    · exact fun h => he'.2.2 (Finset.mem_union_left _ h)
    · exact fun h => he'.2.1 (Finset.mem_union_right _ h)
    · exact fun h => he'.2.2 (Finset.mem_union_right _ h)
  have far_ne {a b : V ⊕ D}
      (hf : ∀ p : (r.graph origin).subdivision.Walk a b, 2*N < p.length) : a ≠ b := by
    intro h
    subst b
    have hh := hf SimpleGraph.Walk.nil
    simp at hh
  have hxe : x ≠ e.val := by
    intro h
    exact far_ne (hfar (.inr x) (by simp) (.inr e.val) (by simp)) (congrArg Sum.inr h)
  have hxr : x ≠ r e.val := by
    intro h
    exact far_ne (hfar (.inr x) (by simp) (.inr (r e.val)) (by simp)) (congrArg Sum.inr h)
  refine ⟨r.switch_contains C hC x e.val e.property.symm hxC he'.1,?_⟩
  rw [graph_switch,subdivision_switch (r.graph origin) x e.val hxe hxr]
  exact girth_switch N hg rfl hfar

/-- The exact finite space conditioned on girth and prior prescriptions. -/
def conditioned (origin : D → V) (N : ℕ) (C : Finset (Sym2 D)) :
    Finset (Matching label bar) := by
  classical
  exact Finset.univ.filter fun r => r.Contains C ∧
    (N : ℕ∞) ≤ (r.graph origin).subdivision.egirth

/-- Direct double counting on the whole tuple space, with all other matchings
retained in the output. No independence after conditioning is used. -/
theorem conditioned_count (origin : D → V) (N : ℕ) (C : Finset (Sym2 D))
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (x y : D) (hxy : s(x,y) ∉ C) :
    ((conditioned (label := label) (bar := bar) origin N C).filter (fun r => r x = y)).card *
      (Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1)) ≤
      (conditioned (label := label) (bar := bar) origin N C).card := by
  classical
  let Ω := conditioned (label := label) (bar := bar) origin N C
  let r₀ := Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1)
  let F := {r : Matching label bar // r ∈ Ω ∧ r x = y}
  let S := (r : F) × {e : {e : D // label e = label x} //
    e ∈ r.val.admissible origin x (2*N) C}
  have hm (r : F) : r.val.Contains C ∧
      (N : ℕ∞) ≤ (r.val.graph origin).subdivision.egirth := by
    have h := r.property.1
    simpa only [Ω,conditioned,Finset.mem_filter,Finset.mem_univ,true_and] using h
  let out : S → {r : Matching label bar // r ∈ Ω} := fun p =>
    ⟨p.1.val.switch x p.2.val.val p.2.val.property.symm,by
      have hh := p.1.val.admissible_preserves origin x N C (hm p.1).1
        (by simpa only [p.1.property.2] using hxy) (hm p.1).2 p.2.val p.2.property
      simpa only [Ω,conditioned,Finset.mem_filter,Finset.mem_univ,true_and] using hh⟩
  have hout : Function.Injective out := by
    intro p q h
    have hs : p.1.val.switch x p.2.val.val p.2.val.property.symm =
        q.1.val.switch x q.2.val.val q.2.val.property.symm := congrArg Subtype.val h
    have hi := switch_injective (label := label) (bar := bar) x y hbar
      (a₁ := (⟨p.1.val,p.1.property.2⟩,⟨p.2.val.val,p.2.val.property.symm⟩))
      (a₂ := (⟨q.1.val,q.1.property.2⟩,⟨q.2.val.val,q.2.val.property.symm⟩)) hs
    have hr : p.1 = q.1 := Subtype.ext (congrArg (fun z => z.1.val) hi)
    cases p with
    | mk r e =>
      cases q with
      | mk s f =>
        dsimp at hr
        subst s
        have hef : e = f := Subtype.ext (Subtype.ext (congrArg (fun z => z.2.val) hi))
        subst f
        rfl
  have hc := Fintype.card_le_of_injective out hout
  have hsource : Fintype.card S = ∑ r : F, (r.val.admissible origin x (2*N) C).card := by
    simp only [S,Fintype.card_sigma,Fintype.card_coe]
  have htarget : Fintype.card {r : Matching label bar // r ∈ Ω} = Ω.card := Fintype.card_coe Ω
  have hF : Fintype.card F = (Ω.filter (fun r => r x = y)).card := by
    change Fintype.card {r : Matching label bar // r ∈ Ω ∧ r x = y} = _
    rw [Fintype.card_subtype]
    congr 1
    ext r
    simp
  have hsum : Fintype.card F * r₀ ≤ ∑ r : F, (r.val.admissible origin x (2*N) C).card := by
    calc
      Fintype.card F * r₀ = ∑ _r : F, r₀ := by simp
      _ ≤ ∑ r : F, (r.val.admissible origin x (2*N) C).card :=
        Finset.sum_le_sum fun r _ => r.val.admissible_card origin hbar d h2 hd x (2*N) C
  rw [hsource,htarget] at hc
  rw [hF] at hsum
  exact hsum.trans hc

omit [Fintype D] in
/-- Adding one undirected prescription is exactly one matching-coordinate
condition; the reverse orientation is automatic, not an extra constraint. -/
theorem contains_insert (r : Matching label bar) (C : Finset (Sym2 D)) (x y : D) :
    r.Contains (insert s(x,y) C) ↔ r.Contains C ∧ r x = y := by
  classical
  constructor
  · intro h
    exact ⟨fun a b hab => h a b (Finset.mem_insert_of_mem hab),h x y (by simp)⟩
  · rintro ⟨hC,hxy⟩ a b hab
    rcases Finset.mem_insert.mp hab with h | h
    · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hxy
      · rw [← hxy,r.reverse_reverse]
    · exact hC a b h

omit [Fintype V] in
theorem conditioned_insert (origin : D → V) (N : ℕ) (C : Finset (Sym2 D))
    (x y : D) :
    conditioned (label := label) (bar := bar) origin N (insert s(x,y) C) =
      (conditioned (label := label) (bar := bar) origin N C).filter (fun r => r x = y) := by
  classical
  ext r
  simp only [conditioned,Finset.mem_filter,Finset.mem_univ,true_and,contains_insert]
  tauto

/-- The simultaneous-prescription bound obtained by successive conditioning.
No independence is asserted, even for prescriptions on distinct labels. -/
theorem prescriptions_count (origin : D → V) (N : ℕ)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (R : ℕ) (C : Finset (Sym2 D))
    (hR : ∀ x, R + C.card + 4*d^(2*N+1) ≤ Nat.card {e : D // label e = label x}) :
    (conditioned (label := label) (bar := bar) origin N C).card * R^C.card ≤
      (conditioned (label := label) (bar := bar) origin N ∅).card := by
  classical
  induction C using Finset.induction with
  | empty => simp
  | @insert e C he ih =>
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hR' : ∀ z, R + C.card + 4*d^(2*N+1) ≤
          Nat.card {e : D // label e = label z} := by
        intro z
        have hh := hR z
        rw [Finset.card_insert_of_notMem he] at hh
        omega
      have hstep := conditioned_count (label := label) (bar := bar)
        origin N C hbar d h2 hd x y he
      have hsmall : R ≤ Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1) := by
        have := hR' x
        omega
      have hstep' : (conditioned (label := label) (bar := bar) origin N (insert s(x,y) C)).card * R ≤
          (conditioned (label := label) (bar := bar) origin N C).card := by
        rw [conditioned_insert]
        exact (Nat.mul_le_mul_left _ hsmall).trans hstep
      rw [Finset.card_insert_of_notMem he,pow_succ,← mul_assoc,mul_right_comm]
      exact (Nat.mul_le_mul_right _ hstep').trans (ih hR')

/-- The uniform one-prescription bound for the actual girth-conditioned model. -/
theorem conditioned_probability (origin : D → V) (N : ℕ) (C : Finset (Sym2 D))
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (x y : D) (hxy : s(x,y) ∉ C)
    (hΩ : (conditioned (label := label) (bar := bar) origin N C).Nonempty)
    (hr : 0 < Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1)) :
    (((conditioned (label := label) (bar := bar) origin N C).filter (fun r => r x = y)).card : ℝ) /
        (conditioned (label := label) (bar := bar) origin N C).card ≤
      1 / (Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1) : ℕ) := by
  have hc := conditioned_count (label := label) (bar := bar) origin N C hbar d h2 hd x y hxy
  have hc' : (((conditioned (label := label) (bar := bar) origin N C).filter
      (fun r => r x = y)).card : ℝ) *
      (Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1) : ℕ) ≤
      (conditioned (label := label) (bar := bar) origin N C).card := by exact_mod_cast hc
  have hΩ' : (0 : ℝ) < (conditioned (label := label) (bar := bar) origin N C).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hΩ)
  have hr' : (0 : ℝ) < (Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1) : ℕ) :=
    Nat.cast_pos.mpr hr
  apply (div_le_iff₀ hΩ').mpr
  rw [div_mul_eq_mul_div,one_mul]
  exact (le_div_iff₀ hr').mpr hc'

end Matching
end TorsionFreeZeroDivisors.ConditionedMatchings

end

end OAI
