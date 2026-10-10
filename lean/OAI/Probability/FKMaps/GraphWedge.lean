import OAI.Probability.FKMaps.MapCycles

namespace OAI

noncomputable section
open scoped ENNReal
namespace FKCRT.GraphWedge
variable {A B V : Type*} (G : SimpleGraph A) (K : SimpleGraph B) (H : SimpleGraph V)

/-- Each original edge belongs to exactly one block; a collapsed loop may
have zero cost in either retraction. This local statement implies the full
global, all-edge metric lower bound. -/
lemma retraction_pair_edist_le (r : V→A) (s : V→B)
    (h : ∀ {u v},H.Adj u v → G.edist (r u) (r v)+K.edist (s u) (s v) ≤ 1)
    (u v : V) : G.edist (r u) (r v)+K.edist (s u) (s v) ≤ H.edist u v := by
  unfold SimpleGraph.edist
  apply le_iInf
  intro w
  change G.edist (r u) (r v)+K.edist (s u) (s v) ≤ (w.length:ℕ∞)
  induction w with
  | nil => simp
  | @cons u x v hadj w ih =>
    calc
      G.edist (r u) (r v)+K.edist (s u) (s v) ≤
          (G.edist (r u) (r x)+G.edist (r x) (r v))+
          (K.edist (s u) (s x)+K.edist (s x) (s v)) :=
        add_le_add (G.edist_triangle) (K.edist_triangle)
      _=(G.edist (r u) (r x)+K.edist (s u) (s x))+
          (G.edist (r x) (r v)+K.edist (s x) (s v)) := by ac_rfl
      _≤1+(w.length:ℕ∞) := add_le_add (h hadj) ih
      _=((SimpleGraph.Walk.cons hadj w).length:ℕ∞) := by simp [add_comm]

lemma hom_edist_le {A V : Type*} {G : SimpleGraph A} {H : SimpleGraph V}
    (i : G→g H) (x y : A) : H.edist (i x) (i y) ≤ G.edist x y := by
  unfold SimpleGraph.edist
  apply le_iInf
  intro w
  change H.edist (i x) (i y) ≤ (w.length:ℕ∞)
  simpa only [SimpleGraph.Walk.length_map] using (w.map i).edist_le

/-- Combinatorial data of an actual one-vertex union. Distances are not
part of these hypotheses; they are derived from the adjacency data below. -/
structure Data where
  left : G→g H
  right : K→g H
  poleLeft : A
  poleRight : B
  shared : left poleLeft=right poleRight
  retractLeft : V→A
  retractRight : V→B
  left_left : ∀ x,retractLeft (left x)=x
  right_right : ∀ y,retractRight (right y)=y
  right_left : ∀ x,retractRight (left x)=poleRight
  left_right : ∀ y,retractLeft (right y)=poleLeft
  edge : ∀ {u v},H.Adj u v →
    (G.Adj (retractLeft u) (retractLeft v) ∧ retractRight u=retractRight v) ∨
    (retractLeft u=retractLeft v ∧ K.Adj (retractRight u) (retractRight v))

namespace Data
variable {G K H}

lemma cost_le (D : Data G K H) {u v : V} (h : H.Adj u v) :
    G.edist (D.retractLeft u) (D.retractLeft v)+
      K.edist (D.retractRight u) (D.retractRight v) ≤ 1 := by
  rcases D.edge h with ⟨h,h'⟩|⟨h',h⟩
  · rw [h',SimpleGraph.edist_self,add_zero,SimpleGraph.edist_eq_one_iff_adj.mpr h]
  · rw [h',SimpleGraph.edist_self,zero_add,SimpleGraph.edist_eq_one_iff_adj.mpr h]

/-- Attachments cannot shorten distances within any block. -/
theorem edist_left (D : Data G K H) (x y : A) : H.edist (D.left x) (D.left y)=G.edist x y := by
  apply le_antisymm (hom_edist_le D.left x y)
  have h := retraction_pair_edist_le G K H D.retractLeft D.retractRight D.cost_le (D.left x) (D.left y)
  simpa only [D.left_left,D.right_left,SimpleGraph.edist_self,add_zero] using h

theorem edist_right (D : Data G K H) (x y : B) : H.edist (D.right x) (D.right y)=K.edist x y := by
  apply le_antisymm (hom_edist_le D.right x y)
  have h := retraction_pair_edist_le G K H D.retractLeft D.retractRight D.cost_le (D.right x) (D.right y)
  simpa only [D.right_right,D.left_right,SimpleGraph.edist_self,zero_add] using h

/-- Distances between blocks add exactly through their shared pole. -/
theorem edist_cross (D : Data G K H) (x : A) (y : B) :
    H.edist (D.left x) (D.right y)=G.edist x D.poleLeft+K.edist D.poleRight y := by
  apply le_antisymm
  · calc
      H.edist (D.left x) (D.right y) ≤
        H.edist (D.left x) (D.left D.poleLeft)+H.edist (D.left D.poleLeft) (D.right y) :=
          H.edist_triangle
      _=_ := by rw [D.edist_left,D.shared,D.edist_right]
  · have h := retraction_pair_edist_le G K H D.retractLeft D.retractRight D.cost_le (D.left x) (D.right y)
    simpa only [D.left_left,D.right_right,D.right_left,D.left_right] using h

end Data
end FKCRT.GraphWedge
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
open MapCycles
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

def sideSetoid (p : Perm α) (S : Set α) : Setoid S where
  r x y := p.SameCycle x.val y.val
  iseqv := ⟨fun x => SameCycle.refl p x.val,fun h => h.symm,fun h h' => h.trans h'⟩

abbrev Side (p : Perm α) (S : Set α) := Quotient (sideSetoid p S)
def sideMk (p : Perm α) (S : Set α) (d : α) (hd : d∈S) : Side p S := Quotient.mk _ ⟨d,hd⟩
abbrev Vertex (p : Perm α) := Quotient (SameCycle.setoid p)
def vertex (p : Perm α) (d : α) : Vertex p := Quotient.mk _ d

def dartGraph (e p : Perm α) : SimpleGraph (Vertex p) :=
  SimpleGraph.fromRel (fun v w => ∃ d,vertex p d=v ∧ vertex p (e d)=w)

def sideGraph (e p : Perm α) (S : Set α) (he : ∀ d,e d∈S ↔ d∈S) : SimpleGraph (Side p S) :=
  SimpleGraph.fromRel (fun v w => ∃ d,∃ hd : d∈S,sideMk p S d hd=v ∧ sideMk p S (e d) ((he d).mpr hd)=w)

variable {p e : Perm α} {S : Set α} {a b : α}
variable (hp : ∀ d,p d∈S ↔ d∈S) (ha : a∈S) (hb : b∉S)

/- The maps below operate on the actual rotation-cycle quotients. -/
def inclusion : Side p S→Vertex (swap a b*p) := Quotient.lift
  (fun d => vertex (swap a b*p) d.val)
  (fun _ _ h => Quotient.sound (sameCycle_le_vertexJoin p (not_sameCycle_partition hp ha hb) h))

lemma inclusion_mk (d : α) (hd : d∈S) : inclusion hp ha hb (sideMk p S d hd)=vertex (swap a b*p) d := rfl

lemma inclusion_injective : Function.Injective (inclusion hp ha hb) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      exact (vertexJoin_inside_iff hp ha hb x.property y.property).mp (Quotient.exact h)

def retractD (d : α) : Side p S :=
  if hd : d∈S then sideMk p S d hd else sideMk p S a ha

include hp hb in
lemma retractD_eq_of_join {x y : α} (hxy : (swap a b*p).SameCycle x y) :
    retractD (p := p) ha x=retractD (p := p) ha y := by
  by_cases hx : x∈S
  · by_cases hy : y∈S
    · simp only [retractD,dite_eq_left hx,dite_eq_left hy]
      exact Quotient.sound ((vertexJoin_inside_iff hp ha hb hx hy).mp hxy)
    · simp only [retractD,dite_eq_left hx,dite_eq_right hy]
      exact Quotient.sound ((vertexJoin_cross_iff hp ha hb hx hy).mp hxy).1
  · by_cases hy : y∈S
    · simp only [retractD,dite_eq_right hx,dite_eq_left hy]
      exact (Quotient.sound ((vertexJoin_cross_iff hp ha hb hy hx).mp hxy.symm).1).symm
    · simp only [retractD,dite_eq_right hx,dite_eq_right hy]

def retract : Vertex (swap a b*p)→Side p S :=
  Quotient.lift (retractD (p := p) ha) (fun _ _ h => retractD_eq_of_join hp ha hb h)

lemma retract_vertex (d : α) : retract hp ha hb (vertex (swap a b*p) d)=retractD (p := p) ha d := rfl

lemma retract_inclusion (x : Side p S) : retract hp ha hb (inclusion hp ha hb x)=x := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_left d.property

def flipInclusion : Side p Sᶜ →Vertex (swap a b*p) := Quotient.lift
  (fun d => vertex (swap a b*p) d.val)
  (fun _ _ h => Quotient.sound (sameCycle_le_vertexJoin p (not_sameCycle_partition hp ha hb) h))

lemma flipInclusion_injective : Function.Injective (flipInclusion hp ha hb) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      exact (vertexJoin_outside_iff hp ha hb x.property y.property).mp (Quotient.exact h)

def flipRetractD (d : α) : Side p Sᶜ :=
  if hd : d∈Sᶜ then sideMk p Sᶜ d hd else sideMk p Sᶜ b hb

include hp ha in
lemma flipRetractD_eq_of_join {x y : α} (hxy : (swap a b*p).SameCycle x y) :
    flipRetractD (p := p) hb x=flipRetractD (p := p) hb y := by
  have h := retractD_eq_of_join (S := Sᶜ) (p := p)
    (fun d => not_congr (hp d)) hb (by simpa using ha)
    (show (swap b a*p).SameCycle x y by simpa only [swap_comm b a] using hxy)
  by_cases hx : x∈Sᶜ <;> by_cases hy : y∈Sᶜ <;>
    simp_all only [retractD,flipRetractD,dite_eq_left]

def flipRetract : Vertex (swap a b*p)→Side p Sᶜ :=
  Quotient.lift (flipRetractD (p := p) hb) (fun _ _ h => flipRetractD_eq_of_join hp ha hb h)

lemma flipRetract_vertex (d : α) : flipRetract hp ha hb (vertex (swap a b*p) d)=flipRetractD (p := p) hb d := rfl

lemma flipRetract_flipInclusion (x : Side p Sᶜ) : flipRetract hp ha hb (flipInclusion hp ha hb x)=x := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_left d.property

lemma flipRetract_inclusion (x : Side p S) :
    flipRetract hp ha hb (inclusion hp ha hb x)=sideMk p Sᶜ b hb := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_right (by simp [d.property])

lemma retract_flipInclusion (x : Side p Sᶜ) :
    retract hp ha hb (flipInclusion hp ha hb x)=sideMk p S a ha := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_right d.property

lemma inclusion_poles : inclusion hp ha hb (sideMk p S a ha)=flipInclusion hp ha hb (sideMk p Sᶜ b hb) :=
  Quotient.sound (sameCycle_swap_of_not_sameCycle p (not_sameCycle_partition hp ha hb))

variable (he : ∀ d,e d∈S ↔ d∈S)

def inclusionHom : sideGraph e p S he →g dartGraph e (swap a b*p) where
  toFun := inclusion hp ha hb
  map_rel' := by
    intro x y hxy
    refine ⟨fun h => hxy.1 (inclusion_injective hp ha hb h),?_⟩
    rcases hxy.2 with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
    · exact Or.inl ⟨d,by rw [← hx];rfl,by rw [← hy];rfl⟩
    · exact Or.inr ⟨d,by rw [← hy];rfl,by rw [← hx];rfl⟩

def flipInclusionHom : sideGraph e p Sᶜ (fun d => not_congr (he d)) →g dartGraph e (swap a b*p) where
  toFun := flipInclusion hp ha hb
  map_rel' := by
    intro x y hxy
    refine ⟨fun h => hxy.1 (flipInclusion_injective hp ha hb h),?_⟩
    rcases hxy.2 with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
    · exact Or.inl ⟨d,by rw [← hx];rfl,by rw [← hy];rfl⟩
    · exact Or.inr ⟨d,by rw [← hy];rfl,by rw [← hx];rfl⟩

lemma retraction_edge {x y : Vertex (swap a b*p)} (hxy : (dartGraph e (swap a b*p)).Adj x y) :
    ((sideGraph e p S he).Adj (retract hp ha hb x) (retract hp ha hb y) ∧
      flipRetract hp ha hb x=flipRetract hp ha hb y) ∨
    (retract hp ha hb x=retract hp ha hb y ∧
      (sideGraph e p Sᶜ (fun d => not_congr (he d))).Adj (flipRetract hp ha hb x) (flipRetract hp ha hb y)) := by
  have forward (d : α) (hdiff : vertex (swap a b*p) d≠vertex (swap a b*p) (e d)) :
      ((sideGraph e p S he).Adj (retractD (p := p) ha d) (retractD (p := p) ha (e d)) ∧
        flipRetractD (p := p) hb d=flipRetractD (p := p) hb (e d)) ∨
      (retractD (p := p) ha d=retractD (p := p) ha (e d) ∧
        (sideGraph e p Sᶜ (fun d => not_congr (he d))).Adj (flipRetractD (p := p) hb d) (flipRetractD (p := p) hb (e d))) := by
    by_cases hd : d∈S
    · have he' := (he d).mpr hd
      left
      simp only [retractD,dite_eq_left hd,dite_eq_left he']
      refine ⟨⟨?_,Or.inl ⟨d,hd,rfl,rfl⟩⟩,?_⟩
      · intro h
        exact hdiff (congrArg (inclusion hp ha hb) h)
      · simp [flipRetractD,hd,he']
    · have he' : e d∉S := fun h => hd ((he d).mp h)
      right
      simp only [retractD,dite_eq_right hd,dite_eq_right he',flipRetractD,Set.mem_compl_iff,dite_eq_left hd,dite_eq_left he']
      refine ⟨trivial,⟨?_,Or.inl ⟨d,hd,rfl,rfl⟩⟩⟩
      intro h
      exact hdiff (congrArg (flipInclusion hp ha hb) h)
  rcases hxy.2 with ⟨d,rfl,rfl⟩|⟨d,rfl,rfl⟩
  · exact forward d hxy.1
  · rcases forward d hxy.1.symm with ⟨h,h'⟩|⟨h',h⟩
    · exact Or.inl ⟨h.symm,h'.symm⟩
    · exact Or.inr ⟨h'.symm,h.symm⟩

/-- Actual permutation-map insertion satisfies graph-wedge adjacency data.
No metric or distance assertion is supplied as an assumption. -/
def data : GraphWedge.Data (sideGraph e p S he)
    (sideGraph e p Sᶜ (fun d => not_congr (he d))) (dartGraph e (swap a b*p)) where
  left := inclusionHom hp ha hb he
  right := flipInclusionHom hp ha hb he
  poleLeft := sideMk p S a ha
  poleRight := sideMk p Sᶜ b hb
  shared := inclusion_poles hp ha hb
  retractLeft := retract hp ha hb
  retractRight := flipRetract hp ha hb
  left_left := retract_inclusion hp ha hb
  right_right := flipRetract_flipInclusion hp ha hb
  right_left := flipRetract_inclusion hp ha hb
  left_right := retract_flipInclusion hp ha hb
  edge := retraction_edge hp ha hb he

end FKCRT.PermutationWedge
end


noncomputable section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT.Chords
variable {N : ℕ}

abbrev Opener (a : Perm (Fin N)) := { i : Fin N // i < a i }

def Cross (a : Perm (Fin N)) (x y : Opener a) : Prop :=
  (x.val < y.val ∧ y.val < a x.val ∧ a x.val < a y.val) ∨
  (y.val < x.val ∧ x.val < a y.val ∧ a y.val < a x.val)

def graph (a : Perm (Fin N)) : SimpleGraph (Opener a) where
  Adj := Cross a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by intro x; simp [Cross]⟩

def Inside (a : Perm (Fin N)) (f x : Opener a) : Prop :=
  f.val < x.val ∧ a x.val < a f.val

lemma opener_endpoints_ne (a : Perm (Fin N)) (ha : Function.Involutive a)
    (x y : Opener a) (hxy : x≠y) :
    x.val≠y.val ∧ x.val≠a y.val ∧ a x.val≠y.val ∧ a x.val≠a y.val := by
  have h1 : x.val≠y.val := fun h => hxy (Subtype.ext h)
  have h2 : x.val≠a y.val := by
    intro h
    have hx := x.property
    have hy := y.property
    rw [h,ha] at hx
    exact (not_lt_of_ge hy.le) hx
  have h3 : a x.val≠y.val := by
    intro h
    have hh : x.val=a y.val := by rw [← h,ha]
    exact h2 hh
  exact ⟨h1,h2,h3,fun h => h1 (a.injective h)⟩

/-- A chord which crosses a chord strictly inside a third chord must either
be inside the third chord or cross it. Endpoint disjointness is explicit. -/
lemma inside_propagates (a : Perm (Fin N)) (ha : Function.Involutive a)
    (f x y : Opener a) (hyf : y≠f) (hc : Cross a x y)
    (hn : ¬Cross a f y) (hx : Inside a f x) : Inside a f y := by
  obtain ⟨h1,h2,h3,h4⟩ := opener_endpoints_ne a ha y f hyf
  have hp := y.property
  unfold Cross at hc hn
  unfold Inside at hx ⊢
  have hv1 := Fin.val_ne_of_ne h1
  have hv2 := Fin.val_ne_of_ne h2
  have hv3 := Fin.val_ne_of_ne h3
  have hv4 := Fin.val_ne_of_ne h4
  simp only [Fin.lt_def] at hc hn hx hp ⊢
  omega

/-- A chord outside the root crossing component has no root-component
endpoint in its interior. This is the algebraic corner-separation lemma:
it requires neither a Jordan-curve assumption nor a stipulated block law. -/
theorem component_gap (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r f : Opener a) (hroot : r.val≤f.val) (hf : ¬(graph a).Reachable r f)
    (x : Opener a) (hx : (graph a).Reachable r x) :
    ¬(f.val < x.val ∧ x.val < a f.val) ∧
      ¬(f.val < a x.val ∧ a x.val < a f.val) := by
  have hne (y : Opener a) (hy : (graph a).Reachable r y) : y≠f := by
    rintro rfl
    exact hf hy
  have hno (y : Opener a) (hy : (graph a).Reachable r y) : ¬Cross a f y := by
    intro h
    exact hf (hy.trans (show (graph a).Adj y f from Or.symm h).reachable)
  have hinside : ¬Inside a f x := by
    have hp := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hx
    induction hp with
    | refl => exact fun h => not_lt_of_ge hroot h.1
    | @tail y z hp hadj ih =>
      intro hz
      have hy : (graph a).Reachable r y := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hp
      exact ih hy (inside_propagates a ha f z y (hne y hy) (Or.symm hadj) (hno y hy) hz)
  have hnc := hno x hx
  obtain ⟨h1,h2,h3,h4⟩ := opener_endpoints_ne a ha x f (hne x hx)
  have hp := x.property
  have hv1 := Fin.val_ne_of_ne h1
  have hv2 := Fin.val_ne_of_ne h2
  have hv3 := Fin.val_ne_of_ne h3
  have hv4 := Fin.val_ne_of_ne h4
  unfold Cross at hnc
  unfold Inside at hinside
  simp only [Fin.lt_def] at hnc hinside hp ⊢
  omega

/-- Actual endpoint set of the root crossing component. -/
def componentDarts (a : Perm (Fin N)) (r : Opener a) : Finset (Fin N) :=
  Finset.univ.filter (fun d => ∃ x : Opener a, (graph a).Reachable r x ∧ (d=x.val ∨ d=a x.val))

lemma mem_componentDarts (a : Perm (Fin N)) (r : Opener a) (d : Fin N) :
    d∈componentDarts a r ↔ ∃ x : Opener a,(graph a).Reachable r x ∧ (d=x.val ∨ d=a x.val) := by
  classical
  simp [componentDarts]

lemma external_not_component (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r f : Opener a) (hf : ¬(graph a).Reachable r f) :
    f.val∉componentDarts a r ∧ a f.val∉componentDarts a r := by
  have hne (x : Opener a) (hx : (graph a).Reachable r x) : f≠x := by
    rintro rfl
    exact hf hx
  constructor
  · intro h
    obtain ⟨x,hx,he|he⟩ := (mem_componentDarts a r _).mp h
    · exact (opener_endpoints_ne a ha f x (hne x hx)).1 he
    · exact (opener_endpoints_ne a ha f x (hne x hx)).2.1 he
  · intro h
    obtain ⟨x,hx,he|he⟩ := (mem_componentDarts a r _).mp h
    · exact (opener_endpoints_ne a ha f x (hne x hx)).2.2.1 he
    · exact (opener_endpoints_ne a ha f x (hne x hx)).2.2.2 he

/-- The gap index is determined solely by the ordered root-component darts.
The two ends of every exterior matched pair have the same gap index. -/
def gapIndex (a : Perm (Fin N)) (r : Opener a) (d : Fin N) : ℕ :=
  ((componentDarts a r).filter (·<d)).card

theorem exterior_same_gap (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r f : Opener a) (hroot : r.val≤f.val) (hf : ¬(graph a).Reachable r f) :
    gapIndex a r f.val=gapIndex a r (a f.val) := by
  have hn := external_not_component a ha r f hf
  unfold gapIndex
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1,h.2.trans f.property⟩
  · rintro ⟨hd,hlt⟩
    refine ⟨hd,?_⟩
    have hdne : d≠f.val := fun h => hn.1 (h ▸ hd)
    by_contra h
    have hfd : f.val < d := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hdne)
    obtain ⟨x,hx,rfl|rfl⟩ := (mem_componentDarts a r d).mp hd
    · exact (component_gap a ha r f hroot hf x hx).1 ⟨hfd,hlt⟩
    · exact (component_gap a ha r f hroot hf x hx).2 ⟨hfd,hlt⟩

end FKCRT.Chords
end

end OAI
