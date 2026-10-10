import OAI.GroupTheory.Hyperbolic.Links

namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem rectangle_turn_large (i : d.Label) (u u' v v' : Fin r)
    (hu : u ≠ u') (hv : v ≠ v')
    (a b : (d.presentation hr).OrientedEdge)
    (ha : a ∈ [(d.presentation hr).orientedX i u v,
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u' v),
      (d.presentation hr).orientedX i u' v',
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u v')])
    (hb : b ∈ [(d.presentation hr).orientedX i u v,
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u' v),
      (d.presentation hr).orientedX i u' v',
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u v')])
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge b) =
      (d.presentation hr).edgeTarget a)
    (p : (d.allLink hr).Walk (d.linkDirection hr ((d.presentation hr).flipEdge b))
      (d.linkDirection hr a)) (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr a)) * p.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl
  all_goals rcases hb with rfl|rfl|rfl|rfl
  all_goals simp only [BlockPresentation.orientedX,BlockPresentation.flipEdge,
    BlockPresentation.edgeTarget,Bool.not_true,Bool.not_false] at ht
  all_goals cases ht
  all_goals
    first
    | exact d.x_turn_large hr i u v u' v true false rfl
        (by intro he; exact hu (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u v u v' true false rfl
        (by intro he; exact hv (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v u v false true rfl
        (by intro he; exact hu.symm (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u' v u' v' false true rfl
        (by intro he; exact hv (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v' u' v true false rfl
        (by intro he; exact hv.symm (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v' u v' true false rfl
        (by intro he; exact hu.symm (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u v' u v false true rfl
        (by intro he; exact hv.symm (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u v' u' v' false true rfl
        (by intro he; exact hu (congrArg Prod.fst he)) p hp

/-- Every actual rectangular word in the fixed presentation is nontrivial:
nullhomotopy gives a minimal labelled planar filling, whose reduced link sectors
contradict its Euler-characteristic-one angular identity. -/
theorem rectangular_nontriviality : d.RectangularNontriviality hr := by
  intro i u u' v v' hu hv he
  have hf := (d.presentation hr).rectangle_fillable_of_eq_one i u u' v v' he
  obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
  have hn : D.boundary ≠ [] := by
    intro hz
    have hh := D.boundary_word
    rw [hz] at hh
    cases hh
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
  apply (d.concreteRibbon hr D b hb).not_all_turns_geodesic
    (d.allLink hr) (d.dartDirection hr D)
    (d.ribbon_adj hr D b hb) (d.ribbon_reduced hr D b hb hD)
    (d.ribbon_closed hr D b hb)
  intro a ha p hp
  have ha' : a.val ∈ D.boundary := (d.ribbon_outer_iff hr D b hb a).mp ha
  have hb' : D.next a.val ∈ D.boundary := (D.boundary_cycle.mem_iff a.val).mpr ha'
  have hal : D.label a.val ∈ _ := List.mem_map.mpr ⟨a.val,ha',rfl⟩
  have hbl : D.label (D.next a.val) ∈ _ := List.mem_map.mpr ⟨D.next a.val,hb',rfl⟩
  rw [D.boundary_word] at hal hbl
  rw [d.ribbon_color hr D b hb a]
  have ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (D.label (D.next a.val))) =
      (d.presentation hr).edgeTarget (D.label a.val) := by
    rw [← D.reverse_label]
    exact D.color_next a.val
  have hs := d.ribbon_direction_step hr D b hb a
  let p' := p.copy hs rfl
  have hp' : ReducedWalk p' := by
    intro j hj
    simpa only [p',SimpleGraph.Walk.getVert_copy] using
      hp j (by simpa only [p',SimpleGraph.Walk.length_copy] using hj)
  have hh := d.rectangle_turn_large hr i u u' v v' hu hv _ _ hal hbl ht p' hp'
  have hlen : p'.length = p.length := SimpleGraph.Walk.length_copy p hs rfl
  change 5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (D.label a.val))) * p'.length at hh
  rw [hlen] at hh
  exact hh

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

theorem ribbon_closed_strict (a : D.ActiveDart)
    (p : (d.allLink hr).Walk (d.dartDirection hr D a) (d.dartDirection hr D a))
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight ((d.concreteRibbon hr D b hb).color
      (cl (d.concreteRibbon hr D b hb).vertexPerm a)) * p.length := by
  rw [d.ribbon_color hr D b hb a]
  exact d.allLink_closed hr _ p hn hp

theorem ribbon_boundary_length : (d.concreteRibbon hr D b hb).counts.boundaryLength = w.length := by
  let R := d.concreteRibbon hr D b hb
  change (∑ v : R.Vertex, R.visits v) = _
  rw [R.visits_sum]
  let e : {a : R.Dart // cl R.face a = R.outer} ≃ {a : D.Dart // a ∈ D.boundary} := {
    toFun a := ⟨a.val.val,(d.ribbon_outer_iff hr D b hb a.val).mp a.property⟩
    invFun a := ⟨⟨a.val,D.active_of_mem a.property⟩,
      (d.ribbon_outer_iff hr D b hb _).mpr a.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_subtype]
  have hset : Finset.univ.filter (fun a => a ∈ D.boundary) = D.boundary.toFinset := by
    ext a; simp
  rw [hset,List.toFinset_card_of_nodup D.boundary_cycle.1]
  exact (List.length_map D.label).symm.trans (congrArg List.length D.boundary_word)

include b hb in
theorem reduced_linear_active_bound (hD : IsEmpty D.Dipole) :
    D.activeCount + 36 ≤ 19*w.length := by
  let R := d.concreteRibbon hr D b hb
  have hstrict := R.interior_angle_lower (d.allLink hr) (d.dartDirection hr D)
    (d.ribbon_adj hr D b hb) (d.ribbon_reduced hr D b hb hD) 12
    (d.ribbon_closed_strict hr D b hb)
  have hface := R.counts.linear_face_bound hstrict
  have hlen := d.ribbon_boundary_length hr D b hb
  change R.counts.boundaryLength = w.length at hlen
  rw [hlen] at hface
  have hdart : Fintype.card R.Dart = D.activeCount := by
    change Fintype.card D.ActiveDart = _
    exact Fintype.card_subtype _
  have he := R.exterior_count
  rw [← R.dart_card,hdart] at he
  change R.counts.boundaryLength + 3*R.counts.faces = D.activeCount at he
  rw [hlen] at he
  omega

/-- An actual finite nullhomotopy has a genuine planar filling of linearly
bounded size, not an assumed Dehn-function estimate. This estimate is a necessary
bridge to the uniform Cayley thinness argument below. -/
theorem exists_linear_filling (hf : Fillable (d.presentation hr).flipEdge
    (d.presentation hr).edgeTarget (d.presentation hr).TriangleFace w) :
    ∃ D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace w, D.activeCount ≤ 19*w.length := by
  by_cases hw : w = []
  · subst w
    refine ⟨TriangleFilling.empty,?_⟩
    unfold TriangleFilling.activeCount
    apply (Finset.card_le_univ _).trans
    change 0 ≤ _
    exact Nat.zero_le _
  · obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
    have hn : D.boundary ≠ [] := by
      intro he
      apply hw
      rw [← D.boundary_word,he,List.map_nil]
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
    exact ⟨D,by have hh := d.reduced_linear_active_bound hr D b hb hD; omega⟩

/-- The fixed presentation's non-residual-finiteness is now unconditional in
its finite incidence data; no rectangular nontriviality premise remains. -/
theorem actual_presentation_not_residuallyFinite (hq : r < q) (hq200 : 200 ≤ q) :
    ¬ Group.ResiduallyFinite (d.presentation hr).GroupType :=
  d.presentation_not_residuallyFinite hr hq hq200 (d.rectangular_nontriviality hr)

end Release075.MarkedLineData

end OAI
