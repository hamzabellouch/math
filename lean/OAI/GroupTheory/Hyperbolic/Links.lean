import OAI.GroupTheory.Hyperbolic.Ribbons

namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

abbrev ODirections := (d.presentation hr).LEdge ⊕ (d.presentation hr).REdge
abbrev VDirections := ShiftScheme.XDirection (I := d.Label) (r := r) ⊕ (d.vShift hr).LDirection
abbrev WDirections := ShiftScheme.XDirection (I := d.Label) (r := r) ⊕ (d.wShift hr).LDirection
abbrev AllDirections := d.ODirections hr ⊕ (d.VDirections hr ⊕ d.WDirections hr)

/-- At O a larger complete bipartite graph suffices for the four-edge girth bound;
at V and W we use precisely the shifted incidence links. -/
noncomputable def allLink : SimpleGraph (d.AllDirections hr) :=
  (relationGraph (fun (_ : (d.presentation hr).LEdge) (_ : (d.presentation hr).REdge) => True)).sum
    ((d.vShift hr).link.sum (d.wShift hr).link)

def linkDirection : (d.presentation hr).OrientedEdge → d.AllDirections hr
  | (.inl (i,u,v),false) => .inr (.inl (.inl (i,u,v)))
  | (.inl (i,u,v),true) => .inr (.inr (.inl (i,v,u)))
  | (.inr (.inl l),false) => .inl (.inl l)
  | (.inr (.inl l),true) => .inr (.inl (.inr l))
  | (.inr (.inr s),false) => .inl (.inr s)
  | (.inr (.inr s),true) => .inr (.inr (.inr s))

def linkColor : d.AllDirections hr → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

 theorem linkDirection_color (a : (d.presentation hr).OrientedEdge) :
    d.linkColor hr (d.linkDirection hr a) =
      (d.presentation hr).vertexColor ((d.presentation hr).edgeTarget a) := by
  rcases a with ⟨a,s⟩
  rcases a with ⟨i,u,v⟩|l|s' <;> cases s <;> rfl

 theorem linkDirection_injective : Function.Injective (d.linkDirection hr) := by
  rintro ⟨a,s⟩ ⟨b,t⟩ h
  rcases a with ⟨i,u,v⟩|l|s'
  all_goals rcases b with ⟨j,u',v'⟩|l'|t'
  all_goals cases s <;> cases t <;> simp_all [linkDirection]
  all_goals exact Sum.inr.inj h

 theorem face_corner_adj {a b c : (d.presentation hr).OrientedEdge}
    (h : (d.presentation hr).TriangleFace a b c) :
    (d.allLink hr).Adj (d.linkDirection hr a)
      (d.linkDirection hr ((d.presentation hr).flipEdge b)) := by
  cases h <;>
    simp only [BlockPresentation.orientedL,BlockPresentation.orientedX,
      BlockPresentation.orientedR,BlockPresentation.flipEdge, Bool.not_true,
      Bool.not_false, linkDirection,allLink,SimpleGraph.sum_adj_inl,SimpleGraph.sum_adj_inr]
  all_goals first | exact True.intro | exact ⟨Subtype.prop _,rfl,rfl⟩

 theorem allLink_closed (a : d.AllDirections hr) (p : (d.allLink hr).Walk a a)
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight (d.linkColor hr a) * p.length := by
  rcases a with a|a|a
  · let p' := SumWalk.left p
    have hlen : p'.length = p.length := SumWalk.left_length p
    have hg := reduced_closed_length_ge 4 (relationGraph_cycle_length _) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced hp)
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,Fin.zero_eta,ite_true]
    exact_mod_cast (by omega : 12 ≤ 3*p.length)
  · let p' := SumWalk.left (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 14 (d.v_link_girth hr) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (1 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)
  · let p' := SumWalk.right (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 14 (d.w_link_girth hr) p'
      (by rw [hlen]; exact hn) (SumWalk.right_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (2 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)

 theorem v_reduced_same_label (i : d.Label) (u v u' v' : Fin r)
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk (.inr (.inl (.inl (i,u,v)))) (.inr (.inl (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 14 ≤ p.length := by
  let p' := SumWalk.left (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.left_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (d.vShift hr).projection
    (d.vShift hr).projection_locallyInjective 14 d.incidences_girth
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh

 theorem w_reduced_same_label (i : d.Label) (u v u' v' : Fin r)
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk (.inr (.inr (.inl (i,u,v)))) (.inr (.inr (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 14 ≤ p.length := by
  let p' := SumWalk.right (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.right_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (d.wShift hr).projection
    (d.wShift hr).projection_locallyInjective 14 d.incidences_girth
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

 theorem x_turn_large (i : d.Label) (u v u' v' : Fin r) (s t : Bool)
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (.inl (i,u',v'),t)) =
      (d.presentation hr).edgeTarget (.inl (i,u,v),s))
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk
      (d.linkDirection hr ((d.presentation hr).flipEdge (.inl (i,u',v'),t)))
      (d.linkDirection hr (.inl (i,u,v),s)))
    (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (.inl (i,u,v),s))) * p.length := by
  cases s <;> cases t <;>
    simp only [BlockPresentation.flipEdge,BlockPresentation.edgeTarget,Bool.not_false,Bool.not_true] at ht
  · cases ht
  · have hh := d.v_reduced_same_label hr i u' v' u v hne.symm p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 14 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 14) hh)
  · have hh := d.w_reduced_same_label hr i v' u' v u
      (by simpa only [ne_eq,Prod.mk.injEq,and_comm] using hne.symm) p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 14 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 14) hh)
  · cases ht

variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

noncomputable abbrev concreteRibbon := D.ribbon (d.presentation hr).vertexColor
  (fun _ _ _ => BlockPresentation.TriangleFace.colors _) b hb

def dartDirection (a : D.ActiveDart) : d.AllDirections hr :=
  d.linkDirection hr (D.label a)

theorem ribbon_outer_iff (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).IsOuter a ↔ a.val ∈ D.boundary :=
  D.active_boundary_iff hb a

theorem ribbon_color (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).color (cl (d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkColor hr (d.dartDirection hr D a) := by
  change (D.activeColor (d.presentation hr).vertexColor) (cl (D.activeReverse*D.activeNext) a) = _
  rw [TriangleFilling.activeColor,descend_cl]
  exact (d.linkDirection_color hr (D.label a)).symm

theorem ribbon_direction_step (a : D.ActiveDart) :
    d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkDirection hr ((d.presentation hr).flipEdge (D.label (D.next a))) := by
  change d.linkDirection hr (D.label (D.reverse (D.next a))) = _
  rw [D.reverse_label]

theorem ribbon_adj (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a) :
    (d.allLink hr).Adj (d.dartDirection hr D a)
      (d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  rw [d.ribbon_direction_step hr D b hb a]
  exact d.face_corner_adj hr (D.triangular a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))).2.2

theorem ribbon_reduced (hD : IsEmpty D.Dipole) (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a)
    (ha' : ¬(d.concreteRibbon hr D b hb).IsOuter ((d.concreteRibbon hr D b hb).vertexPerm a)) :
    d.dartDirection hr D a ≠
      d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm
        ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  intro he
  apply D.noDipole_link_reduced
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
    (d.presentation hr).flipEdge_flipEdge
    (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
    (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))
    (fun h => ha' ((d.ribbon_outer_iff hr D b hb _).mpr h))
  exact d.linkDirection_injective hr he

theorem ribbon_closed (a : D.ActiveDart)
    (p : (d.allLink hr).Walk (d.dartDirection hr D a) (d.dartDirection hr D a))
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    10 ≤ TriangleRibbon.weight ((d.concreteRibbon hr D b hb).color
      (cl (d.concreteRibbon hr D b hb).vertexPerm a)) * p.length := by
  rw [d.ribbon_color hr D b hb a]
  exact le_trans (by norm_num) (d.allLink_closed hr _ p hn hp)

end Release075.MarkedLineData

end OAI
