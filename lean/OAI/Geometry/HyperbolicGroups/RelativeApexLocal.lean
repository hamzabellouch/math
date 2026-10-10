import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFanCorner
import OAI.Geometry.HyperbolicGroups.MacroRadialIndex
import OAI.Geometry.HyperbolicGroups.LetterNormalPicture
import OAI.Geometry.HyperbolicGroups.NormalFaceFilling
import OAI.Geometry.HyperbolicGroups.FrozenPrevious

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
abbrev target := exteriorWalkTarget n w d ell hell (letterDart n w ∘ word)
  (letterWordClosed n w ell word) c hc f
abbrev frozen := exteriorWalkFrozen n w d ell hell (letterDart n w ∘ word)
  (letterWordClosed n w ell word) c hc f
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma start_link_constant {x y : P.Dart} (h : P.pairing.vertex.SameCycle x y) :
    start n w ((target n w d ell hell word c hc f).label (P.index x)) = start n w ((target n w d ell hell word c hc f).label (P.index y)) := by
  exact (sameCycle_le_of_apply
    (s := Setoid.ker (fun x => start n w ((target n w d ell hell word c hc f).label (P.index x))))
    (fun x => (P.respects.1 x).symm)) h

lemma apex_interior (x : P.Dart)
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    ∃ s, P.index x = .inl s := by
  cases hx : P.index x with
  | inl s => exact ⟨s,rfl⟩
  | inr s =>
    rcases s with ⟨a,o,i⟩
    rw [hx] at ha
    cases o <;> change false = true at ha <;> cases ha

lemma index_edge_previous (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (x : P.Dart)
    (hy : (target n w d ell hell word c hc f).free ((target n w d ell hell word c hc f).kind (P.index (P.pairing.vertex x))) = false) :
    P.index (P.pairing.edge x) = (frozen n w d ell hell word c hc f).next⁻¹ (P.index (P.pairing.vertex x)) := by
  have he : (target n w d ell hell word c hc f).free ((target n w d ell hell word c hc f).kind (P.index (P.pairing.edge x))) = false := by
    have hk := P.kind (P.pairing.edge x)
    change (target n w d ell hell word c hc f).kind (P.index (P.pairing.vertex x)) = (target n w d ell hell word c hc f).kind (P.index (P.pairing.edge x)) at hk
    rw [← hk]; exact hy
  apply (frozen n w d ell hell word c hc f).next.injective
  simp only [Perm.inv_def,apply_symm_apply]
  exact (hm.commute ⟨P.pairing.edge x,he⟩).symm

lemma corner_previous (g : FanTriangle n w) (o : Bool) :
    rev n w ((target n w d ell hell word c hc f).label ((frozen n w d ell hell word c hc f).next⁻¹ (.inl (frozenCorner n w d g o)))) = cornerIn n w g o := by
  cases o <;> rfl
lemma corner_reverse (g : FanTriangle n w) (o : Bool) :
    (frozen n w d ell hell word c hc f).next⁻¹ (.inl (frozenCorner n w d g (!o))) = (target n w d ell hell word c hc f).opposite (.inl (frozenCorner n w d g o)) := by
  cases o <;> rfl
lemma corner_label (g : FanTriangle n w) (o : Bool) :
    (target n w d ell hell word c hc f).label (.inl (frozenCorner n w d g o)) = cornerOut n w g o := by
  cases o <;> rfl

lemma corner_ports (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) {x : P.Dart}
    {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index (P.pairing.vertex x) = .inl (frozenCorner n w d h p)) :
    cornerOut n w g o = cornerIn n w h p := by
  have he : (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) := P.paired x
  rw [index_edge_previous n w d ell hell word c hc f P hm x (by rw [hy]; rfl),hy,hx,
    corner_label] at he
  have hh := congrArg (rev n w) he
  rw [corner_previous,rev_rev] at hh
  exact hh.symm

lemma corner_no_two_step (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (hred : P.FullyReduced) {x : P.Dart}
    {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index (P.pairing.vertex x) = .inl (frozenCorner n w d h p)) :
    P.pairing.vertex (P.pairing.vertex x) ≠ x := by
  intro hh
  have hxy := corner_ports n w d ell hell word c hc f P hm hx hy
  have hyx := corner_ports n w d ell hell word c hc f P hm hy (by rw [hh]; exact hx)
  obtain ⟨rfl,rfl⟩ := reverse_corner_unique n w hxy hyx.symm
  apply hred x
  rw [index_edge_previous n w d ell hell word c hc f P hm x (by rw [hy]; rfl),hy,hx,corner_reverse]

lemma fan_corner {x : P.Dart} {g : FanTriangle n w} {o : Bool} {i : Fin 3}
    (hx : P.index x = .inl (.inr ⟨.inl g,o,i⟩))
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    P.index x = .inl (frozenCorner n w d g o) := by
  rw [hx]
  have hh := apex_side_corner n w d g o i (by rw [hx] at ha; exact ha)
  cases o <;> fin_cases i <;> first | rfl | cases hh

lemma apex_cases (x : P.Dart)
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    (∃ a e, P.index x = .inl (.inl (a,e))) ∨
      ∃ g o, P.index x = .inl (frozenCorner n w d g o) := by
  obtain ⟨s,hx⟩ := apex_interior n w d ell hell word c hc f P x ha
  cases s with
  | inl s => exact Or.inl ⟨s.1,s.2,hx⟩
  | inr s =>
    rcases s with ⟨g,o,i⟩
    rcases g with g | (s | z)
    · exact Or.inr ⟨g,o,fan_corner n w d ell hell word c hc f P hx ha⟩
    · exfalso
      change Fin 4 at i
      rw [hx] at ha
      cases o with
      | false =>
        change isApex n w (start n w (rev n w (squareSide n w s i))) = true at ha
        rw [squareSide_end] at ha
        cases ha
      | true =>
        change isApex n w (start n w (squareSide n w s i)) = true at ha
        rw [squareSide_start] at ha
        cases ha
    · exfalso
      change Fin 6 at i
      rw [hx] at ha
      cases o with
      | false =>
        change isApex n w (start n w (rev n w (letterDart n w (z.val i)))) = true at ha
        rw [rev_letter,start_letter] at ha
        cases ha
      | true =>
        change isApex n w (start n w (letterDart n w (z.val i))) = true at ha
        rw [start_letter] at ha
        cases ha

lemma top_adjacent_different (hred : P.FullyReduced) {x : P.Dart}
    {a b : Top n w} {e k : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (.inl (a,e)))
    (hy : P.index (P.pairing.vertex x) = .inl (.inl (b,k)))
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) : a ≠ b := by
  intro hab; subst b
  obtain ⟨j,hj⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f P hy
    ((SameCycle.rfl (f := P.pairing.face) (x := P.pairing.edge x)).apply_left)
  have hpair := P.paired x
  change (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) at hpair
  rw [hj,hx] at hpair
  change macroStep n w a j.adj = rev n w (macroStep n w a e.adj) at hpair
  have hj' : macroStep n w a j.symm.adj = macroStep n w a e.adj := by
    exact (macroStep_reverse n w a j.adj).trans
      ((congrArg (rev n w) hpair).trans (rev_rev n w _))
  have he : e = j.symm := macroStep_radial_injective n w a e j.symm
    (by rw [hx] at ha; exact ha) hj'.symm
  have hje : j = e.symm := by rw [he]; rfl
  apply hred x
  rw [hj,hx,hje]
  rfl

lemma top_unique_turn (hs : P.Simple) {x y : P.Dart} {a : Top n w}
    {e : MacroGraph.graph.Dart} (hx : P.index x = .inl (.inl (a,e)))
    (hxy : P.pairing.face.SameCycle x y) (b : Fan n w)
    (hax : start n w ((target n w d ell hell word c hc f).label (P.index x)) = .inr b)
    (hay : start n w ((target n w d ell hell word c hc f).label (P.index y)) = .inr b) : x = y := by
  obtain ⟨k,hk⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f P hx hxy
  rw [hx] at hax
  rw [hk] at hay
  change start n w (macroStep n w a e.adj) = .inr b at hax
  change start n w (macroStep n w a k.adj) = .inr b at hay
  have hax := (macroStep_start n w a e.adj).symm.trans hax
  have hay := (macroStep_start n w a k.adj).symm.trans hay
  have he : e.fst = k.fst := (macroVertex_at_apex n w a e.fst b hax).trans
    (macroVertex_at_apex n w a k.fst b hay).symm
  apply P.simple_front hs (by rw [hx]; rfl) hxy
  rw [hx,hk]
  exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl he))

lemma apex_no_fixed (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (hred : P.FullyReduced) (x : P.Dart)
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    P.pairing.vertex x ≠ x := by
  intro he
  rcases apex_cases n w d ell hell word c hc f P x ha with ⟨a,e,hx⟩ | ⟨g,o,hx⟩
  · exact top_adjacent_different n w d ell hell word c hc f P hred hx (by rw [he]; exact hx) ha rfl
  · have hports := corner_ports n w d ell hell word c hc f P hm hx (by rw [he]; exact hx)
    exact corner_bipartite n w g o (congrArg (dartPart n w) hports)

lemma link_card (hrad : P.RadialInjective (isApex n w)) (a : P.Dart) (b : Fan n w)
    (ha : start n w ((target n w d ell hell word c hc f).label (P.index a)) = .inr b) :
    Fintype.card {x : P.Dart // P.pairing.vertex.SameCycle a x} ≤ 5 := by
  let j : {x : P.Dart // P.pairing.vertex.SameCycle a x} → Outgoing n w b := fun x =>
    ⟨(target n w d ell hell word c hc f).label (P.index x.val),(start_link_constant n w d ell hell word c hc f P x.property).symm.trans ha⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply hrad x.val y.val
    · change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x.val))) = true
      rw [← start_link_constant n w d ell hell word c hc f P x.property,ha]; rfl
    · exact x.property.symm.trans y.property
    · exact congrArg Subtype.val hxy
  exact (Fintype.card_le_of_injective j hj).trans (card_outgoing n w b)

lemma vertex_inverse (x : P.Dart) :
    P.pairing.vertex⁻¹ x = P.pairing.edge (P.pairing.face⁻¹ x) := by
  apply P.pairing.vertex.injective
  rw [Perm.inv_def,apply_symm_apply]
  change x = P.pairing.face (P.pairing.edge (P.pairing.edge (P.pairing.face⁻¹ x)))
  rw [P.pairing.edge_edge,Perm.inv_def,apply_symm_apply]

lemma corner_incoming (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o)) :
    (target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)) = cornerIn n w g o := by
  rw [vertex_inverse]
  have hh := P.paired (P.pairing.face⁻¹ x)
  change (target n w d ell hell word c hc f).label (P.index (P.pairing.edge (P.pairing.face⁻¹ x))) =
    rev n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.face⁻¹ x))) at hh
  rw [hh,P.frozen_previous_index (frozen n w d ell hell word c hc f) hm (by rw [hx]; rfl),hx,corner_previous]

lemma triangle_bipartite (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o)) :
    dartPart n w ((target n w d ell hell word c hc f).label (P.index x)) ≠
      dartPart n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x))) := by
  rw [corner_incoming n w d ell hell word c hc f P hm hx,hx,corner_label]
  exact corner_bipartite n w g o

lemma triangle_inverse_no_two (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) {x : P.Dart} {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index (P.pairing.vertex⁻¹ x) = .inl (frozenCorner n w d h p)) :
    P.pairing.vertex⁻¹ (P.pairing.vertex⁻¹ x) ≠ x := by
  intro he
  have hn := corner_no_two_step n w d ell hell word c hc f P hm hred hy
    (by rw [Perm.inv_def,apply_symm_apply]; exact hx)
  rw [Perm.inv_def,apply_symm_apply] at hn
  have hh := congrArg P.pairing.vertex he
  simp only [Perm.inv_def,apply_symm_apply] at hh
  exact hn hh.symm

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
