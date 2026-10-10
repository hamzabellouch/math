import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkRawPosition
import OAI.Geometry.HyperbolicGroups.ConeApexProducer
import OAI.Geometry.HyperbolicGroups.IndexedFanCards
import OAI.Geometry.HyperbolicGroups.PictureVertexBoundary
import OAI.Geometry.HyperbolicGroups.FrozenPrevious

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

def walkApex (x : P.Dart) := isApex n w (start n w (walkLabel n w d (P.index x)))
def walkSelected (x : P.Dart) := select (P.faceClass x)
def walkRadial (x : P.Dart) : Prop := isLetter n w (walkLabel n w d (P.index x)) = false

abbrev RadialBoundarySide := P.pairing.BoundarySide (fun x => walkSelected n w d c hc f P select x = true)
  (walkRadial n w d c hc f P)

lemma walk_apex_previous (x : P.Dart) :
    walkApex n w d c hc f P (P.pairing.vertex⁻¹ x) = walkApex n w d c hc f P x := by
  exact congrArg (isApex n w) (walk_start_link_constant n w d c hc f P
    (sameCycle_inv.mp (SameCycle.rfl.apply_left)))
lemma walk_apex_paired (x : P.Dart) (hx : walkApex n w d c hc f P x = true) :
    walkApex n w d c hc f P (P.pairing.edge x) = false := by
  change isApex n w (start n w (walkLabel n w d (P.index (P.pairing.edge x)))) = false
  have he : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  rw [he]
  exact radial n w _ hx
lemma walk_apex_radial (x : P.Dart) (hx : walkApex n w d c hc f P x = true) :
    walkRadial n w d c hc f P x := by
  change isApex n w (start n w (walkLabel n w d (P.index x))) = true at hx
  change isLetter n w (walkLabel n w d (P.index x)) = false
  generalize hh : walkLabel n w d (P.index x) = l at *
  rcases l with ⟨e,o⟩
  cases e with
  | inl a => cases hx
  | inr e => rfl
lemma walk_radial_paired (x : P.Dart) :
    walkRadial n w d c hc f P (P.pairing.edge x) ↔ walkRadial n w d c hc f P x := by
  unfold walkRadial
  have he : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  rw [he]
  rfl

lemma walk_transitions_le_boundary : Fintype.card
    (P.pairing.VertexTransition (walkApex n w d c hc f P) (walkSelected n w d c hc f P select)) ≤
    Fintype.card (RadialBoundarySide n w d c hc f P select) := by
  apply P.pairing.vertex_transitions_le_boundary
  · intro x; exact congrArg select (P.faceClass_apply x)
  · exact walk_apex_previous n w d c hc f P
  · exact walk_apex_paired n w d c hc f P
  · exact walk_apex_radial n w d c hc f P
  · exact walk_radial_paired n w d c hc f P

lemma fragment_active (b : Fan n w) (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    (fragmentMark n w d c hc f P select b z x).plain.active = select (P.faceClass x.val) := by
  unfold fragmentMark
  split_ifs with hs ht <;> simp_all [FanLink.Mark.plain,FanLink.State.active]

/-- Tags on actual apex corners are determined by their source dart. -/
lemma apexCorner_injective : Function.Injective
    (fun p : Σ b : Fan n w, Σ z : ApexInstance n w d c hc f P select b, P.Link z.val => p.2.2.val) := by
  rintro ⟨b,z,x⟩ ⟨a,y,k⟩ h
  have hb : b = a := Sum.inr.inj ((instance_start n w d c hc f P select b z x).symm.trans
    ((congrArg (fun t => start n w (walkLabel n w d (P.index t))) h).trans
      (instance_start n w d c hc f P select a y k)))
  subst a
  have hz : z = y := Subtype.ext (x.property.symm.trans ((congrArg P.vertexClass h).trans k.property))
  subst y
  exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subtype.ext h))))

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllBoundaryIndex := Σ b : Fan n w,
  (indexedFanData n w d c hc f P select b hs hm hred hrad).BoundaryIndex

def boundaryTransition (p : AllBoundaryIndex n w d c hc f P select hs hm hred hrad) :
    P.pairing.VertexTransition (walkApex n w d c hc f P) (walkSelected n w d c hc f P select) := by
  refine ⟨p.2.val.2.val,instance_apex n w d c hc f P select p.1 p.2.val.1 p.2.val.2,?_⟩
  have hh := p.2.property
  change (fragmentMark n w d c hc f P select p.1 p.2.val.1 p.2.val.2).plain.active ≠
    (fragmentMark n w d c hc f P select p.1 p.2.val.1 (P.linkNext p.2.val.1.val p.2.val.2)).plain.active at hh
  rw [fragment_active,fragment_active] at hh
  exact hh

lemma boundaryTransition_injective : Function.Injective
    (boundaryTransition n w d c hc f P select hs hm hred hrad) := by
  intro p q h
  have hh : (⟨p.1,p.2.val⟩ : Σ b : Fan n w, Σ z : ApexInstance n w d c hc f P select b, P.Link z.val) =
      ⟨q.1,q.2.val⟩ := apexCorner_injective n w d c hc f P select (congrArg Subtype.val h)
  rcases p with ⟨b,x⟩; rcases q with ⟨a,y⟩
  have hb : b = a := congrArg Sigma.fst hh
  subst a
  have hv : x.val = y.val := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))

lemma allBoundaryIndex_card : Fintype.card (AllBoundaryIndex n w d c hc f P select hs hm hred hrad) =
    ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).boundary := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natBoundaryIndex_card
    (fun b => indexedFanData n w d c hc f P select b hs hm hred hrad)

/-- The partial-apex error is paid by actual radial boundary sides. No
radial-side accounting identity is supplied as an extra hypothesis. -/
theorem actual_radial_sides :
    (∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).boundary) ≤
      Fintype.card (RadialBoundarySide n w d c hc f P select) := by
  rw [← allBoundaryIndex_card n w d c hc f P select hs hm hred hrad]
  exact (Fintype.card_le_of_injective _
    (boundaryTransition_injective n w d c hc f P select hs hm hred hrad)).trans
    (walk_transitions_le_boundary n w d c hc f P select)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
