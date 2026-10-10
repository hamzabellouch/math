import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeFrozenTarget
import OAI.Geometry.HyperbolicGroups.ConeMappedWalk
import OAI.Geometry.HyperbolicGroups.FullWalkNormal

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- Full actual mixed-cell normal form, with literal complete frozen face
maps as the only raw indexing condition. Every finite genus-zero input is
normalized by the checked surgeries, without assuming any fan link data,
contact bound, or filling estimate. -/
theorem normalizedPicture (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f)) :
    ∃ Q : WalkPicture.{u} (walkTarget n w d c hc f),
      Nonempty (P.Survives Q) ∧ Q.FrozenMapped (walkFrozenTarget n w d c hc f) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective (isApex n w) ∧
      Q.chain = P.chain ∧
      ∀ (hs : Q.Simple) (hb : Q.NoBigon) (x : Q.Dart) (a : Top n w)
        (e : MacroGraph.graph.Dart) (hx : Q.index x = .inl (a,e)),
        Fintype.card {y : Q.Dart // Q.pairing.face.SameCycle x y} ≤ 15 ∧
          3 ≤ (mappedMacroPolygon n w d c hc f Q hs hb x a e hx).points.card := by
  obtain ⟨Q,hr,hm,hs,hb,hred,hrad,hchain⟩ := P.normalize_full
    (walkFrozenTarget n w d c hc f) hm (isApex n w)
    (fun s => radial n w (walkLabel n w d s))
  refine ⟨Q,hr,hm,hs,hb,hred,hrad,hchain,?_⟩
  intro hs hb x a e hx
  let B := mappedMacroPolygon n w d c hc f Q hs hb x a e hx
  constructor
  · exact B.perimeter_le
  · apply B.points_ge
    change 0 < Fintype.card {y : Q.Dart // Q.pairing.face.SameCycle x y}
    exact Fintype.card_pos_iff.mpr ⟨⟨x,SameCycle.rfl⟩⟩
end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
