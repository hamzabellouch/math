import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeWalkTarget
import OAI.Geometry.HyperbolicGroups.FrozenWalk

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

private def freeReverse : Perm (Top n w × MacroGraph.graph.Dart) where
  toFun s := (s.1,s.2.symm)
  invFun s := (s.1,s.2.symm)
  left_inv := by intro s; rcases s with ⟨a,e⟩; rfl
  right_inv := by intro s; rcases s with ⟨a,e⟩; rfl

variable {A : Type*} [AddCommGroup A]

def walkFrozenTarget (c : Top n w → MacroGraph.graph.Dart → A)
    (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A) :
    FrozenTarget (walkTarget n w d c hc f) where
  next := Equiv.sumCongr 1 (frozenBoundary n w d).next
  reverse := Equiv.sumCongr (freeReverse n w) (frozenBoundary n w d).opposite
  reverse_eq := by rintro (s | s) <;> rfl
  reverse_sq := by
    apply Equiv.ext
    rintro (⟨a,e⟩ | ⟨a,b,i⟩)
    · rfl
    · cases b <;> rfl
  reverse_next := by
    rintro (s | s)
    · rfl
    · exact congrArg Sum.inr ((frozenBoundary n w d).reverse_next s)
  opposite_cycle := by
    let F : WalkStep n w d → Option (Top n w × MacroGraph.graph.Dart) :=
      fun s => match s with | .inl a => some a | .inr _ => none
    let G : WalkStep n w d → Option Bool :=
      fun s => match s with | .inl _ => none | .inr a => some a.2.1
    have hF : ∀ s, F ((Equiv.sumCongr (1 : Perm (Top n w × MacroGraph.graph.Dart)) (frozenBoundary n w d).next) s) = F s := by
      rintro (s | s) <;> rfl
    have hG : ∀ s, G ((Equiv.sumCongr (1 : Perm (Top n w × MacroGraph.graph.Dart)) (frozenBoundary n w d).next) s) = G s := by
      rintro (s | s) <;> rfl
    rintro (⟨a,e⟩ | ⟨a,b,i⟩) h
    · have hh := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Option (Top n w × MacroGraph.graph.Dart)))) hF h)
      have he : e = e.symm := congrArg Prod.snd (Option.some.inj hh)
      exact e.fst_ne_snd (congrArg (fun e : MacroGraph.graph.Dart => e.fst) he)
    · have hh := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Option Bool))) hG h)
      cases b <;> cases hh
  opposite_weight := by
    rintro (s | s)
    · exact walkWeight_opposite n w d c hc f (.inl s)
    · exact walkWeight_opposite n w d c hc f (.inr s)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
