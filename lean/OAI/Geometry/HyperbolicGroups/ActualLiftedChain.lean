import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCover

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type v} [Group G] (voltage : Dart n w → G)
  (hv : ∀ e, voltage (rev n w e) = (voltage e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => voltage (side n w d a i))).prod = 1)
variable {A : Type z} [AddCommGroup A]
  (c : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, c g a e.symm = -c g a e) (f : G → FrozenCell n w d → A)

def liftedWalkTarget :=
  (actualCellCover n w d voltage hv hcell).target
    (fun g => walkWeight n w d (c g) (f g))
    (fun g s _ => walkWeight_opposite n w d (c g) (hc g) (f g) s)

def liftedFrozenTarget : FrozenTarget (liftedWalkTarget n w d voltage hv hcell c hc f) :=
  (actualCellCover n w d voltage hv hcell).frozenTarget
    (fun g => walkWeight n w d (c g) (f g))
    (fun g s _ => walkWeight_opposite n w d (c g) (hc g) (f g) s)
    (indexingFrozenTarget n w d)
    (fun g s => walkWeight_opposite n w d (c g) (hc g) (f g) s)

/-- Source closed-picture conclusion with independent signed coefficients for
EACH lift of every elementary cone triangle and frozen cell, and actual
prefix-product and cone-route coordinates. The cutoff is selected before
the realization, deck group, voltage and coefficients. -/
theorem uniform_actual_lifted_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (G : Type v) [Group G] (A : Type z) [AddCommGroup A]
        (voltage : Dart n w → G) (hv : ∀ e, voltage (rev n w e) = (voltage e)⁻¹)
        (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => voltage (side n w d a i))).prod = 1)
        (c : G → Top n w → MacroGraph.graph.Dart → A)
        (hc : ∀ g a e, c g a e.symm = -c g a e) (f : G → FrozenCell n w d → A)
        (P : WalkPicture.{u} (liftedWalkTarget n w d voltage hv hcell c hc f)),
        P.FrozenMapped (liftedFrozenTarget n w d voltage hv hcell c hc f) → P.chain = 0 := by
  obtain ⟨M,hM,hh⟩ := uniform_lifted_picture_chain_zero.{u,v,z} ha hb hd
  refine ⟨M,hM,?_⟩
  intro n w d hgood G _ A _ voltage hv hcell c hc f P hm
  exact hh n w d hgood G A (actualCellCover n w d voltage hv hcell)
    (fun g => walkWeight n w d (c g) (f g))
    (fun g s => walkWeight_opposite n w d (c g) (hc g) (f g) s) P hm

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
