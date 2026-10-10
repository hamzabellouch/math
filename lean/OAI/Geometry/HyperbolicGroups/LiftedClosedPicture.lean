import Mathlib
import OAI.Geometry.HyperbolicGroups.GlobalClosedPicture
import OAI.Geometry.HyperbolicGroups.WalkCover

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z

/-- Zero coefficients specify the base indexing target only: the cover
has arbitrary independent weights for each lifted step. -/
def indexingTarget (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
    (d : (Fin 6 → Alphabet n) → Bool) :=
  walkTarget n w d (fun _ _ => (0 : ℤ)) (by simp) (fun _ => 0)

def indexingFrozenTarget (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
    (d : (Fin 6 → Alphabet n) → Bool) :=
  walkFrozenTarget n w d (fun _ _ => (0 : ℤ)) (by simp) (fun _ => 0)

/-- Normal-form vanishing holds in every regular voltage cover, with each
signed lifted cell retained separately. This is stronger than vanishing of
the projected base-cell chain. -/
theorem uniform_lifted_picture_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (G : Type v) [Group G] (B : Type z) [AddCommMonoid B]
        (H : WalkCellCover (indexingTarget n w d) G) (weight : G → WalkStep n w d → B)
        (hw : ∀ g s, weight g s + weight g (walkOpposite n w d s) = 0)
        (P : WalkPicture.{u} (H.target weight (fun g s _ => hw g s))),
        P.FrozenMapped (H.frozenTarget weight (fun g s _ => hw g s)
          (indexingFrozenTarget n w d) hw) → P.chain = 0 := by
  obtain ⟨K,hK,hh⟩ := uniform_normal_picture_empty.{u,0} ha hb hd
  refine ⟨8*K,Nat.mul_pos (by decide) hK,?_⟩
  intro n w d hgood G _ B _ H weight hw P hm
  let T := H.target weight (fun g s _ => hw g s)
  let F := H.frozenTarget weight (fun g s _ => hw g s) (indexingFrozenTarget n w d) hw
  obtain ⟨Q,_,hmQ,hsQ,hbQ,hrQ,hradQ,hchain⟩ :=
    P.normalize_full F hm (isApex n w ∘ Prod.snd) (by
      intro s hs
      exact radial n w (walkLabel n w d s.2) hs)
  let R := H.forget weight (fun g s _ => hw g s) Q
  have hR : IsEmpty R.Dart := hh n w d hgood ℤ (fun _ _ => 0) (by simp) (fun _ => 0) R
    (H.forget_simple _ _ Q hsQ)
    (H.forget_frozenMapped _ _ Q (indexingFrozenTarget n w d) hw hmQ)
    (H.forget_fullyReduced _ _ Q hrQ)
    (H.forget_radialInjective _ _ Q (isApex n w) hradQ)
    (H.forget_noBigon _ _ Q hbQ)
  have : IsEmpty Q.Dart := hR
  rw [← hchain]
  simp only [WalkPicture.chain,Finset.univ_eq_empty,Finset.sum_empty]

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
