import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! # Gluing representations across a normal subgroup product

This is the algebraic descent used to integrate a solvable representation
from its nilpotent ideal and Cartan subgroup: agreement on the intersection
and compatibility with conjugation are exactly the required relations.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N H G A : Type*} [Group N] [Group H] [Group G] [Group A]

theorem exists_representation_of_factor_maps
    (φ : H →* MulAut N) (iN : N →* G) (iH : H →* G)
    (hbase : ∀ h, iN.comp (φ h).toMonoidHom =
      (MulAut.conj (iH h)).toMonoidHom.comp iN)
    (hcover : ∀ g : G, ∃ n : N, ∃ h : H, iN n * iH h = g)
    (fN : N →* A) (fH : H →* A)
    (hconj : ∀ (h : H) (n : N), fN (φ h n) = fH h * fN n * (fH h)⁻¹)
    (hagree : ∀ (n : N) (h : H), iN n = iH h → fN n = fH h) :
    ∃ f : G →* A, ∀ (n : N) (h : H), f (iN n * iH h) = fN n * fH h := by
  have htarget (h : H) : fN.comp (φ h).toMonoidHom =
      (MulAut.conj (fH h)).toMonoidHom.comp fN := by
    ext n
    exact hconj h n
  let π : N ⋊[φ] H →* G := SemidirectProduct.lift iN iH hbase
  let F : N ⋊[φ] H →* A := SemidirectProduct.lift fN fH htarget
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨n, h, rfl⟩ := hcover g
    exact ⟨⟨n, h⟩, rfl⟩
  have hker : π.ker ≤ F.ker := by
    intro z hz
    change iN z.left * iH z.right = 1 at hz
    change fN z.left * fH z.right = 1
    have heq : iN z.left = iH z.right⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hz
    rw [hagree z.left z.right⁻¹ heq, map_inv, inv_mul_cancel]
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let F' := QuotientGroup.lift π.ker F hker
  refine ⟨F'.comp e.symm.toMonoidHom, ?_⟩
  intro n h
  have he : e (QuotientGroup.mk (⟨n, h⟩ : N ⋊[φ] H)) = iN n * iH h := rfl
  change F' (e.symm (iN n * iH h)) = _
  rw [← he, e.symm_apply_apply]
  rfl

end PolycyclicRecognition

end

end OAI
