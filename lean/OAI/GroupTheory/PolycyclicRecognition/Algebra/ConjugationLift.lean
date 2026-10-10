import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # Recovering a group action from faithful conjugation

Pointwise automorphisms compatible with ambient conjugation automatically
form an action. This removes a separate action-law assumption when the Cartan
automorphisms have already been identified in a faithful representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {N D G : Type*} [Group N] [Group D] [Group G]

/-- Faithful ambient conjugation forces the action laws. -/
def conjugationLift (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (a : D → MulAut N)
    (ha : ∀ d n, ι (a d n) = κ d * ι n * (κ d)⁻¹) : D →* MulAut N where
  toFun := a
  map_one' := by
    apply MulEquiv.ext
    intro n
    apply hι
    simp only [ha, map_one, inv_one, one_mul, mul_one, MulAut.one_apply]
  map_mul' d e := by
    apply MulEquiv.ext
    intro n
    apply hι
    simp only [ha, map_mul, mul_inv_rev, MulAut.mul_apply]
    simp only [mul_assoc]

@[simp] theorem conjugationLift_apply
    (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (a : D → MulAut N) (ha : ∀ d n, ι (a d n) = κ d * ι n * (κ d)⁻¹)
    (d : D) : conjugationLift ι κ hι a ha d = a d := rfl

/-- A normal image supplies the pointwise automorphisms by transport from
the actual subgroup. In particular, no action is part of this premise. -/
def conjugationLiftOfNormal (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (hnormal : ι.range.Normal) : D →* MulAut N := by
  let _ := hnormal
  let e : N ≃* ι.range := MonoidHom.ofInjective hι
  let a : D → MulAut N := fun d => e.trans ((MulAut.conjNormal (κ d)).trans e.symm)
  apply conjugationLift ι κ hι a
  intro d n
  simp only [a, e, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

theorem conjugationLiftOfNormal_spec (ι : N →* G) (κ : D →* G)
    (hι : Function.Injective ι) (hnormal : ι.range.Normal) (d : D) (n : N) :
    ι (conjugationLiftOfNormal ι κ hι hnormal d n) = κ d * ι n * (κ d)⁻¹ := by
  let _ := hnormal
  simp only [conjugationLiftOfNormal, conjugationLift, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

end PolycyclicRecognition

end

end OAI
