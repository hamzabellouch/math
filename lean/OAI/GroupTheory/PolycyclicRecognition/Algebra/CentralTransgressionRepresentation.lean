import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralTransgressionNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AutomorphismSecondHomologyAction

namespace OAI

/-! # The transgression intertwines actual automorphism actions -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q P : Type} [CommGroup N] [Group G] [Group Q] [Group P]

def automorphismAdditiveRepresentation (α : P →* MulAut N) :
    Representation ℤ P (Additive N) where
  toFun p := (α p).toAdditive.toIntLinearEquiv.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro n
    change Additive.ofMul (α 1 n.toMul) = n
    rw [map_one]
    rfl
  map_mul' p q := by
    apply LinearMap.ext
    intro n
    change Additive.ofMul (α (p * q) n.toMul) = Additive.ofMul (α p (α q n.toMul))
    rw [map_mul]
    rfl

def centralTransgressionIntertwining
    (E : GroupExtension N G Q) (hc : E.inl.range ≤ Subgroup.center G)
    (αN : P →* MulAut N) (αG : P →* MulAut G) (αQ : P →* MulAut Q)
    (hl : ∀ p n, αG p (E.inl n) = E.inl (αN p n))
    (hr : ∀ p a, E.rightHom (αG p a) = αQ p (E.rightHom a))
    (σ : E.Section) :
    Representation.IntertwiningMap (automorphismSecondHomologyRepresentation αQ)
      (automorphismAdditiveRepresentation αN) where
  toLinearMap := centralExtensionTransgression E hc σ
  isIntertwining' p := by
    apply LinearMap.ext
    intro x
    exact (centralExtensionTransgression_natural E E hc
      (αN p).toMonoidHom (αG p).toMonoidHom (αQ p).toMonoidHom
      (hl p) (hr p) hc σ σ x).symm

end PolycyclicRecognition

end

end OAI
