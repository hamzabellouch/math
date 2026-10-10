import OAI.GroupTheory.PolycyclicRecognition.Algebra.NonabelianFactorSystem
import Mathlib.GroupTheory.GroupExtension.Defs

namespace OAI

/-! # Maps between groups with the same quotient factor system -/

namespace PolycyclicRecognition.FactorExtension
variable {N M Q : Type*} [Group N] [Group M] [Group Q]
  (S : NonabelianFactorSystem N Q) (T : NonabelianFactorSystem M Q)
  (f : N →* M)
  (ha : ∀ q n, f (S.action q n) = T.action q (f n))
  (hc : ∀ q r, f (S.factor q r) = T.factor q r)

/-- Extend a kernel homomorphism compatible with both action and cocycle. -/
def map : FactorExtension S →* FactorExtension T where
  toFun a := ⟨f a.left, a.right⟩
  map_one' := by apply FactorExtension.ext; exact f.map_one; rfl
  map_mul' a b := by
    apply FactorExtension.ext
    · change f (a.left * S.action a.right b.left * S.factor a.right b.right) = _
      simp only [map_mul, ha, hc]
      rfl
    · rfl

theorem map_injective (hf : Function.Injective f) :
    Function.Injective (map S T f ha hc) := by
  intro a b h
  apply FactorExtension.ext
  · exact hf (congrArg FactorExtension.left h)
  · exact congrArg (fun x : FactorExtension T => x.right) h


/-- The defining group extension of a factor system. -/
def groupExtension : GroupExtension N (FactorExtension S) Q where
  inl := inl S
  rightHom := projection S
  inl_injective := inl_injective S
  range_inl_eq_ker_rightHom := by
    ext a
    constructor
    · rintro ⟨n, rfl⟩
      rfl
    · intro ha
      change a.right = 1 at ha
      refine ⟨a.left, ?_⟩
      apply FactorExtension.ext
      · rfl
      · exact ha.symm
  rightHom_surjective := projection_surjective S

end PolycyclicRecognition.FactorExtension

end OAI
