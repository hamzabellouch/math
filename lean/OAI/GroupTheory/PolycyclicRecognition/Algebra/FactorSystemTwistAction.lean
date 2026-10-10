import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemTwist
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionMap
import Mathlib.GroupTheory.SemidirectProduct

namespace OAI

/-! # The removed action and the original extension

The removed quotient action acts on the twisted extension. The original
extension embeds into its semidirect product as the graph of the quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {N Q : Type} [Group N] [Group Q] [IsMulCommutative Q]
  (R : NonabelianFactorSystem N Q) (χ : Q →* MulAut N)
  (hcomm : ∀ q r, Commute (R.action q) (χ r))
  (hfix : ∀ q r s, χ q (R.factor r s) = R.factor r s)

private theorem twist_action_commutes (q r : Q) (x : N) :
    χ q ((R.twist χ hcomm hfix).action r x) =
      (R.twist χ hcomm hfix).action r (χ q x) := by
  have hc₀ : Commute (χ q) (χ r) := by
    change χ q * χ r = χ r * χ q
    rw [← map_mul, ← map_mul, mul_comm q r]
  have hc : Commute (χ q) ((χ r)⁻¹) := hc₀.inv_right
  have ha : χ q (R.action r x) = R.action r (χ q x) :=
    DFunLike.congr_fun (hcomm r q).symm.eq x
  change χ q ((χ r)⁻¹ (R.action r x)) = (χ r)⁻¹ (R.action r (χ q x))
  have hi : χ q ((χ r)⁻¹ (R.action r x)) = (χ r)⁻¹ (χ q (R.action r x)) :=
    DFunLike.congr_fun hc.eq _
  rw [hi, ha]

def factorTwistAction : Q →* MulAut (FactorExtension (R.twist χ hcomm hfix)) where
  toFun q :=
    { toFun a := ⟨χ q a.left, a.right⟩
      invFun a := ⟨χ q⁻¹ a.left, a.right⟩
      left_inv a := by
        apply FactorExtension.ext
        · change (χ q⁻¹ * χ q) a.left = a.left
          rw [← map_mul, inv_mul_cancel, map_one]
          rfl
        · rfl
      right_inv a := by
        apply FactorExtension.ext
        · change (χ q * χ q⁻¹) a.left = a.left
          rw [← map_mul, mul_inv_cancel, map_one]
          rfl
        · rfl
      map_mul' a b := by
        apply FactorExtension.ext
        · change χ q (a.left * (R.twist χ hcomm hfix).action a.right b.left *
              R.factor a.right b.right) = _
          rw [map_mul, map_mul, twist_action_commutes, hfix]
          rfl
        · rfl }
  map_one' := by
    apply DFunLike.ext
    intro a
    apply FactorExtension.ext
    · exact DFunLike.congr_fun (map_one χ) a.left
    · rfl
  map_mul' q r := by
    apply DFunLike.ext
    intro a
    apply FactorExtension.ext
    · exact DFunLike.congr_fun (map_mul χ q r) a.left
    · rfl

/-- The graph embedding retains both coordinates of the original group. -/
def factorTwistGraph : FactorExtension R →*
    (FactorExtension (R.twist χ hcomm hfix) ⋊[factorTwistAction R χ hcomm hfix] Q) where
  toFun a := ⟨⟨a.left, a.right⟩, a.right⟩
  map_one' := rfl
  map_mul' a b := by
    apply SemidirectProduct.ext
    · apply FactorExtension.ext
      · change a.left * R.action a.right b.left * R.factor a.right b.right =
          a.left * (R.twist χ hcomm hfix).action a.right (χ a.right b.left) *
            R.factor a.right b.right
        rw [factorSystem_twist_recompose]
      · rfl
    · rfl

theorem factorTwistGraph_injective : Function.Injective (factorTwistGraph R χ hcomm hfix) := by
  intro a b h
  apply FactorExtension.ext
  · exact congrArg (fun z => z.left.left) h
  · exact congrArg (fun z => z.right) h

end PolycyclicRecognition

end

end OAI
