import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegralAugmentation

namespace OAI

/-! # Injectivity of the difference map for an infinite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra

variable {G : Type} [Group G] [Infinite G]

theorem leftRegular_fixed_generator_eq_zero (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : ℤ[G])
    (hx : Representation.leftRegular ℤ G g x = x) : x = 0 := by
  obtain ⟨a, ha⟩ := x.coeff.support.exists_notMem
  have hcoeff : x.coeff g = 0 :=
    (coeff_of_leftRegular_of_generator g hg x hx a).symm.trans
      (Finsupp.notMem_support_iff.mp ha)
  ext b
  exact (coeff_of_leftRegular_of_generator g hg x hx b).trans hcoeff

theorem leftRegular_difference_injective (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Injective
      ((Representation.leftRegular ℤ G g - LinearMap.id) : ℤ[G] →ₗ[ℤ] ℤ[G]) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  apply leftRegular_fixed_generator_eq_zero g hg x
  exact sub_eq_zero.mp hx

end PolycyclicRecognition

end

end OAI
