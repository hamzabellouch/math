import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicCoinvariants

namespace OAI

/-! # The augmentation kernel of the integral group ring -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra

variable (G : Type) [Group G]

def integralAugmentation : ℤ[G] →ₗ[ℤ] ℤ :=
  (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1).hom.toLinearMap

@[simp] theorem integralAugmentation_single (g : G) (r : ℤ) :
    integralAugmentation G (MonoidAlgebra.single g r) = r := by
  exact (Rep.leftRegularHom_hom_single g 1 r).trans (by simp)

theorem integralAugmentation_leftRegular (g : G) (x : ℤ[G]) :
    integralAugmentation G (Representation.leftRegular ℤ G g x) =
      integralAugmentation G x := by
  simpa only [integralAugmentation, Rep.trivial_ρ, Representation.trivial_apply,
    Representation.leftRegular, Representation.IntertwiningMap.toLinearMap_apply] using
    Rep.hom_comm_apply (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1) g x

theorem sub_augmentation_mem_coinvariants (x : ℤ[G]) :
    x - MonoidAlgebra.single 1 (integralAugmentation G x) ∈
      Coinvariants.ker (Representation.leftRegular ℤ G) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, MonoidAlgebra.single_add]
      convert (Coinvariants.ker (Representation.leftRegular ℤ G)).add_mem hx hy using 1
      abel
  | single g r =>
      rw [integralAugmentation_single]
      simpa using Coinvariants.sub_mem_ker (ρ := Representation.leftRegular ℤ G)
        g (MonoidAlgebra.single 1 r)

theorem integralAugmentation_ker :
    LinearMap.ker (integralAugmentation G) =
      Coinvariants.ker (Representation.leftRegular ℤ G) := by
  apply le_antisymm
  · intro x hx
    have hz : integralAugmentation G x = 0 := hx
    simpa only [hz, MonoidAlgebra.single_zero, sub_zero] using
      sub_augmentation_mem_coinvariants G x
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, x⟩, rfl⟩
    change integralAugmentation G (Representation.leftRegular ℤ G g x - x) = 0
    rw [map_sub, integralAugmentation_leftRegular, sub_self]

theorem integralAugmentation_ker_of_cyclic (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (integralAugmentation G) =
      LinearMap.range (Representation.leftRegular ℤ G g - LinearMap.id) :=
  (integralAugmentation_ker G).trans (cyclic_coinvariantsKer_eq_range _ g hg)

end PolycyclicRecognition

end

end OAI
