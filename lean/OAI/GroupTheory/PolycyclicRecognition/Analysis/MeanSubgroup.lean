import OAI.GroupTheory.Thompson.InvariantMean
import Mathlib.GroupTheory.Coset.Basic

namespace OAI

/-!
# Restricting invariant means to subgroups

The finite-index height kernel in the recognition argument inherits amenability
from the ambient group. The construction below works for an arbitrary subgroup:
choose representatives for right cosets, construct an equivariant map to the subgroup,
and extend each bounded function by composition with this map.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u

variable {G : Type u} [Group G]

/-- The representative selected for the right coset containing `g`. -/
def rightCosetRepresentative (K : Subgroup G) (g : G) : G :=
  (Quotient.mk'' g : Quotient (QuotientGroup.rightRel K)).out

/-- A right-coset transversal gives an equivariant coordinate in the subgroup. -/
def subgroupCoordinate (K : Subgroup G) (g : G) : K :=
  ⟨g * (rightCosetRepresentative K g)⁻¹,
    QuotientGroup.rightRel_apply.mp
      (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' g :
        Quotient (QuotientGroup.rightRel K))))⟩

/-- The subgroup coordinate intertwines the left action of the subgroup. -/
theorem subgroupCoordinate_mul (K : Subgroup G) (k : K) (g : G) :
    subgroupCoordinate K ((k : G) * g) = k * subgroupCoordinate K g := by
  have hq : (Quotient.mk'' ((k : G) * g) : Quotient (QuotientGroup.rightRel K)) =
      Quotient.mk'' g := by
    apply Quotient.sound'
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using K.inv_mem k.property
  apply Subtype.ext
  change (k : G) * g * (rightCosetRepresentative K ((k : G) * g))⁻¹ =
    (k : G) * (g * (rightCosetRepresentative K g)⁻¹)
  unfold rightCosetRepresentative
  rw [hq, mul_assoc]

/-- Extend a bounded subgroup function to the whole group by the equivariant coordinate. -/
def subgroupFunctionExtension (K : Subgroup G) : BoundedReal K →ₗ[ℝ] BoundedReal G where
  toFun f := ⟨fun g => f (subgroupCoordinate K g), memℓp_infty ⟨‖f‖, by
    rintro y ⟨g, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (subgroupCoordinate K g)⟩⟩
  map_add' f g := by
    apply lp.ext
    funext x
    rfl
  map_smul' r f := by
    apply lp.ext
    funext x
    rfl

@[simp]
theorem subgroupFunctionExtension_apply (K : Subgroup G) (f : BoundedReal K) (g : G) :
    subgroupFunctionExtension K f g = f (subgroupCoordinate K g) := rfl

@[simp]
theorem subgroupFunctionExtension_one (K : Subgroup G) :
    subgroupFunctionExtension K 1 = 1 := by
  apply lp.ext
  funext g
  rfl

/-- Equivariance makes extension commute with pullback by subgroup translations. -/
theorem subgroupFunctionExtension_leftPull (K : Subgroup G) (k : K) (f : BoundedReal K) :
    subgroupFunctionExtension K (leftPull k f) =
      leftPull (k : G) (subgroupFunctionExtension K f) := by
  apply lp.ext
  funext g
  change f (k * subgroupCoordinate K g) = f (subgroupCoordinate K ((k : G) * g))
  rw [subgroupCoordinate_mul]

/-- Every subgroup of a group with an invariant mean has an invariant mean. -/
def subgroupInvariantMean (M : InvariantMean G) (K : Subgroup G) : InvariantMean K where
  toLinearMap := M.toLinearMap.comp (subgroupFunctionExtension K)
  positive f hf := M.positive _ (fun g => hf (subgroupCoordinate K g))
  normalized := by
    change M.toLinearMap (subgroupFunctionExtension K 1) = 1
    rw [subgroupFunctionExtension_one]
    exact M.normalized
  left_invariant k f := by
    change M.toLinearMap (subgroupFunctionExtension K (leftPull k f)) =
      M.toLinearMap (subgroupFunctionExtension K f)
    rw [subgroupFunctionExtension_leftPull]
    exact M.left_invariant (k : G) (subgroupFunctionExtension K f)

end PolycyclicRecognition

end

end OAI
