import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteDimensionHomology
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalInductionSupport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupShapiro
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareTopHomology

namespace OAI

/-! # Top homology vanishes in a normal subgroup of infinite index -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem IsIntegralPoincareDualityGroup.infiniteQuotient_topHomology_zero {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (N : Subgroup G)
    [N.Normal] [Infinite (G ⧸ N)] (A : Rep ℤ N) : IsZero (groupHomology A n) := by
  obtain ⟨D, ⟨eD⟩, hD⟩ := hG.topHomology_orientation
  obtain ⟨e⟩ := hD (Rep.ind N.subtype A)
  let j := (subgroupShapiroIso N A n).toLinearEquiv.trans e
  have hsub : Subsingleton (groupHomology A n) := ⟨by
    intro x y
    apply j.injective
    exact (rankOne_induced_hom_eq_zero N A D eD (j x)).trans
      (rankOne_induced_hom_eq_zero N A D eD (j y)).symm⟩
  let := hsub
  exact ModuleCat.isZero_of_subsingleton _

theorem IsIntegralPoincareDualityGroup.lt_dimension_of_normal_topHomology {n d : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (N : Subgroup G)
    [N.Normal] [Infinite (G ⧸ N)] (A : Rep ℤ N)
    (x : groupHomology A d) (hx : x ≠ 0) : d < n := by
  have hd : d ≤ n := by
    by_contra h
    let := hG.cohomologicalDimension
    let := subgroup_cohomologicalDimension_le N n
    have hz := groupHomology_isZero_above_dimension n A d (Nat.lt_of_not_ge h)
    let := ModuleCat.subsingleton_of_isZero hz
    exact hx (Subsingleton.elim _ _)
  have hne : d ≠ n := by
    rintro rfl
    let := ModuleCat.subsingleton_of_isZero (hG.infiniteQuotient_topHomology_zero N A)
    exact hx (Subsingleton.elim _ _)
  omega

end PolycyclicRecognition

end

end OAI
