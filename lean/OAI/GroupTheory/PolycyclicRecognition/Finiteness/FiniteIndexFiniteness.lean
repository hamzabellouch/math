import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexRestriction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupFiniteGenerationFromFP
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoarseFiniteness

namespace OAI

/-! # Integral FP finiteness is invariant under finite index

The reverse direction uses the proved coarse filling theorem. The necessary
finite-generation hypotheses are derived from FP one and coset representatives.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]

theorem group_fg_of_finiteIndex [Group.FG H] : Group.FG G := by
  let R := Set.range (rightCosetRepresentative H)
  have hR : R.Finite := finite_rightCosetRepresentatives H
  have hH : H.FG := (Group.fg_iff_subgroup_fg H).mp inferInstance
  have hK : H ⊔ Subgroup.closure R = ⊤ := by
    apply top_unique
    intro g _
    have heq : g = (subgroupCoordinate H g : G) * rightCosetRepresentative H g := by
      simp [subgroupCoordinate]
    rw [heq]
    exact Subgroup.mul_mem _
      (show (subgroupCoordinate H g : G) ∈ H ⊔ Subgroup.closure R from
        (show H ≤ H ⊔ Subgroup.closure R from le_sup_left) (subgroupCoordinate H g).property)
      ((show Subgroup.closure R ≤ H ⊔ Subgroup.closure R from le_sup_right)
        (Subgroup.subset_closure ⟨g, rfl⟩))
  apply Group.fg_def.mpr
  rw [← hK]
  exact hH.sup ((Subgroup.fg_iff _).mpr ⟨R, rfl, hR⟩)

theorem typeFP_finiteIndex_iff (n : ℕ) : TypeFP H n ↔ TypeFP G n := by
  constructor
  · intro hH
    cases n with
    | zero => exact typeFP_zero G
    | succ n =>
      let : Group.FG H := (hH.mono (by omega : 1 ≤ n + 1)).fg
      let : Group.FG G := group_fg_of_finiteIndex H
      exact liFinitenessInput H G (finiteIndexCoarseEquivalence H) (n + 1) hH
  · intro hG
    exact hG.finiteIndex_subgroup H

theorem typeFPInfinity_finiteIndex_iff : TypeFPInfinity H ↔ TypeFPInfinity G := by
  constructor <;> intro h n
  · exact (typeFP_finiteIndex_iff H n).mp (h n)
  · exact (typeFP_finiteIndex_iff H n).mpr (h n)

theorem IsIntegralPoincareDualityGroup.finiteIndex_subgroup {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : IsIntegralPoincareDualityGroup H n := by
  let : Group.FG G := hG.1.fg
  let : Group.FG H := inferInstance
  exact liDualityInput G H (finiteIndexCoarseEquivalence H).symm
    (hG.finiteCohomologicalDimension G) ((hG.finiteCohomologicalDimension G).subgroup H)
    n hG

end PolycyclicRecognition

end

end OAI
