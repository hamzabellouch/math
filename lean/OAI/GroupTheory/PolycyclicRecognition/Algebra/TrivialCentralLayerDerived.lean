import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyBoundedDerivedSeries

namespace OAI

/-! # Trivial central-layer action bounds the derived series modulo the centralizer -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]

theorem centralLayers_kernel_derived_le_centralizer (hF : HasNoNontrivialTorsion F) :
    ambientDerivedSeries (centralLayersAction F (Group.nilpotencyClass F)).ker
      (Group.nilpotencyClass F) ≤ Subgroup.centralizer (F : Set G) := by
  let c := Group.nilpotencyClass F
  let K := (centralLayersAction F c).ker
  let U := ambientUpperCentralSeries F
  have hstep (i : ℕ) : ⁅K, U (i + 1)⁆ ≤ U i := by
    by_cases hi : i < c
    · apply commutator_centralLayer_le_of_rational_kernel F hF i K
      intro g hg
      exact (centralLayersAction_ker_iff F c g).mp hg ⟨i, hi⟩
    · have he (j : ℕ) (hj : c ≤ j) : U j = F := by
        dsimp [U, ambientUpperCentralSeries]
        rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr hj]
        simp only [Subgroup.map_top, Subgroup.range_subtype]
      rw [he i (by omega), he (i + 1) (by omega)]
      exact Subgroup.commutator_le_right K F
  have hz : ⁅K.lowerCentralSeries c, F⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    have he : U (c + 1) = F := by
      dsimp [U, ambientUpperCentralSeries]
      rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr (Nat.le_succ c)]
      simp only [Subgroup.map_top, Subgroup.range_subtype]
    have hd := lowerCentralSeries_action_depth K U hstep c 0
    simpa only [Nat.zero_add, he, U, ambientUpperCentralSeries_zero] using hd
  have hder : ambientDerivedSeries K c ≤ K.lowerCentralSeries c := by
    rw [ambientDerivedSeries, ← Subgroup.top_subtype_lowerCentralSeries]
    exact Subgroup.map_mono (Subgroup.derived_le_lower_central c)
  exact hder.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz)

end PolycyclicRecognition

end

end OAI
