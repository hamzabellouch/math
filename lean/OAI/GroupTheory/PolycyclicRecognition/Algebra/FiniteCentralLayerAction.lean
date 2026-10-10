import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRationalRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentQuotient

namespace OAI

/-! # Uniform index of the central-layer action kernel -/
noncomputable section
namespace PolycyclicRecognition
open Module
open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]

omit [F.Normal] in
theorem centralLayer_finrank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] (i : ℕ) :
    Module.finrank ℚ (RationalAbelianSpace (CentralLayer F i)) ≤ d := by
  let := nilpotent_upperCentral_center_rational_finite (G := F) d i
  apply FiniteDimensional.finrank_le_iff_rank_le.mpr
  rw [rationalAbelianSpace_rank]
  exact nilpotent_quotient_abelian_subgroup_rank_le d
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (Subgroup.center _)

omit [F.Normal] in
theorem centralLayersSpace_finrank_le (d c : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] :
    Module.finrank ℚ (CentralLayersSpace F c) ≤ c * d := by
  let := centralLayersSpace_finite F ⟨d, inferInstance⟩ c
  let (i : Fin c) : Module.Finite ℚ (RationalAbelianSpace (CentralLayer F i)) :=
    nilpotent_upperCentral_center_rational_finite (G := F) d i
  change Module.finrank ℚ ((i : Fin c) → RationalAbelianSpace (CentralLayer F i)) ≤ c * d
  rw [Module.finrank_pi_fintype]
  calc
    ∑ i : Fin c, Module.finrank ℚ (RationalAbelianSpace (CentralLayer F i)) ≤
        ∑ _i : Fin c, d := Finset.sum_le_sum (fun i _ => centralLayer_finrank_le F d i)
    _ = c * d := by simp

theorem centralLayersAction_index_le [F.FiniteIndex] (d c : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] :
    (centralLayersAction F c).ker.index ≤ 3 ^ ((c * d) * (c * d)) := by
  let ρ := centralLayersAction F c
  let : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le (subgroup_le_centralLayersAction_ker F c)
  let : Finite ρ.range := Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_ker]
    exact Subgroup.FiniteIndex.index_ne_zero)
  let := centralLayersSpace_finite F ⟨d, inferInstance⟩ c
  let σ : ρ.range →* Module.End ℚ (CentralLayersSpace F c) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ.range.subtype
  have hσ : Function.Injective σ :=
    LinearEquiv.toLinearMap_injective.comp Subtype.val_injective
  have hb := finite_rational_representation_card_le σ hσ
  rw [Subgroup.index_ker]
  exact hb.trans (Nat.pow_le_pow_right (by omega)
    (Nat.mul_self_le_mul_self (centralLayersSpace_finrank_le F d c)))

end PolycyclicRecognition

end

end OAI
