import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianSubgroupRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteDimensionTorsionFree
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.FractionRing

namespace OAI

/-! # Rationalizing the bounded-rank abelian subgroups

The integral dimension bound applies even to abelian subgroups which are not
finitely generated. Their rationalizations have the same rank, and the
canonical map is injective because integral cohomological dimension excludes
torsion. Thus these subgroups embed in finite-dimensional rational spaces.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct

variable {A : Type} [CommGroup A]

abbrev RationalAbelianSpace (A : Type) [CommGroup A] := ℚ ⊗[ℤ] Additive A

def rationalAbelianMap : Additive A →ₗ[ℤ] RationalAbelianSpace A :=
  TensorProduct.mk ℤ ℚ (Additive A) 1

theorem rationalAbelianMap_injective (hA : HasNoNontrivialTorsion A) :
    Function.Injective (rationalAbelianMap (A := A)) := by
  let : IsMulTorsionFree A := isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
    intro a ha hf
    exact ha (hA a (orderOf a) (ne_of_gt hf.orderOf_pos) (pow_orderOf_eq_one a)))
  let : IsAddTorsionFree (Additive A) := inferInstance
  let : Module.IsTorsionFree ℤ (Additive A) := inferInstance
  exact Module.Flat.tensorProduct_mk_injective ℤ (Additive A) ℚ

theorem rationalAbelianSpace_rank :
    Module.rank ℚ (RationalAbelianSpace A) = Module.rank ℤ (Additive A) := by
  exact (TensorProduct.isBaseChange ℤ (Additive A) ℚ).rank_eq

theorem abelian_subgroup_rational_rank_le {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [IsMulCommutative H] :
    Module.rank ℚ (RationalAbelianSpace H) ≤ d := by
  rw [rationalAbelianSpace_rank]
  exact abelian_subgroup_integral_rank_le d H

theorem abelian_subgroup_rational_finite {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [IsMulCommutative H] :
    Module.Finite ℚ (RationalAbelianSpace H) :=
  Module.rank_lt_aleph0_iff.mp <|
    (abelian_subgroup_rational_rank_le d H).trans_lt Cardinal.natCast_lt_aleph0

theorem abelian_subgroup_rationalMap_injective {G : Type} [Group G]
    (hG : HasFiniteIntegralCohomologicalDimension G)
    (H : Subgroup G) [IsMulCommutative H] :
    Function.Injective (rationalAbelianMap (A := H)) :=
  rationalAbelianMap_injective (hG.subgroup H).torsionFree

end PolycyclicRecognition

end

end OAI
