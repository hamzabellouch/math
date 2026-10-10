import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCentralLayerAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCentralizerCommutator
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteConjugationIndexBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TrivialCentralLayerDerived

namespace OAI

/-! # Uniform solvability bounds from a nilpotent finite-index subgroup -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G] (F : Subgroup G)
  [F.Normal] [F.FiniteIndex] [Group.IsNilpotent F]

theorem bounded_solvable_subgroup_of_nilpotent_finiteIndex
    (hF : HasNoNontrivialTorsion F) (b d : ℕ)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral F) d] :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      H.index ≤ 3 ^ (((Group.nilpotencyClass F) * d) * ((Group.nilpotencyClass F) * d)) * b ^ b ∧
      derivedSeries H (Group.nilpotencyClass F + 2) = ⊥ := by
  let c := Group.nilpotencyClass F
  let K := (centralLayersAction F c).ker
  let C := Subgroup.centralizer (F : Set G)
  let D := (commutator C).map C.subtype
  let : Finite (commutator C) := centralizer_commutator_finite F
  let : Finite D := Finite.of_equiv (commutator C)
    ((commutator C).equivMapOfInjective C.subtype Subtype.val_injective).toEquiv
  let : D.Normal := by dsimp [D, C]; infer_instance
  let T := Subgroup.centralizer (D : Set G)
  let : T.FiniteIndex := finiteIndex_centralizer_of_finite_normal D
  let : K.FiniteIndex := Subgroup.finiteIndex_of_le (subgroup_le_centralLayersAction_ker F c)
  let H := K ⊓ T
  have hKD : ambientDerivedSeries K (c + 1) ≤ D := by
    rw [ambientDerivedSeries_succ]
    have hKC := centralLayers_kernel_derived_le_centralizer F hF
    simpa only [D, Subgroup.map_subtype_commutator] using Subgroup.commutator_mono hKC hKC
  have hHD : ambientDerivedSeries H (c + 1) ≤ D :=
    (ambientDerivedSeries_mono inf_le_left (c + 1)).trans hKD
  have hHT : ambientDerivedSeries H (c + 1) ≤ T :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hzero : ambientDerivedSeries H (c + 2) = ⊥ := by
    change ambientDerivedSeries H ((c + 1) + 1) = ⊥
    rw [ambientDerivedSeries_succ]
    apply eq_bot_iff.mpr
    apply (Subgroup.commutator_mono hHD hHT).trans
    rw [Subgroup.commutator_comm D T]
    exact le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl)
  refine ⟨H, inferInstance, ?_, ?_⟩
  · exact (Subgroup.index_inf_le (H := K) (K := T)).trans (Nat.mul_le_mul
      (centralLayersAction_index_le F d c) (finite_normal_centralizer_index_le D b (hb D inferInstance)))
  · apply eq_bot_iff.mpr
    intro x hx
    have hm : (x : G) ∈ ambientDerivedSeries H (c + 2) := ⟨x, hx, rfl⟩
    rw [hzero] at hm
    exact Subtype.ext hm

end PolycyclicRecognition

end

end OAI
