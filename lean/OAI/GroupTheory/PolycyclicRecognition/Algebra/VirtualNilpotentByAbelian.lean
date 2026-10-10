import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralLayerUnipotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralLayersWordProjection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtuallyUnipotentCommutatorAction
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OAI

/-! # Finite-index nilpotent-by-abelian structure in finite integral dimension

The maximal nilpotent normal subgroup has finite-dimensional rational
central layers. After passing to finite index the derived action on those
layers is uniformly unipotent. The centralizer criterion then puts that
derived subgroup inside the nilpotent normal subgroup itself.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Group.IsSolvable G]

theorem exists_finiteIndex_commutator_le_maximal_nilpotent
    (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]
    (hFcd : HasFiniteIntegralCohomologicalDimension F)
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ (commutator H).map H.subtype ≤ F := by
  let c := Group.nilpotencyClass F
  let := centralLayersSpace_finite F hFcd c
  let ρ := centralLayersAction F c
  obtain ⟨H, hHn, hHi, d, hd⟩ := exists_finiteIndex_rational_commutator_words ρ
  let := hHn
  let D := (commutator H).map H.subtype
  let K := F ⊔ D
  have hmatch (a : K) : ∃ b : commutator H, ρ a = ρ (b : H) := by
    have ha : (a : G) ∈ (F : Set G) * (D : Set G) := by
      rw [← Subgroup.normal_mul]
      exact a.property
    obtain ⟨f, hf, x, hx, he⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨⟨b, hb⟩, ?_⟩
    change ρ (a : G) = ρ (b : G)
    rw [← he, map_mul]
    have hf' : ρ f = 1 := subgroup_le_centralLayersAction_ker F c hf
    rw [hf', one_mul]
    rfl
  have hwords : ∀ w : List K, w.length = d →
      actionOperatorWord (fun g : K => (ρ g).toLinearMap - 1) w = 0 := by
    apply actionOperatorWord_zero_of_matching_generators
      (fun g : K => (ρ g).toLinearMap - 1)
      (fun a : commutator H => (ρ (a : H)).toLinearMap - 1) _ d hd
    intro a
    obtain ⟨b, hb⟩ := hmatch a
    exact ⟨b, by rw [hb]⟩
  have hK : Group.IsNilpotent K := by
    apply nilpotent_of_unipotent_central_layers F hFcd.torsionFree K
      (centralizer_le_maximal_nilpotent_normal F hmax)
    intro i hi
    exact ⟨d, centralLayers_word_projection F c K d hwords ⟨i, hi⟩⟩
  have he : K = F := hmax K inferInstance hK le_sup_left
  exact ⟨H, hHn, hHi, (show D ≤ K from le_sup_right).trans_eq he⟩

theorem exists_nilpotent_normal_finiteIndex_commutator
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ F : Subgroup G, F.Normal ∧ Group.IsNilpotent F ∧
      ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ (commutator H).map H.subtype ≤ F := by
  obtain ⟨F, hFn, hF, hmax⟩ := exists_maximal_nilpotent_normal_subgroup hG
  let := hFn
  let := hF
  exact ⟨F, hFn, hF,
    exists_finiteIndex_commutator_le_maximal_nilpotent F (hG.subgroup F) hmax⟩

end PolycyclicRecognition

end

end OAI
