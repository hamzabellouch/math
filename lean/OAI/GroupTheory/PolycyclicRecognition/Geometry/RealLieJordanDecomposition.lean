import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealJordanLieFactor
import OAI.GroupTheory.PolycyclicRecognition.Geometry.InvertibleJordanDecomposition
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

namespace OAI

/-! # Multiplicative Jordan decomposition inside real Lie automorphisms -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

theorem real_lie_jordan_decomposition_centralizer (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      A.toLinearMap = S.toLinearMap * U.toLinearMap ∧
      ∀ T : Module.End ℝ L, Commute A.toLinearMap T →
        Commute S.toLinearMap T ∧ Commute U.toLinearMap T := by
  obtain ⟨s, u, hs, hu, hsu, hA, _, hcom⟩ := invertible_jordan_decomposition_centralizer A.toLinearMap
    ((Module.End.isUnit_iff _).mpr A.bijective)
  have hc : Commute A.toLinearMap (s : Module.End ℝ L) := by
    rw [hA]
    exact (Commute.refl _).mul_left hsu.symm
  have hn : IsNilpotent (A.toLinearMap - (s : Module.End ℝ L)) := by
    have he : A.toLinearMap - (s : Module.End ℝ L) = (s : Module.End ℝ L) * (u - 1) := by
      rw [hA, mul_sub, mul_one]
    rw [he]
    obtain ⟨k, hk⟩ := hu
    exact ⟨k, by rw [(hsu.sub_right (Commute.one_right _)).mul_pow, hk, mul_zero]⟩
  let S : L ≃ₗ⁅ℝ⁆ L :=
    { LinearMap.GeneralLinearGroup.toLinearEquiv s with
      map_lie' := fun {x y} =>
        real_semisimple_jordan_factor_map_lie A (s : Module.End ℝ L) hs hc hn x y }
  let U : L ≃ₗ⁅ℝ⁆ L := A.trans S.symm
  have heS : S.toLinearMap = (s : Module.End ℝ L) := rfl
  have heU : U.toLinearMap = u := by
    change (s⁻¹ : (Module.End ℝ L)ˣ) * A.toLinearMap = u
    rw [hA, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨S, U, heS.symm ▸ hs, heU.symm ▸ hu,
    by rwa [heS, heU], by rwa [heS, heU], ?_⟩
  intro T hT
  rw [heS, heU]
  exact hcom T hT

theorem real_lie_jordan_decomposition (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      A.toLinearMap = S.toLinearMap * U.toLinearMap := by
  obtain ⟨S, U, hs, hu, hc, he, _⟩ := real_lie_jordan_decomposition_centralizer A
  exact ⟨S, U, hs, hu, hc, he⟩

end PolycyclicRecognition

end

end OAI
