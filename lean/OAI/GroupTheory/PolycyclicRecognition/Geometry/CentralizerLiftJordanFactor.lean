import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleCentralizerExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteSemisimpleLiftFamily

namespace OAI

/-! # All lifts in a centralizer fiber retain the same semisimple factor -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

theorem inner_centralizer_preserves_jordan_factor (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (v : L) (hv : Commute S.toLinearMap (polynomialInnerLieEquiv v).toLinearMap) :
    ∃ W : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧
      (polynomialInnerLieEquiv v).toLinearMap * A.toLinearMap = S.toLinearMap * W.toLinearMap := by
  let W := U.trans (polynomialInnerLieEquiv v)
  have hW : W.toLinearMap = (polynomialInnerLieEquiv v).toLinearMap * U.toLinearMap := rfl
  refine ⟨W, polynomial_inner_mul_unipotent U hU v, ?_, ?_⟩
  · rw [hW]
    exact hv.mul_right hSU
  · rw [hA, hW, ← mul_assoc, hv.symm.eq, mul_assoc]

theorem centralizer_same_fiber_jordan_factor (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (S U : L ≃ₗ⁅ℝ⁆ L) (t g : G)
    (ht : t ∈ semisimpleActionCentralizer E S)
    (hg : g ∈ semisimpleActionCentralizer E S)
    (hgt : E.rightHom g = E.rightHom t)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
      S.toLinearMap * U.toLinearMap) :
    ∃ W : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧
      (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap =
        S.toLinearMap * W.toLinearMap := by
  have hn : g * t⁻¹ ∈ E.inl.range := by
    rw [E.range_inl_eq_ker_rightHom]
    change E.rightHom (g * t⁻¹) = 1
    rw [map_mul, map_inv, hgt, mul_inv_cancel]
  obtain ⟨v, hv⟩ := hn
  have hvm : v ∈ innerCentralizerLieSubalgebra S :=
    (inl_mem_semisimpleCentralizer_iff E S v).mp (by
      rw [hv]
      exact (semisimpleActionCentralizer E S).mul_mem hg
        ((semisimpleActionCentralizer E S).inv_mem ht))
  obtain ⟨W, hW, hSW, he⟩ := inner_centralizer_preserves_jordan_factor
    (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)) S U hU hSU hA v
    ((mem_innerCentralizerLieSubalgebra_iff S v).mp hvm)
  refine ⟨W, hW, hSW, ?_⟩
  have hvg : E.inl v * t = g := by rw [hv]; group
  rw [← hvg, extension_conjugationLinear_inl_mul]
  exact he

end PolycyclicRecognition

end

end OAI
