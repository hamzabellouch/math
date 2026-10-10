import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonSemisimpleCentralizer

namespace OAI

/-! # Surjectivity survives successive semisimple centralizer reductions -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]

theorem common_semisimpleCentralizer_surjective_step
    (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ T ∈ ss, Module.End.IsSemisimple T.toLinearMap)
    (hpair : ∀ T ∈ ss, ∀ R ∈ ss, Commute T.toLinearMap R.toLinearMap)
    (hsurj : Function.Surjective (E.rightHom.comp (commonSemisimpleCentralizer E ss).subtype))
    (t : G) (ht : t ∈ commonSemisimpleCentralizer E ss) :
    ∃ S U : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
        S.toLinearMap * U.toLinearMap ∧
      (∀ T ∈ ss, Commute T.toLinearMap S.toLinearMap) ∧
      Function.Surjective (E.rightHom.comp (commonSemisimpleCentralizer E (S :: ss)).subtype) := by
  obtain ⟨S, U, hS, hU, hSU, hA, hTS, hc⟩ :=
    common_semisimpleCentralizer_step E hsmooth ss hss hpair t ht
  refine ⟨S, U, hS, hU, hSU, hA, hTS, ?_⟩
  intro q
  obtain ⟨g, hg⟩ := hsurj q
  obtain ⟨v, _, hv⟩ := hc g g.property
  refine ⟨⟨E.inl v * g, hv⟩, ?_⟩
  change E.rightHom (E.inl v * g) = q
  rw [map_mul, E.rightHom_inl, one_mul]
  exact hg

end PolycyclicRecognition

end

end OAI
