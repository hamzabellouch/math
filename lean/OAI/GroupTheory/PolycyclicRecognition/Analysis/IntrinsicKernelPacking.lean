import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothExponentialHeight

namespace OAI

/-! # Polynomial bounded-height packing from the intrinsic nilpotent kernel -/

noncomputable section
namespace PolycyclicRecognition

open PositiveTriangular
open scoped Manifold Matrix.Norms.Operator

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem polynomialBoundedChainPacking_intrinsic
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    PolynomialBoundedChainPacking (fun g => (π g).toAdd) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let d := q.toLinearMap.comp (heightProjection T.character)
  have hd : Function.Surjective d := q.surjective.comp (heightProjection_surjective T.character)
  let : FiniteDimensional ℝ W := Module.Finite.of_surjective d hd
  have hπ : Continuous π := (contMDiff_height_of_exponential_linear hExp π d he).continuous
  obtain ⟨N, ExpN, hExpN, ι, _, _, hιExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ he
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2
    ExpN hExpN (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  obtain ⟨m, hm, ρ, hρ, hnil⟩ := onshuusPostRealizationInput_intrinsic T Exp hExp
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hker : ∀ g, π g = 1 → StrictUpper (matrix (ρ g) - 1) := by
    intro g hg
    have hg' : g ∈ Set.range ι := by rw [hrange]; exact hg
    obtain ⟨n, hn⟩ := hg'
    obtain ⟨v, hv⟩ := cN.surjective n
    have hx : Exp (N.equiv.symm v) = g := by
      rw [← hιExp]
      simp only [N.equiv.apply_symm_apply]
      rw [← hcN, hv, hn]
    rw [← hx]
    exact hnil _ (N.equiv.symm v).property
  exact polynomialBoundedChainPacking_of_unipotent_kernel π ρ
    (integrated_height_surjective T q Exp π he)
    (isQuotientMap_of_exponential_linear_quotient hExp d hd π he hπ) hρ hker

end PolycyclicRecognition

end

end OAI
