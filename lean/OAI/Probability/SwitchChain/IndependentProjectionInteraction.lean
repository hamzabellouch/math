import OAI.Probability.SwitchChain.IndependentCell
import OAI.Probability.SwitchChain.FiniteEventVectors
import OAI.Probability.SwitchChain.RankOneCentering

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.IndependentCell

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem inner_constantVector (f : EuclideanSpace ℝ Ω) :
    ⟪f, FiniteEventVectors.constantVector⟫ =
      (∑ ω, f ω) / Real.sqrt (Fintype.card Ω : ℝ) := by
  rw [FiniteEventVectors.constantVector, FiniteEventVectors.eventVector,
    real_inner_smul_right, inner_eq_sum]
  simp only [FiniteEventVectors.rawIndicator, Finset.mem_univ, ite_true, mul_one]
  rw [div_eq_mul_inv, mul_comm]

theorem expectation_constantVector (R : Setoid Ω) :
    PairFibers.expectation R (FiniteEventVectors.constantVector (Ω := Ω)) =
      FiniteEventVectors.constantVector := by
  apply (PairFibers.expectation_eq_self_iff R _).mpr
  intro x y hxy
  simp [FiniteEventVectors.constantVector, FiniteEventVectors.eventVector,
    FiniteEventVectors.rawIndicator]

theorem covariance_constantVector (R S : Setoid Ω)
    (hcov : ∀ f g : EuclideanSpace ℝ Ω,
      ⟪PairFibers.expectation R f, PairFibers.expectation S g⟫ =
        (∑ ω, f ω) * (∑ ω, g ω) / (Fintype.card Ω : ℝ))
    (f g : EuclideanSpace ℝ Ω) :
    ⟪PairFibers.expectation R f, PairFibers.expectation S g⟫ =
      ⟪f, FiniteEventVectors.constantVector⟫ *
        ⟪g, FiniteEventVectors.constantVector⟫ := by
  rw [hcov, inner_constantVector, inner_constantVector, div_mul_div_comm]
  rw [Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card Ω))]

theorem independent_interaction_of_covariance [Nonempty Ω]
    (R S : Setoid Ω)
    (hcov : ∀ f g : EuclideanSpace ℝ Ω,
      ⟪PairFibers.expectation R f, PairFibers.expectation S g⟫ =
        (∑ ω, f ω) * (∑ ω, g ω) / (Fintype.card Ω : ℝ))
    (G : EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω)
    (hGs : G.IsSymmetric) (hGi : ∀ f, G (G f) = G f)
    (hGR : ∀ f, G (PairFibers.expectation R f) = 0)
    (hGS : ∀ f, G (PairFibers.expectation S f) = 0)
    (f : EuclideanSpace ℝ Ω) :
    ‖G f‖ ^ 2 ≤
      ⟪f - PairFibers.expectation R f, f - PairFibers.expectation S f⟫ := by
  apply RankOneInteraction.independent_interaction_with_constants
    (PairFibers.expectation R).toLinearMap (PairFibers.expectation S).toLinearMap G
    (PairFibers.expectation_symmetric R) (PairFibers.expectation_symmetric S) hGs
    (PairFibers.expectation_idempotent R) (PairFibers.expectation_idempotent S) hGi
    (FiniteEventVectors.constantVector (Ω := Ω))
    FiniteEventVectors.inner_constantVector_self
    (expectation_constantVector R) (expectation_constantVector S)
    (covariance_constantVector R S hcov) _ hGR hGS f
  rw [← expectation_constantVector R]
  exact hGR _

theorem independent_interaction_of_jointCount [Nonempty Ω]
    {α β : Type*} [Fintype α] [Fintype β]
    (X : Ω → α) (Y : Ω → β) (a : α → ℝ) (b : β → ℝ)
    (hcount : ∀ x y, (jointCount X Y x y : ℝ) = a x * b y)
    (G : EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω)
    (hGs : G.IsSymmetric) (hGi : ∀ f, G (G f) = G f)
    (hGX : ∀ f, G (PairFibers.expectation (Setoid.ker X) f) = 0)
    (hGY : ∀ f, G (PairFibers.expectation (Setoid.ker Y) f) = 0)
    (f : EuclideanSpace ℝ Ω) :
    ‖G f‖ ^ 2 ≤ ⟪f - PairFibers.expectation (Setoid.ker X) f,
      f - PairFibers.expectation (Setoid.ker Y) f⟫ :=
  independent_interaction_of_covariance (Setoid.ker X) (Setoid.ker Y)
    (projection_covariance_of_jointCount X Y a b hcount) G hGs hGi hGX hGY f

end Problem315.IndependentCell

end

end OAI
