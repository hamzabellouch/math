import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Analysis.FieldVectorState
import OAI.Analysis.IrrationalRotation.Operators.FieldTraceFaithfulness
import OAI.Analysis.IrrationalRotation.Analysis.FieldPositivity
import OAI.Analysis.IrrationalRotation.Operators.HilbertModelSize
import OAI.Analysis.IrrationalRotation.Analysis.FieldCovariance

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω}

theorem represented_eq_zero_of_field_ae_zero
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hA : A =ᵐ[μ] 0) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT ξ, hA, Lp.coeFn_zero E 2 μ] with x hx hxA hx0
  simpa only [hxA, Pi.zero_apply, zero_apply, hx0] using hx

variable [CompleteSpace E] [IsFiniteMeasure μ]

theorem represented_eq_zero_of_vector_state_zero
    (b : HilbertBasis ℤ ℂ E) (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hpos : ∀ᵐ x ∂μ, (A x).IsPositive)
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hcov : ∀ r : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b 0) (A (σ r x) (b 0)) = inner ℂ (b r) (A x (b r)))
    (hzero : inner ℂ (Lp.const 2 μ (b 0)) (T (Lp.const 2 μ (b 0))) = 0) :
    T = 0 := by
  have hi : Integrable (fun x => inner ℂ (b 0) (A x (b 0))) μ := by
    apply (L2.integrable_inner (𝕜 := ℂ) (Lp.const 2 μ (b 0))
      (T (Lp.const 2 μ (b 0)))).congr
    filter_upwards [Lp.coeFn_const 2 μ (b 0), hT (Lp.const 2 μ (b 0))]
      with x hx hTx
    rw [hTx, hx]
    rfl
  have heq : (fun x => (inner ℂ (A x (b 0)) (b 0)).re) =
      fun x => (inner ℂ (b 0) (A x (b 0))).re := by
    funext x
    exact inner_re_symm (𝕜 := ℂ) (A x (b 0)) (b 0)
  have hcov' : ∀ r : ℤ, ∀ᵐ x ∂μ,
      (inner ℂ (A x (b r)) (b r)).re =
        (inner ℂ (A (σ r x) (b 0)) (b 0)).re := by
    intro r
    filter_upwards [hcov r] with x hx
    calc
      (inner ℂ (A x (b r)) (b r)).re = (inner ℂ (b r) (A x (b r))).re :=
        inner_re_symm (𝕜 := ℂ) (A x (b r)) (b r)
      _ = (inner ℂ (b 0) (A (σ r x) (b 0))).re := congrArg Complex.re hx.symm
      _ = (inner ℂ (A (σ r x) (b 0)) (b 0)).re :=
        inner_re_symm (𝕜 := ℂ) (b 0) (A (σ r x) (b 0))
  have hint : Integrable (fun x => (inner ℂ (A x (b 0)) (b 0)).re) μ := by
    rw [heq]
    exact hi.re
  have htr : (∫ x, (inner ℂ (A x (b 0)) (b 0)).re ∂μ) = 0 := by
    rw [heq]
    change (∫ x, RCLike.re (inner ℂ (b 0) (A x (b 0))) ∂μ) = 0
    rw [integral_re hi,
      ← constant_vector_state_eq_integral T A hT (b 0), hzero]
    rfl
  exact represented_eq_zero_of_field_ae_zero T A hT
    (FieldTraceFaithfulness.ae_eq_zero_of_integral_diagonal_eq_zero
      μ b 0 A σ hσ hpos hcov' hint htr)

theorem faithfulTracialVector_of_covariant_fields [IsProbabilityMeasure μ]
    (b : HilbertBasis ℤ ℂ E) (M : VonNeumannAlgebra (Lp E 2 μ))
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hfields : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M →
      ∃ A : Ω → E →L[ℂ] E,
        (∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) ∧
        (∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ) ∧
        (∀ᵐ x ∂μ, ‖A x‖ ≤ ‖T‖) ∧
        (∀ r k l : ℤ, ∀ᵐ x ∂μ,
          inner ℂ (b k) (A (σ r x) (b l)) =
            inner ℂ (b (k + r)) (A x (b (l + r)))) ∧
        (T.IsPositive → ∀ᵐ x ∂μ, (A x).IsPositive)) :
    IsFaithfulTracialVector M (Lp.const 2 μ (b 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Lp.norm_const' 2 μ (b 0) (by norm_num) (by norm_num)]
    simp [b.orthonormal.norm_eq_one]
  · intro T S hTM hSM
    obtain ⟨A, hT, hA, hAbound, hcovA, _⟩ := hfields T hTM
    obtain ⟨B, hS, hB, hBbound, hcovB, _⟩ := hfields S hSM
    exact constant_vector_state_cyclic_of_covariance b T S A B hT hS hA hB
      ‖T‖ ‖S‖ (norm_nonneg _) (norm_nonneg _) hAbound hBbound σ hσ hcovA hcovB
  · intro T hTM hpos hzero
    obtain ⟨A, hT, _, _, hcov, hApos⟩ := hfields T hTM
    apply represented_eq_zero_of_vector_state_zero b T A hT (hApos hpos) σ hσ
    · intro r
      simpa only [zero_add] using hcov r 0 0
    · exact hzero

theorem faithfulTracialVector_of_represented_covariant_fields
    [IsProbabilityMeasure μ]
    (b : HilbertBasis ℤ ℂ E) (M : VonNeumannAlgebra (Lp E 2 μ))
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hfields : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M →
      ∃ A : Ω → E →L[ℂ] E,
        (∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) ∧
        (∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ) ∧
        (∀ᵐ x ∂μ, ‖A x‖ ≤ ‖T‖) ∧
        (∀ r k l : ℤ, ∀ᵐ x ∂μ,
          inner ℂ (b k) (A (σ r x) (b l)) =
            inner ℂ (b (k + r)) (A x (b (l + r))))) :
    IsFaithfulTracialVector M (Lp.const 2 μ (b 0)) := by
  let := HilbertModelSize.separable_of_countable_hilbertBasis b
  apply faithfulTracialVector_of_covariant_fields b M σ hσ
  intro T hTM
  obtain ⟨A, hT, hA, hAbound, hcov⟩ := hfields T hTM
  exact ⟨A, hT, hA, hAbound, hcov,
    ae_isPositive_of_represented_isPositive T A hT⟩

theorem faithfulTracialVector_of_commuting_shiftedPullbacks [IsProbabilityMeasure μ]
    (b : HilbertBasis ℤ ℂ E) (M : VonNeumannAlgebra (Lp E 2 μ))
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (S : ℤ → E →ₗᵢ[ℂ] E) (hS : ∀ r k : ℤ, S r (b k) = b (k + r))
    (hcomm : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M → ∀ r,
      Commute T (DirectIntegral.shiftedPullback (S r).toContinuousLinearMap (σ r) (hσ r)))
    (hfields : ∀ T : Lp E 2 μ →L[ℂ] Lp E 2 μ, T ∈ M →
      ∃ A : Ω → E →L[ℂ] E,
        (∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) ∧
        (∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ) ∧
        (∀ᵐ x ∂μ, ‖A x‖ ≤ ‖T‖)) :
    IsFaithfulTracialVector M (Lp.const 2 μ (b 0)) := by
  apply faithfulTracialVector_of_represented_covariant_fields b M σ hσ
  intro T hTM
  obtain ⟨A, hT, hA, hAbound⟩ := hfields T hTM
  refine ⟨A, hT, hA, hAbound, ?_⟩
  exact ae_matrix_covariance_of_commute b T A
    (fun r => DirectIntegral.shiftedPullback (S r).toContinuousLinearMap (σ r) (hσ r))
    S σ hσ hS hT
    (fun r => shiftedPullback_ae (S r).toContinuousLinearMap (σ r) (hσ r)) (hcomm T hTM)

end Invariant233.FieldTraceCyclic

end OAI
