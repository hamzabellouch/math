import OAI.Analysis.IrrationalRotation.Operators.FieldTraceCyclic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

theorem constant_vector_state_eq_integral
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) (v : E) :
    inner ℂ (Lp.const 2 μ v) (T (Lp.const 2 μ v)) =
      ∫ x, inner ℂ v (A x v) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ v, hT (Lp.const 2 μ v)] with x hx hTx
  rw [hTx, hx]
  rfl

theorem constant_vector_state_mul_eq_integral
    (T S : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A B : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hS : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (S ξ) x = B x (ξ x)) (v : E) :
    inner ℂ (Lp.const 2 μ v) ((T * S) (Lp.const 2 μ v)) =
      ∫ x, inner ℂ v (A x (B x v)) ∂μ := by
  change inner ℂ (Lp.const 2 μ v) (T (S (Lp.const 2 μ v))) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ v, hT (S (Lp.const 2 μ v)),
    hS (Lp.const 2 μ v)] with x hx hTx hSx
  rw [hTx, hSx, hx]
  rfl

theorem constant_vector_state_cyclic_of_covariance [CompleteSpace E]
    (b : HilbertBasis ℤ ℂ E) (T S : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (A B : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hS : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (S ξ) x = B x (ξ x))
    (hA : ∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ)
    (hB : ∀ r : ℤ, AEStronglyMeasurable (fun x => B x (b r)) μ)
    (CA CB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hAbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA) (hBbound : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hcovA : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (A (σ r x) (b l)) = inner ℂ (b (k + r)) (A x (b (l + r))))
    (hcovB : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (B (σ r x) (b l)) = inner ℂ (b (k + r)) (B x (b (l + r)))) :
    inner ℂ (Lp.const 2 μ (b 0)) ((T * S) (Lp.const 2 μ (b 0))) =
      inner ℂ (Lp.const 2 μ (b 0)) ((S * T) (Lp.const 2 μ (b 0))) := by
  rw [constant_vector_state_mul_eq_integral T S A B hT hS,
    constant_vector_state_mul_eq_integral S T B A hS hT]
  exact integral_central_matrix_product_cyclic b A B hA hB CA CB hCA hCB
    hAbound hBbound σ hσ hcovA hcovB

theorem constant_vector_state_one [IsProbabilityMeasure μ] (v : E) (hv : ‖v‖ = 1) :
    inner ℂ (Lp.const 2 μ v) ((1 : Lp E 2 μ →L[ℂ] Lp E 2 μ) (Lp.const 2 μ v)) = 1 := by
  change inner ℂ (Lp.const 2 μ v) (Lp.const 2 μ v) = _
  rw [inner_self_eq_norm_sq_to_K, Lp.norm_const' 2 μ v (by norm_num) (by norm_num)]
  simp [hv]

theorem constant_vector_state_nonneg
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (hT : T.IsPositive) (v : E) :
    0 ≤ (inner ℂ (Lp.const 2 μ v) (T (Lp.const 2 μ v))).re :=
  hT.re_inner_nonneg_right (Lp.const 2 μ v)

theorem norm_constant_vector_state_le [IsProbabilityMeasure μ]
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (v : E) (hv : ‖v‖ = 1) :
    ‖inner ℂ (Lp.const 2 μ v) (T (Lp.const 2 μ v))‖ ≤ ‖T‖ := by
  have hc : ‖Lp.const 2 μ v‖ = 1 := by
    rw [Lp.norm_const' 2 μ v (by norm_num) (by norm_num)]
    simp [hv]
  calc
    ‖inner ℂ (Lp.const 2 μ v) (T (Lp.const 2 μ v))‖ ≤
        ‖Lp.const 2 μ v‖ * ‖T (Lp.const 2 μ v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖Lp.const 2 μ v‖ * (‖T‖ * ‖Lp.const 2 μ v‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖T‖ := by simp [hc]

theorem tendsto_constant_vector_state {ι : Type*} {l : Filter ι}
    (T : ι → Lp E 2 μ →L[ℂ] Lp E 2 μ) (S : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (h : ∀ ξ, Tendsto (fun i => T i ξ) l (𝓝 (S ξ))) (v : E) :
    Tendsto (fun i => inner ℂ (Lp.const 2 μ v) (T i (Lp.const 2 μ v))) l
      (𝓝 (inner ℂ (Lp.const 2 μ v) (S (Lp.const 2 μ v)))) := by
  exact tendsto_const_nhds.inner (h (Lp.const 2 μ v))

end Invariant233.FieldTraceCyclic

end OAI
