import OAI.NumberTheory.TwoPoint.Bounds.RoughFourier
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

/-!
# The low/high Fourier split

The short-sum bound is uniform at a fixed frequency. It is applied after
summing the origins, and no supremum is moved through an integral.
-/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

private lemma circle_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : AddCircle (1 : ℝ) → E) (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma circle_integral_mul_norm_le (F G : AddCircle (1 : ℝ) → ℂ)
    (hF : Continuous F) (hG : Continuous G) :
    (∫ θ, ‖F θ‖ * ‖G θ‖ ∂AddCircle.haarAddCircle) ≤
      Real.sqrt (∫ θ, ‖F θ‖ ^ 2 ∂AddCircle.haarAddCircle) *
        Real.sqrt (∫ θ, ‖G θ‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  have hf : MemLp F (ENNReal.ofReal (2 : ℝ)) AddCircle.haarAddCircle :=
    hF.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : MemLp G (ENNReal.ofReal (2 : ℝ)) AddCircle.haarAddCircle :=
    hG.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff]) hf hg
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using hh

private lemma fourier_pointwise_split {ι : Type*} (S : Finset ι)
    (B : AddCircle (1 : ℝ) → ℂ) (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (ε Bmax Gmax K : ℝ) (hε : 0 < ε)
    (hBmax : 0 ≤ Bmax) (hGmax : 0 ≤ Gmax) (hK : 0 ≤ K)
    (hBbound : ∀ θ, ‖B θ‖ ≤ Bmax)
    (hGbound : ∀ v ∈ S, ∀ θ, ‖G v θ‖ ≤ Gmax)
    (hFsum : ∀ θ, (∑ v ∈ S, ‖F v θ‖) ≤ K) (θ : AddCircle (1 : ℝ)) :
    (∑ v ∈ S, ‖B θ‖ * ‖F v θ‖ * ‖G v θ‖) ≤
      ε * (∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖) +
        (Bmax * Gmax * K / ε ^ 4) * ‖B θ‖ ^ 4 := by
  let A (θ : AddCircle (1 : ℝ)) := ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖
  let C : ℝ := Bmax * Gmax * K / ε ^ 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  by_cases ht : ‖B θ‖ ≤ ε
  · calc
      _ ≤ ∑ v ∈ S, ε * (‖F v θ‖ * ‖G v θ‖) := by
        apply sum_le_sum
        intro v _
        calc
          _ = ‖B θ‖ * (‖F v θ‖ * ‖G v θ‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right ht
            (mul_nonneg (norm_nonneg (F v θ)) (norm_nonneg (G v θ)))
      _ = ε * A θ := by simp only [A, mul_sum]
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hC (by positivity))
  · have hs : (∑ v ∈ S, ‖B θ‖ * ‖F v θ‖ * ‖G v θ‖) ≤ Bmax * Gmax * K := by
      calc
        _ ≤ ∑ v ∈ S, Bmax * Gmax * ‖F v θ‖ := by
          apply sum_le_sum
          intro v hv
          have hh := mul_le_mul (hBbound θ) (hGbound v hv θ)
            (norm_nonneg _) hBmax
          calc
            _ = (‖B θ‖ * ‖G v θ‖) * ‖F v θ‖ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hh (norm_nonneg (F v θ))
        _ = Bmax * Gmax * ∑ v ∈ S, ‖F v θ‖ := (mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hFsum θ) (mul_nonneg hBmax hGmax)
    have hp : ε ^ 4 ≤ ‖B θ‖ ^ 4 :=
      pow_le_pow_left₀ hε.le (le_of_lt (lt_of_not_ge ht)) 4
    have hc : Bmax * Gmax * K ≤ C * ‖B θ‖ ^ 4 := by
      dsimp [C]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (pow_pos hε 4)).mpr
      exact mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hBmax hGmax) hK)
    exact hs.trans (hc.trans (le_add_of_nonneg_left (mul_nonneg hε.le
      (sum_nonneg (fun v _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))))))


private lemma norm_sum_circle_integral_le {ι : Type*} (S : Finset ι)
    (U : ι → AddCircle (1 : ℝ) → ℂ) (hU : ∀ v ∈ S, Continuous (U v)) :
    ‖∑ v ∈ S, ∫ θ, U v θ ∂AddCircle.haarAddCircle‖ ≤
      ∫ θ, ∑ v ∈ S, ‖U v θ‖ ∂AddCircle.haarAddCircle := by
  calc
    _ ≤ ∑ v ∈ S, ‖∫ θ, U v θ ∂AddCircle.haarAddCircle‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ S, ∫ θ, ‖U v θ‖ ∂AddCircle.haarAddCircle := by
      exact sum_le_sum (fun v _ => norm_integral_le_integral_norm (U v))
    _ = _ := by
      rw [integral_finsetSum S (f := fun v θ => ‖U v θ‖)
        (fun v hv => (circle_integrable (U v) (hU v hv)).norm)]

private lemma circle_integral_sum_mul_norm_le {ι : Type*} (S : Finset ι)
    (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (hF : ∀ v ∈ S, Continuous (F v)) (hG : ∀ v ∈ S, Continuous (G v)) :
    (∫ θ, ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖ ∂AddCircle.haarAddCircle) ≤
      ∑ v ∈ S, Real.sqrt (∫ θ, ‖F v θ‖ ^ 2 ∂AddCircle.haarAddCircle) *
        Real.sqrt (∫ θ, ‖G v θ‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  rw [integral_finsetSum S (f := fun v θ => ‖F v θ‖ * ‖G v θ‖)
    (fun v hv => circle_integrable _ ((hF v hv).norm.mul (hG v hv).norm))]
  exact sum_le_sum (fun v hv => circle_integral_mul_norm_le _ _ (hF v hv) (hG v hv))

private lemma circle_integral_linear_bound
    (P A B : AddCircle (1 : ℝ) → ℝ) (hP : Continuous P) (hA : Continuous A)
    (hB : Continuous B) (ε C : ℝ) (hpoint : ∀ θ, P θ ≤ ε * A θ + C * B θ) :
    (∫ θ, P θ ∂AddCircle.haarAddCircle) ≤
      ε * (∫ θ, A θ ∂AddCircle.haarAddCircle) +
        C * ∫ θ, B θ ∂AddCircle.haarAddCircle := by
  have hl : Integrable (fun θ => ε * A θ) AddCircle.haarAddCircle :=
    (circle_integrable _ hA).const_mul _
  have hr : Integrable (fun θ => C * B θ) AddCircle.haarAddCircle :=
    (circle_integrable _ hB).const_mul _
  calc
    _ ≤ ∫ θ, ε * A θ + C * B θ ∂AddCircle.haarAddCircle :=
      integral_mono (circle_integrable _ hP) (hl.add hr) hpoint
    _ = _ := by rw [integral_add hl hr, integral_const_mul, integral_const_mul]

private lemma circle_integrate_pointwise_split {ι : Type*} (S : Finset ι)
    (B : AddCircle (1 : ℝ) → ℂ) (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (hB : Continuous B) (hF : ∀ v ∈ S, Continuous (F v))
    (hG : ∀ v ∈ S, Continuous (G v)) (ε C : ℝ)
    (hpoint : ∀ θ, (∑ v ∈ S, ‖B θ‖ * ‖F v θ‖ * ‖G v θ‖) ≤
      ε * (∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖) + C * ‖B θ‖ ^ 4) :
    ‖∑ v ∈ S, ∫ θ, B θ * F v θ * G v θ ∂AddCircle.haarAddCircle‖ ≤
      ε * (∫ θ, ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖ ∂AddCircle.haarAddCircle) +
        C * ∫ θ, ‖B θ‖ ^ 4 ∂AddCircle.haarAddCircle := by
  have hnorm := norm_sum_circle_integral_le S
    (fun v θ => B θ * F v θ * G v θ)
    (fun v hv => (hB.mul (hF v hv)).mul (hG v hv))
  apply hnorm.trans
  apply circle_integral_linear_bound
    (fun θ => ∑ v ∈ S, ‖B θ * F v θ * G v θ‖)
    (fun θ => ∑ v ∈ S, ‖F v θ‖ * ‖G v θ‖)
    (fun θ => ‖B θ‖ ^ 4)
    (continuous_finsetSum S (fun v hv => ((hB.mul (hF v hv)).mul (hG v hv)).norm))
    (continuous_finsetSum S (fun v hv => (hF v hv).norm.mul (hG v hv).norm))
    (hB.norm.pow 4) ε C
  intro θ
  simpa only [norm_mul] using hpoint θ

/-- A finite-family version of the analytic split. The threshold term uses
only Cauchy--Schwarz; the complementary term uses the fourth moment and
our fixed-frequency sum over origins. -/
theorem fourier_region_bound {ι : Type*} (S : Finset ι)
    (B : AddCircle (1 : ℝ) → ℂ) (F G : ι → AddCircle (1 : ℝ) → ℂ)
    (hB : Continuous B) (hF : ∀ v ∈ S, Continuous (F v))
    (hG : ∀ v ∈ S, Continuous (G v))
    (ε Bmax Gmax K : ℝ) (hε : 0 < ε)
    (hBmax : 0 ≤ Bmax) (hGmax : 0 ≤ Gmax) (hK : 0 ≤ K)
    (hBbound : ∀ θ, ‖B θ‖ ≤ Bmax)
    (hGbound : ∀ v ∈ S, ∀ θ, ‖G v θ‖ ≤ Gmax)
    (hFsum : ∀ θ, (∑ v ∈ S, ‖F v θ‖) ≤ K) :
    ‖∑ v ∈ S, ∫ θ, B θ * F v θ * G v θ ∂AddCircle.haarAddCircle‖ ≤
      ε * ∑ v ∈ S,
        Real.sqrt (∫ θ, ‖F v θ‖ ^ 2 ∂AddCircle.haarAddCircle) *
          Real.sqrt (∫ θ, ‖G v θ‖ ^ 2 ∂AddCircle.haarAddCircle) +
      (Bmax * Gmax * K / ε ^ 4) *
        ∫ θ, ‖B θ‖ ^ 4 ∂AddCircle.haarAddCircle := by
  apply (circle_integrate_pointwise_split S B F G hB hF hG ε
    (Bmax * Gmax * K / ε ^ 4)
    (fourier_pointwise_split S B F G ε Bmax Gmax K hε hBmax hGmax hK
      hBbound hGbound hFsum)).trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    (circle_integral_sum_mul_norm_le S F G hF hG) hε.le) le_rfl

end TwoPointCorrelations

end OAI
