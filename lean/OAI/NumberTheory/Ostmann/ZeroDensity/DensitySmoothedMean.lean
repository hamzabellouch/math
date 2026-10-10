import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPartialMean
import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareLimit
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFatou

namespace OAI

/-! # The actual smoothed square satisfies the sixth-log mean bound -/

namespace Ostmann

open Complex MeasureTheory Filter Set
open scoped BigOperators Topology Classical

 theorem densitySmoothedSquare_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ,
      1 ≤ T → 1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∀ χ ∈ F, Integrable (fun t =>
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2)
          (volume.restrict (Icc (-T) T))) ∧
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_partial_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hN hQ T hT hL hscale F hF
  let p := fun (J : ℕ) (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ‖∑ n ∈ Finset.Icc 1 (2 ^ J * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2
  let f := fun (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2
  have hp (J : ℕ) (χ : PrimitiveComplexCharacter) :
      Integrable (p J χ) (volume.restrict (Icc (-T) T)) :=
    ((densityFiniteSquare_continuousOn χ _ (fun n hn => (Finset.mem_Icc.mp hn).1) T hT).norm.pow 2).integrableOn_Icc
  have ht (χ : PrimitiveComplexCharacter) (t : ℝ) :
      Tendsto (fun J => p J χ t) atTop (𝓝 (f χ t)) :=
    ((densitySquare_partial_limit χ N hN t).norm).pow 2
  have hsum : Integrable (fun t => ∑ χ ∈ F, f χ t) (volume.restrict (Icc (-T) T)) ∧
      (∫ t in Icc (-T) T, ∑ χ ∈ F, f χ t) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
    apply density_integral_limit_bound (fun J t => ∑ χ ∈ F, p J χ t)
      (fun t => ∑ χ ∈ F, f χ t) _ _ (by positivity)
    · intro J
      exact integrable_finsetSum F (fun χ _ => hp J χ)
    · intro J t
      exact Finset.sum_nonneg (fun χ _ => sq_nonneg _)
    · intro t
      exact tendsto_finsetSum F (fun χ _ => ht χ t)
    · intro J
      rw [integral_finsetSum F (fun χ _ => hp J χ)]
      exact hb N Q hN hQ T hT hL hscale J F hF
  have hi (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      Integrable (f χ) (volume.restrict (Icc (-T) T)) := by
    apply hsum.1.mono'
    · exact aestronglyMeasurable_of_tendsto_ae atTop (fun J => (hp J χ).aestronglyMeasurable)
        (Filter.Eventually.of_forall (ht χ))
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact Finset.single_le_sum (f := fun ψ => f ψ t) (fun ψ _ => sq_nonneg _) hχ
  refine ⟨hi, ?_⟩
  simpa only [integral_finsetSum F hi] using hsum.2

end Ostmann

end OAI
