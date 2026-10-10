import OAI.Geometry.EinsteinFour.JacobiLogDetSeries
import OAI.Geometry.EinsteinFour.JacobiSeriesIntegral

namespace OAI

/-! The averaged logarithmic determinant estimate from the finite moments. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem expected_log_det_lower
    (H : Ω → Matrix ι ι ℝ) (C : Matrix κ κ ℝ) (hH : Continuous H)
    (hp : ∀ x, (H x).PosSemidef) (hI : ∀ x, (1 - H x).PosDef)
    (hC : C.PosSemidef) (hIC : (1 - C).PosDef)
    (hfirst : (∫ x, (H x).trace ∂μ) = C.trace)
    (hmoments : ∀ k : ℕ, (∫ x, (H x ^ (k + 2)).trace ∂μ) ≤
      (5 / 6 : ℝ) * (C ^ (k + 2)).trace) :
    (5 / 6 : ℝ) * Real.log (1 - C).det - C.trace / 6 ≤
      ∫ x, Real.log (1 - H x).det ∂μ := by
  let F := fun (n : ℕ) (x : Ω) => (H x ^ (n + 1)).trace / (n + 1)
  let S := fun x => -Real.log (1 - H x).det
  let g := fun n : ℕ => (5 / 6 : ℝ) * ((C ^ (n + 1)).trace / (n + 1)) +
    if n = 0 then C.trace / 6 else 0
  have hF (n : ℕ) : Integrable (F n) μ :=
    (((hH.pow (n + 1)).matrix_trace).div_const _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hS : Integrable S μ :=
    ((((continuous_const.sub hH).matrix_det).log
      (fun x => (hI x).det_pos.ne')).neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpos (n : ℕ) (x : Ω) : 0 ≤ F n x := by
    dsimp [F]
    rw [trace_pow_eq_sum_eigenvalues (hp x).isHermitian]
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => pow_nonneg ((hp x).eigenvalues_nonneg i) _)
    · positivity
  have hs (x : Ω) : HasSum (fun n => F n x) (S x) :=
    hasSum_trace_pow_neg_log_det (hp x) (hI x)
  have hg : HasSum g ((5 / 6 : ℝ) * (-Real.log (1 - C).det) + C.trace / 6) := by
    exact ((hasSum_trace_pow_neg_log_det hC hIC).mul_left (5 / 6)).add
      (hasSum_ite_eq 0 (C.trace / 6))
  have hb (n : ℕ) : (∫ x, F n x ∂μ) ≤ g n := by
    cases n with
    | zero =>
        simp only [F, g, zero_add, pow_one, Nat.cast_zero, div_one, ite_true]
        rw [hfirst]
        linarith
    | succ n =>
        dsimp only [F, g]
        rw [integral_div]
        have h := div_le_div_of_nonneg_right (hmoments n)
          (show (0 : ℝ) ≤ n + 2 by positivity)
        simp only [Nat.cast_add, Nat.cast_one,
          Nat.add_assoc, Nat.reduceAdd, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ite_false, add_zero]
        convert h using 1 <;> ring
  have h := integral_nonnegative_series_le F S g _ hF hS hpos hs hg hb
  change (∫ x, -Real.log (1 - H x).det ∂μ) ≤ _ at h
  rw [integral_neg] at h
  linarith

end
end PositiveEinsteinFour.Jacobi

end OAI
