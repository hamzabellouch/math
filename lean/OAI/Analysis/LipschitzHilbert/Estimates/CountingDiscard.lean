import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# The cost of discarding the counting exceptional set

This proves §6 `count:discard-cost` from the actual restricted integral,
the ordinary model's L² estimate, and the exceptional-set area budget.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

/-- Cauchy–Schwarz on a finite-measure set, with the L² energy taken on
the whole space. In particular the restricted norm integral exists. -/
theorem integral_norm_on_set_le_l2 (μ : Measure X) (P : X → V)
    (hP : MemLp P 2 μ) {A : Set X} (hA : μ A ≠ ∞) :
    IntegrableOn (fun x => ‖P x‖) A μ ∧
      (∫ x in A, ‖P x‖ ∂μ) ≤
        Real.sqrt (∫ x, ‖P x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA
  have hnorm : MemLp (fun x => ‖P x‖) 2 (μ.restrict A) := (hP.restrict A).norm
  have hone : MemLp (fun _ : X => (1 : ℝ)) 2 (μ.restrict A) := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict A)
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall fun x => norm_nonneg (P x))
    (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1))
    (by simpa using hnorm) (by simpa using hone)
  have hsq : (∫ x in A, ‖P x‖ ^ 2 ∂μ) ≤ ∫ x, ‖P x‖ ^ 2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hP.norm.integrable_sq)
  have hh' : (∫ x in A, ‖P x‖ ∂μ) ≤
      Real.sqrt (∫ x in A, ‖P x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
    simpa only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul,
      mul_one, measureReal_restrict_apply_univ, ← Real.sqrt_eq_rpow] using hh
  exact ⟨hnorm.integrable (by norm_num), hh'.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _))⟩

theorem sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

/-- The L² model estimate and the area budget give the exponentially
small discarded integral with its exact square-root loss. -/
theorem counting_discard_from_area (μ : Measure X) (P : X → V)
    (hP : MemLp P 2 μ) {A E : Set X} (hA : μ A ≠ ∞)
    {K B J L : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hmodel : (∫ x, ‖P x‖ ^ 2 ∂μ) ≤ K ^ 2 * μ.real E)
    (harea : μ.real A ≤ B * μ.real E * Real.exp (-J * L)) :
    IntegrableOn (fun x => ‖P x‖) A μ ∧
      (∫ x in A, ‖P x‖ ∂μ) ≤ K * Real.sqrt B * μ.real E * Real.exp (-J * L / 2) := by
  obtain ⟨hi, hcs⟩ := integral_norm_on_set_le_l2 μ P hP hA
  refine ⟨hi, hcs.trans ?_⟩
  have he : 0 ≤ μ.real E := measureReal_nonneg
  calc
    Real.sqrt (∫ x, ‖P x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) ≤
        Real.sqrt (K ^ 2 * μ.real E) *
          Real.sqrt (B * μ.real E * Real.exp (-J * L)) :=
      mul_le_mul (Real.sqrt_le_sqrt hmodel) (Real.sqrt_le_sqrt harea)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = K * Real.sqrt B * μ.real E * Real.exp (-J * L / 2) := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK,
        Real.sqrt_mul (mul_nonneg hB he), Real.sqrt_mul hB, sqrt_exp_half]
      calc
        _ = K * Real.sqrt B * (Real.sqrt (μ.real E) * Real.sqrt (μ.real E)) *
            Real.exp (-J * L / 2) := by ring
        _ = _ := by rw [Real.mul_self_sqrt he]

/-- Converting `|E|=N²|F|` and `N≤exp(2L)` gives the precise exponent
`(2-J/2)L` in the source discard estimate. -/
theorem counting_discard_cost (μ : Measure X) (P : X → V)
    (hP : MemLp P 2 μ) {A E F : Set X} (hA : μ A ≠ ∞)
    {K B J L N : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hratio : μ.real E = N ^ 2 * μ.real F) (hNlarge : N ≤ Real.exp (2 * L))
    (hmodel : (∫ x, ‖P x‖ ^ 2 ∂μ) ≤ K ^ 2 * μ.real E)
    (harea : μ.real A ≤ B * μ.real E * Real.exp (-J * L)) :
    IntegrableOn (fun x => ‖P x‖) A μ ∧
      (∫ x in A, ‖P x‖ ∂μ) ≤
        (K * Real.sqrt B) * Real.exp ((2 - J / 2) * L) * N * μ.real F := by
  obtain ⟨hi, hdiscard⟩ := counting_discard_from_area μ P hP hA hK hB hmodel harea
  refine ⟨hi, hdiscard.trans ?_⟩
  rw [hratio]
  have hNmul : N ^ 2 ≤ Real.exp (2 * L) * N := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hNlarge hN
  have hweight : 0 ≤ (K * Real.sqrt B) * μ.real F * Real.exp (-J * L / 2) := by positivity
  have h := mul_le_mul_of_nonneg_right hNmul hweight
  have hexp : Real.exp (2 * L) * Real.exp (-J * L / 2) =
      Real.exp ((2 - J / 2) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    K * Real.sqrt B * (N ^ 2 * μ.real F) * Real.exp (-J * L / 2) ≤
        (Real.exp (2 * L) * N) *
          ((K * Real.sqrt B) * μ.real F * Real.exp (-J * L / 2)) := by
      convert h using 1
      ring
    _ = _ := by rw [show (Real.exp (2 * L) * N) *
          ((K * Real.sqrt B) * μ.real F * Real.exp (-J * L / 2)) =
        (K * Real.sqrt B) * (Real.exp (2 * L) * Real.exp (-J * L / 2)) * N * μ.real F by ring,
      hexp]

end LipschitzHilbert

end

end OAI
