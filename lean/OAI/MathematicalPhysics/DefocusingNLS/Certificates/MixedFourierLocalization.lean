import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevWeights
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! # The mixed Fourier estimate used by torus localization

The localization kernel sends lattice coefficients to a continuous Fourier
variable. A finite Schur estimate gives the required ℓ²-to-L² bound; its
constants are the uniform periodized L¹ bound and the ordinary L¹ norm of
the kernel. No localization bound is assumed.
-/

open MeasureTheory

namespace DefocusingNLS

/-- Weighted Cauchy--Schwarz for the finite mixed Fourier sum. -/
theorem mixedFourier_pointwise_bound (S : Finset frequencyLattice)
    (v : frequencyLattice → ℂ)
    (K : EuclideanSpace ℝ (Fin 12) → ℂ)
    (x : EuclideanSpace ℝ (Fin 12)) (C : ℝ)
    (hK : ∑ n ∈ S, ‖K (x - n)‖ ≤ C) :
    ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2 ≤
      C * ∑ n ∈ S, ‖v n‖ ^ 2 * ‖K (x - n)‖ := by
  have hn : ‖∑ n ∈ S, v n * K (x - n)‖ ≤
      ∑ n ∈ S, ‖v n‖ * ‖K (x - n)‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun n => v n * K (x - n))
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := fun n => ‖v n‖ * ‖K (x - n)‖)
    (f := fun n => ‖v n‖ ^ 2 * ‖K (x - n)‖)
    (g := fun n => ‖K (x - n)‖)
    (fun n _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))
    (fun n _ => norm_nonneg _) (fun n _ => le_of_eq (by ring))
  have hsum : 0 ≤ ∑ n ∈ S, ‖v n‖ * ‖K (x - n)‖ :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsum2 : 0 ≤ ∑ n ∈ S, ‖v n‖ ^ 2 * ‖K (x - n)‖ :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))
  calc
    _ ≤ (∑ n ∈ S, ‖v n‖ * ‖K (x - n)‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ n ∈ S, v n * K (x - n))]
    _ ≤ (∑ n ∈ S, ‖v n‖ ^ 2 * ‖K (x - n)‖) * ∑ n ∈ S, ‖K (x - n)‖ := hcs
    _ ≤ (∑ n ∈ S, ‖v n‖ ^ 2 * ‖K (x - n)‖) * C :=
      mul_le_mul_of_nonneg_left hK hsum2
    _ = _ := mul_comm _ _

/-- The mixed lattice-to-continuum Fourier kernel is bounded on finite sums.
The bound is independent of the finite frequency set. -/
theorem mixedFourier_integral_bound (S : Finset frequencyLattice)
    (v : frequencyLattice → ℂ)
    (K : EuclideanSpace ℝ (Fin 12) → ℂ) (hK : Integrable K)
    (C : ℝ) (_hC : 0 ≤ C)
    (hperiod : ∀ x, ∑ n ∈ S, ‖K (x - n)‖ ≤ C) :
    Integrable (fun x => ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) ∧
      (∫ x, ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) ≤
        C * (∫ x, ‖K x‖) * ∑ n ∈ S, ‖v n‖ ^ 2 := by
  have hfin : Integrable (fun x => ∑ n ∈ S, v n * K (x - n)) := by
    apply integrable_finsetSum
    intro n _
    exact (hK.comp_sub_right (n : EuclideanSpace ℝ (Fin 12))).const_mul (v n)
  have hterm (n : frequencyLattice) : Integrable (fun x => ‖v n‖ ^ 2 * ‖K (x - n)‖) :=
    ((hK.comp_sub_right (n : EuclideanSpace ℝ (Fin 12))).norm).const_mul _
  have hmajor : Integrable (fun x => C * ∑ n ∈ S, ‖v n‖ ^ 2 * ‖K (x - n)‖) :=
    (integrable_finsetSum S (fun n _ => hterm n)).const_mul C
  have hpoint := mixedFourier_pointwise_bound S v K
  have hsq : Integrable (fun x => ‖∑ n ∈ S, v n * K (x - n)‖ ^ 2) := by
    apply hmajor.mono' (hfin.norm.aestronglyMeasurable.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x C (hperiod x)
  refine ⟨hsq, (integral_mono hsq hmajor (fun x =>
    hpoint x C (hperiod x))).trans_eq ?_⟩
  rw [integral_const_mul, integral_finsetSum S (fun n _ => hterm n)]
  simp only [integral_const_mul]
  simp_rw [show ∀ n : frequencyLattice,
      (∫ x, ‖K (x - n)‖) = ∫ x, ‖K x‖ from
    fun n => integral_sub_right_eq_self (fun x => ‖K x‖) n]
  rw [← Finset.sum_mul]
  ring

end DefocusingNLS

end OAI
