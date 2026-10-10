import OAI.NumberTheory.Ostmann.Arithmetic.BulkPrimeIntegrands
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Atomic log measures of the original harmonic prime subsets -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def primeSubsetLogMeasure (S : Finset ℕ) (Z : ℝ) : Measure ℝ :=
  ENNReal.ofReal Z • ∑ p ∈ S, ENNReal.ofReal ((p : ℝ)⁻¹) • Measure.dirac (Real.log p)

instance finite_primeSubsetLogMeasure (S : Finset ℕ) (Z : ℝ) :
    IsFiniteMeasure (primeSubsetLogMeasure S Z) := by
  unfold primeSubsetLogMeasure
  exact (∑ p ∈ S, ENNReal.ofReal ((p : ℝ)⁻¹) • Measure.dirac (Real.log p)).smul_finite
    ENNReal.ofReal_ne_top

theorem BulkIntegrand.average_primeSubset {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (S : Finset ℕ) (Z : ℝ) (hZ : 0 ≤ Z) (i : σ) (x : σ → ℝ) :
    f.average (primeSubsetLogMeasure S Z) i x =
      (Z : ℂ) * ∑ p ∈ S, f (Function.update x i (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) := by
  change (∫ t, f (Function.update x i t) ∂primeSubsetLogMeasure S Z) = _
  rw [primeSubsetLogMeasure, integral_smul_measure, ENNReal.toReal_ofReal hZ,
    integral_finsetSum_measure]
  · congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul, mul_comm]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  · intro p _
    exact f.slice_integrable _ i x

/-- This is the literal original finite prior, with its own normalization;
no replacement by a uniformly distributed prime is made. -/
theorem BulkIntegrand.average_originalPrimePrior {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (P S : Finset ℕ) (hSP : S ⊆ P) (i : σ) (x : σ → ℝ) :
    f.average (primeSubsetLogMeasure S (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹) i x =
      ∑ p : P, (primeSubsetPrior P S p : ℂ) * f (Function.update x i (Real.log (p : ℕ))) := by
  rw [f.average_primeSubset S _ (inv_nonneg.mpr (Finset.sum_nonneg fun p _ => by positivity)),
    primeSubsetPrior_mean P S hSP (fun p => f (Function.update x i (Real.log p)))]
  simp only [Complex.ofReal_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact mul_comm _ _

/-- Removing the prescribed exceptional primes costs their actual harmonic
mass, while retaining the supplied normalization constant. -/
theorem BulkIntegrand.primeSubset_deletion_bound {σ : Type*} [Fintype σ]
    (f : BulkIntegrand σ) (S D : Finset ℕ) (Z C : ℝ) (hZ : 0 ≤ Z)
    (hF : ∀ x, ‖f x‖ ≤ C) (i : σ) (x : σ → ℝ) :
    ‖f.average (primeSubsetLogMeasure S Z) i x -
      f.average (primeSubsetLogMeasure (S \ D) Z) i x‖ ≤
        Z * C * ∑ p ∈ S ∩ D, (p : ℝ)⁻¹ := by
  let g := fun p : ℕ => f (Function.update x i (Real.log p)) * ((p : ℝ)⁻¹ : ℂ)
  have he : (∑ p ∈ S, g p) - (∑ p ∈ S \ D, g p) = ∑ p ∈ S ∩ D, g p := by
    have h := Finset.sum_inter_add_sum_sdiff S D g
    exact sub_eq_iff_eq_add.mpr h.symm
  rw [f.average_primeSubset S Z hZ, f.average_primeSubset (S \ D) Z hZ, ← mul_sub, he,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hZ]
  calc
    _ ≤ Z * ∑ p ∈ S ∩ D, C * (p : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hZ
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      change ‖f _ * _‖ ≤ _
      rw [norm_mul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ (p : ℝ)⁻¹)]
      exact mul_le_mul_of_nonneg_right (hF _) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

end Ostmann

end OAI
