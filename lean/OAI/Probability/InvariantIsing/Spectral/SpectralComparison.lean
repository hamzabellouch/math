import OAI.Probability.InvariantIsing.Spectral.SpectralCountComparison

namespace OAI

/-! Monotonicity and scalar shifts for the pointwise and mean pressures.
These are the finite-volume squeeze estimates used in spectral discretization. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma rotatedEnergy_mono {N : ℕ} (eig kap : Fin N → ℝ) (U : Rotation N)
    (h : ∀ i, eig i ≤ kap i) (σ : Spin N) :
    rotatedEnergy eig U σ ≤ rotatedEnergy kap U σ := by
  unfold rotatedEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

lemma rotatedPressure_mono {N : ℕ} (eig kap c : Fin N → ℝ) (U : Rotation N)
    (h : ∀ i, eig i ≤ kap i) :
    rotatedPressure eig U c ≤ rotatedPressure kap U c := by
  have hp := logPartition_le_add
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy kap U σ + fieldEnergy c σ) 0
    (fun σ => by simpa only [add_zero] using add_le_add (rotatedEnergy_mono eig kap U h σ) le_rfl)
  simpa only [rotatedPressure, add_zero] using
    mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg N))

lemma rotatedEnergy_add_scalar {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (a : ℝ) (σ : Spin N) :
    rotatedEnergy (fun i => eig i + a) U σ = rotatedEnergy eig U σ + a * N / 2 := by
  simp only [rotatedEnergy, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    rotated_spin_sq_sum]
  ring

lemma rotatedPressure_add_scalar {N : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N) (a : ℝ) :
    rotatedPressure (fun i => eig i + a) U c = rotatedPressure eig U c + a / 2 := by
  have he : (fun σ => rotatedEnergy (fun i => eig i + a) U σ + fieldEnergy c σ) =
      (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ + a * N / 2) := by
    funext σ
    rw [rotatedEnergy_add_scalar]
    ring
  rw [rotatedPressure, he, logPartition_add_const]
  unfold rotatedPressure
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma meanPressure_add_scalar {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (eig c : Fin N → ℝ) (a K : ℝ) (heig : ∀ i, |eig i| ≤ K) :
    (∫ U, rotatedPressure (fun i => eig i + a) (specialRotation U) c ∂μ) =
      (∫ U, rotatedPressure eig (specialRotation U) c ∂μ) + a / 2 := by
  simp_rw [rotatedPressure_add_scalar hN]
  rw [integral_add (integrable_countPressure hN μ eig c K heig) (integrable_const _)]
  simp

lemma meanPressure_squeeze {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (eig lo hi c : Fin N → ℝ) (δ K : ℝ)
    (heig : ∀ i, |eig i| ≤ K) (hlo : ∀ i, |lo i| ≤ K) (hhi : ∀ i, |hi i| ≤ K)
    (hl : ∀ i, lo i - δ ≤ eig i) (hu : ∀ i, eig i ≤ hi i + δ) :
    (∫ U, rotatedPressure lo (specialRotation U) c ∂μ) - δ / 2 ≤
      ∫ U, rotatedPressure eig (specialRotation U) c ∂μ ∧
    (∫ U, rotatedPressure eig (specialRotation U) c ∂μ) ≤
      (∫ U, rotatedPressure hi (specialRotation U) c ∂μ) + δ / 2 := by
  have hli : Integrable (fun U => rotatedPressure (fun i => lo i + -δ) (specialRotation U) c) μ := by
    simp_rw [rotatedPressure_add_scalar hN]
    exact (integrable_countPressure hN μ lo c K hlo).add (integrable_const _)
  have hui : Integrable (fun U => rotatedPressure (fun i => hi i + δ) (specialRotation U) c) μ := by
    simp_rw [rotatedPressure_add_scalar hN]
    exact (integrable_countPressure hN μ hi c K hhi).add (integrable_const _)
  have hei := integrable_countPressure hN μ eig c K heig
  have hlow := integral_mono hli hei (fun U =>
    rotatedPressure_mono _ _ c (specialRotation U) (fun i => by simpa only [sub_eq_add_neg] using hl i))
  have hupp := integral_mono hei hui (fun U => rotatedPressure_mono _ _ c (specialRotation U) hu)
  rw [meanPressure_add_scalar hN μ lo c (-δ) K hlo] at hlow
  rw [meanPressure_add_scalar hN μ hi c δ K hhi] at hupp
  exact ⟨by linarith, hupp⟩

end InvariantIsing

end

end OAI
