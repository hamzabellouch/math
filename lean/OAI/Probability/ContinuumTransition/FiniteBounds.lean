import OAI.Probability.ContinuumTransition.GrandPartition

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem log_factorial_lower (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
    have hh := Real.pow_div_factorial_le_exp (N : ℝ) hpos.le N
    have hl := Real.log_le_log (div_pos (pow_pos hpos _) hf) hh
    rw [Real.log_div (pow_ne_zero _ hpos.ne') hf.ne', Real.log_pow, Real.log_exp] at hl
    linarith

theorem boltzmann_le_of_energy_lower {φ : ℝ → ℝ} {β E : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} {x : Fin N → Space} (hE : (E : EReal) ≤ energy φ x) :
    boltzmann φ β x ≤ Real.exp (-β * E) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal hE (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    exact mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hβ)

theorem partition_le_factorial_of_energy_bound {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    partition φ β L N ≤ (L ^ 3) ^ N / (N.factorial : ℝ) * Real.exp (-β * E) := by
  let S := {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hS : MeasurableSet S := (isCompact_configurations L N).measurableSet
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
  have hh : ∀ᵐ x ∂volume.restrict S, boltzmann φ β x ≤ Real.exp (-β * E) := by
    apply (ae_restrict_iff' hS).mpr
    exact ae_of_all _ (fun x hx => boltzmann_le_of_energy_lower hβ (hE x hx))
  have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
    (integrable_const (Real.exp (-β * E))) hh
  have hc : (∫ x in S, Real.exp (-β * E)) = L ^ (3 * N) * Real.exp (-β * E) := by
    rw [setIntegral_const, Measure.real, volume_configurations, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hL, smul_eq_mul]
  rw [hc] at hi
  unfold partition
  rw [ite_eq_right hN]
  calc
    _ ≤ (1 / (N.factorial : ℝ)) * (L ^ (3 * N) * Real.exp (-β * E)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [pow_mul]; ring

theorem neg_log_partition_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    β * E + N * Real.log ((N : ℝ) / L ^ 3) - N ≤ -Real.log (partition φ β L N) := by
  have hnpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hfp : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hLp : 0 < L ^ 3 := pow_pos hL _
  have hZ := partition_pos hφ hβ hL hstable N
  have hu := partition_le_factorial_of_energy_bound hφ hβ hL.le hstable hN hE
  have hl := Real.log_le_log hZ hu
  rw [Real.log_mul (div_pos (pow_pos hLp _) hfp).ne' (Real.exp_pos _).ne',
    Real.log_div (pow_pos hLp _).ne' hfp.ne', Real.log_pow, Real.log_exp] at hl
  rw [Real.log_div hnpos.ne' hLp.ne']
  have hf := log_factorial_lower N
  nlinarith

end ContinuumTemperature
end

end OAI
