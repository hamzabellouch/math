import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Ising.CopyEnergyIntegrability
import OAI.Probability.FreeIsing.Ising.CopyResponseRowSummability
import OAI.Probability.FreeIsing.Ising.CopyShellEnergies
import OAI.Probability.FreeIsing.Trees.WeightedShellSummation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity IsingConditionalCopyBounds ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem actual_density_eq_path_density_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (t : ℝ≥0) :
    IsingCopyEnergy.density beta (root d) t =ᵐ[copies beta μ]
      DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
        (fun v q => row beta t v q.2.2) (fieldDifference beta (root d) t)
        (fun q => Real.tanh (field beta (root d) t q.2.1))
        (fun q => Real.tanh (field beta (root d) t q.2.2)) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have heq := tanh_field_eq_posterior_ae hμ hb (root d) t
  filter_upwards [hl.quasiMeasurePreserving.ae heq, hr.quasiMeasurePreserving.ae heq] with q hql hqr
  simp only [IsingCopyEnergy.density, IsingCopyEnergy.responseRow, Real.toNNReal_coe,
    DiscrepancyEnergy.density, row, fieldDifference, hql, hqr]
  rfl

theorem integral_actual_density_le_path_sums
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (hQ : Summable (noiseShellEnergy (μ := μ) hb t))
    (hL : Summable (linearShellEnergy (μ := μ) hb t))
    (hZ : Summable (fun n => Real.sqrt (noiseShellEnergy (μ := μ) hb t n))) :
    Integrable (IsingCopyEnergy.density beta (root d) t) (copies beta μ) ∧
    (∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) ≤
      (2 + 8 * ((d : ℝ) * Real.tanh beta ^ 2)) *
        ((∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) +
          (∑' n, noiseShellEnergy (μ := μ) hb t n) +
          (∑' n, linearShellEnergy (μ := μ) hb t n) +
          Real.sqrt (∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) *
            (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n))) := by
  have hQ0 (n : ℕ) : 0 ≤ noiseShellEnergy (μ := μ) hb t n := nonnegativeShellSup_nonneg _ _
  have hL0 (n : ℕ) : 0 ≤ linearShellEnergy (μ := μ) hb t n := nonnegativeShellSup_nonneg _ _
  have hsQ := (summable_and_tsum_shell_le_path hcrit hQ0 hQ).1
  have hsL := (summable_and_tsum_shell_le_path hcrit hL0 hL).1
  have hsZ := (summable_and_tsum_shell_le_path hcrit (fun _ => Real.sqrt_nonneg _) hZ).1
  have hmain := integral_density_le_shell_energies_of_positive hμ hb ht hcrit
    (fun n => hQ0 (n + 1)) (fun n => hL0 (n + 1))
    (fun n v hv => by
      have h := le_nonnegativeShellSup (noiseEnergy (μ := μ) hb t) v
      simpa only [hv, noiseShellEnergy] using h)
    (fun n v hv => by
      have h := le_nonnegativeShellSup (linearEnergy (μ := μ) hb t) v
      simpa only [hv, linearShellEnergy] using h) hsQ hsL hsZ
  have heq := actual_density_eq_path_density_ae hμ hb t
  refine ⟨hmain.1.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact hmain.2.trans (shell_noise_drift_le_path_sums hcrit
    (integral_nonneg (fun _ => sq_nonneg _)) hQ0 hL0 hQ hL hZ)

theorem exists_actual_spatial_endpoint_constant
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1))
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w → 0 < t →
      let S := ∫ z, (cavityLogDifference hb t u w z) ^ 2 ∂copies beta μ
      let V := ∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ
      ∀ (K ω : ℝ), 0 < V → V ≤ K → 1 ≤ K → 0 < ω → ω ≤ 1 →
      (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤ B * S *
          ((v.1.length : ℝ) * Real.exp (-(c * ω) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) →
      (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
        linearEnergy (μ := μ) hb t v ≤ B * V * Real.exp (-(c * ω) * v.1.length) +
          E * Real.exp (-a * q ^ v.1.length)) →
      CriticalSpatialEndpointBounds
        (∫ z, IsingCopyEnergy.density beta (root d) t z ∂copies beta μ)
        (∑' n, noiseShellEnergy (μ := μ) hb t n)
        (∑' n, linearShellEnergy (μ := μ) hb t n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n)) S V M K ω := by
  obtain ⟨A, hA, hshort⟩ := exists_short_shell_energy_bounds hμ hd hb hcrit
  let N := max (cavityLogVarianceCoefficient (Real.tanh beta))
    (2 + 8 * ((d : ℝ) * Real.tanh beta ^ 2))
  obtain ⟨M, hM, hendpoint⟩ := exists_spatial_endpoint_constant_of_path_estimates
    (N := N) (C₀ := C₀) (zero_le_one.trans hA) hB hE hc ha hq
  refine ⟨M, hM, ?_⟩
  intro t u w huw ht
  dsimp only
  intro K ω hV hVK hK hω hω1 hlongQ hlongL
  let S := ∫ z, (cavityLogDifference hb t u w z) ^ 2 ∂copies beta μ
  let V := ∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ
  have hS : 0 ≤ S := integral_nonneg (fun _ => sq_nonneg _)
  have hV0 : 0 ≤ V := integral_nonneg (fun _ => sq_nonneg _)
  have hpaths : WeightedPathEstimates (noiseShellEnergy (μ := μ) hb t)
      (linearShellEnergy (μ := μ) hb t) A B E c a q C₀ S V ω := by
    refine ⟨fun _ => nonnegativeShellSup_nonneg _ _, fun _ => nonnegativeShellSup_nonneg _ _,
      fun n => (hshort t u w huw n).1, fun n => (hshort t u w huw n).2, ?_, ?_⟩
    · intro n hn
      apply nonnegativeShellSup_le (by positivity)
      intro v hv
      simpa only [hv] using hlongQ v (by simpa only [hv] using hn)
    · intro n hn
      apply nonnegativeShellSup_le (by positivity)
      intro v hv
      simpa only [hv] using hlongL v (by simpa only [hv] using hn)
  have hSV : S ≤ N * V := by
    have h := norm_cavityLogDifference_sq_le hμ hb t (root d) u w
    rw [norm_observableDifference_sq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hV0)
  obtain ⟨hsQ, hsL, hsZ⟩ := hpaths.summable hB hE hS hc ha hq hω
  have hbranch : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 := by
    have h := (tanh_threshold_iff_branching_sq hd hb).mp hcrit
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using h
  have hD := (integral_actual_density_le_path_sums hμ hb ht hbranch hsQ hsL hsZ).2
  apply hendpoint hpaths hS hSV hV hVK hK hω hω1
  apply hD.trans
  apply mul_le_mul_of_nonneg_right (le_max_right _ _)
  exact add_nonneg (add_nonneg (add_nonneg hV0
    (tsum_nonneg hpaths.noise_nonneg)) (tsum_nonneg hpaths.linear_nonneg))
    (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg (fun _ => Real.sqrt_nonneg _)))

end Problem367.IsingCopyResponseRowPaths

end

end OAI
