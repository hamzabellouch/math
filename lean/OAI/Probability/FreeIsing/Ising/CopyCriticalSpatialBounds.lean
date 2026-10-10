import OAI.Probability.FreeIsing.Ising.CopyLinearLongBound
import OAI.Probability.FreeIsing.Ising.CopySpatialEndpoints
import OAI.Probability.FreeIsing.Ising.CriticalSmallLogLoss

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

theorem path_decay_mono {c c' ω : ℝ} (hcc : c ≤ c') (hω : 0 ≤ ω) (n : ℕ) :
    Real.exp (-(c' * ω) * n) ≤ Real.exp (-(c * ω) * n) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcc hω) (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  nlinarith

theorem path_double_decay_mono {a a' q q' : ℝ}
    (ha : 0 ≤ a) (haa : a ≤ a') (hq : 0 ≤ q) (hqq : q ≤ q') (n : ℕ) :
    Real.exp (-a' * q' ^ n) ≤ Real.exp (-a * q ^ n) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul haa (pow_le_pow_left₀ hq hqq n)
    (pow_nonneg hq n) (ha.trans haa)
  nlinarith

namespace IsingCopyResponseRowPaths
open IsingObservationFactor IsingConditionalCopyBounds ConnectedHull
open IsingCopySmallLogLoss IsingCriticalSmallLogLoss

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_actual_spatial_endpoint_of_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * (logVariance hb μ u w t) *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (t : ℝ≥0), 0 < t → t ≤ T →
      ∀ (u w : TreeVertex d), treeAdj u w → 0 < siteVariance beta μ (root d) t →
      CriticalSpatialEndpointBounds
        (∫ z, IsingCopyEnergy.density beta (root d) t z ∂copies beta μ)
        (∑' n, noiseShellEnergy (μ := μ) hb t n)
        (∑' n, linearShellEnergy (μ := μ) hb t n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n))
        (logVariance hb μ u w t) (siteVariance beta μ (root d) t)
        M (varianceScale d beta T) (min (Real.sqrt (t : ℝ)) 1) := by
  obtain ⟨cL, aL, qL, CL, hcL, haL, hqL, _, hlinear⟩ :=
    exists_linear_energy_long_constants hμ hb hd hcritical
  let BC := max B 1
  let EC := max E ((2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2)
  let cc := min c cL
  let aa := min a aL
  let qq := min q qL
  let CC := max C₀ CL
  have hBC : 0 ≤ BC := hB.trans (le_max_left _ _)
  have hEC : 0 ≤ EC := hE.trans (le_max_left _ _)
  have hcc : 0 < cc := lt_min hc hcL
  have haa : 0 < aa := lt_min ha haL
  have hqq : 1 < qq := lt_min hq hqL
  have htheta : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
    apply (tanh_threshold_iff_branching_sq hd hb).mpr
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hcritical.le
  obtain ⟨M, hM, hendpoint⟩ := exists_actual_spatial_endpoint_constant hμ hd hb htheta
    (C₀ := CC) hBC hEC hcc haa hqq
  refine ⟨M, hM, ?_⟩
  intro t ht htT u w huw hV
  have hω : 0 < min (Real.sqrt (t : ℝ)) 1 :=
    lt_min (Real.sqrt_pos.2 (show 0 < (t : ℝ) from ht)) zero_lt_one
  apply hendpoint t u w huw ht (varianceScale d beta T) (min (Real.sqrt (t : ℝ)) 1)
    hV (siteVariance_le_varianceScale hμ hb (root d) htT)
    (one_le_varianceScale d beta T) hω (min_le_right _ _) ?_ ?_
  · intro v hv
    have hvQ : C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) :=
      (div_le_div_of_nonneg_right (le_max_left _ _) hω.le).trans hv
    have h := hnoise t ht htT u w huw v hvQ
    apply h.trans
    apply add_le_add
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (logVariance_nonneg hb u w t)
      · exact mul_le_mul_of_nonneg_left (path_decay_mono (min_le_left _ _) hω.le _)
          (Nat.cast_nonneg v.1.length)
      · positivity
      · exact mul_nonneg hBC (logVariance_nonneg hb u w t)
    · apply mul_le_mul
      · exact le_max_left _ _
      · exact mul_le_mul_of_nonneg_left
          (path_double_decay_mono haa.le (min_le_left _ _)
            (zero_lt_one.trans hqq).le (min_le_left _ _) _) (sq_nonneg _)
      · positivity
      · exact hEC
  · intro v hv
    have hvL : CL / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) :=
      (div_le_div_of_nonneg_right (le_max_right _ _) hω.le).trans hv
    have h := hlinear T t ht htT v hvL
    apply h.trans
    apply add_le_add
    · apply mul_le_mul
      · exact le_mul_of_one_le_left (siteVariance_nonneg (root d) t) (le_max_right _ _)
      · exact path_decay_mono (min_le_right _ _) hω.le _
      · exact (Real.exp_pos _).le
      · exact mul_nonneg hBC (siteVariance_nonneg (root d) t)
    · apply mul_le_mul
      · exact le_max_right _ _
      · exact path_double_decay_mono haa.le (min_le_right _ _)
          (zero_lt_one.trans hqq).le (min_le_right _ _) _
      · exact (Real.exp_pos _).le
      · exact hEC

end IsingCopyResponseRowPaths
end Problem367

end

end OAI
