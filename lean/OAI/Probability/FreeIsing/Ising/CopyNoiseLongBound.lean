import OAI.Probability.FreeIsing.Critical.NoisePathConstants
import OAI.Probability.FreeIsing.Ising.CopySmallLogLoss
import OAI.Probability.FreeIsing.Ising.NoiseTwoTails
import OAI.Probability.FreeIsing.Ising.OrientedStemTail

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingOrientedPath IsingCopyPathBounds IsingCopySmallLogLoss TreeKoopman

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_noise_energy_long_constants
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0) :
    ∃ B E c a q C₀ : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ 0 < c ∧ 0 < a ∧ 1 < q ∧ 0 < C₀ ∧
      ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * (logVariance hb μ u w t) *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)) := by
  have hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
    apply (tanh_threshold_iff_branching_sq hd hb).mpr
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hcritical.le
  obtain ⟨C, hC, hraw⟩ := exists_noiseEnergy_bound_of_two_tails hμ hd hb hthreshold
  obtain ⟨hη, hlengthC, hbase, hdecay⟩ := criticalNoise_constants_positive hd hb hcritical
  let K := Real.exp (4 * beta / (1 - Real.tanh beta))
  refine ⟨4 * K * C, 4 * edgeLogBound d beta T ^ 2,
    criticalNoiseEta d beta / 4, 1 / (2 * ((d : ℝ) - 1)), criticalNoiseTailBase d,
    criticalNoiseLengthConstant beta, by positivity, by positivity,
    div_pos hη (by norm_num), hdecay, hbase, hlengthC, ?_⟩
  intro t ht htT u w huw v hn
  let n := v.1.length
  let ω := min (Real.sqrt (t : ℝ)) 1
  have hω : 0 < ω := lt_min (Real.sqrt_pos.2 (show 0 < (t : ℝ) from ht)) zero_lt_one
  obtain ⟨hn8, hlength⟩ := criticalNoise_length_admissible hd hb hcritical hω
    (min_le_right _ _) hn
  have htail (inward : Bool) (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·))
      (m : ℕ) (hm : n / 2 ≤ m) :
      (observationLaw μ) {x | K *
        Real.exp (-((criticalNoiseEta d beta / 4) * ω) * n) <
          extensionAverage hb t inward stem m x} ≤
        ENNReal.ofReal (Real.exp (-(1 / (2 * ((d : ℝ) - 1))) * criticalNoiseTailBase d ^ n)) := by
    obtain ⟨hsum, hlevel, htail⟩ := half_path_cut_admissible hn8 hm
    have hlevel' : ((n : ℝ) / 4) / 2 - 1 ≤ (m / 2 - 1 + 1 : ℕ) := by
      convert hlevel using 1
      ring
    have htail' : ((n : ℝ) / 4) / 2 ≤ (m - m / 2 : ℕ) := by
      convert htail using 1
      ring
    have h := measure_extensionAverage_gt_le_double_exp_common hμ hb hd hcritical ht
      inward stem hstem (m / 2 - 1) (m - m / 2) hη.le
      (show 0 ≤ (n : ℝ) / 4 by positivity)
      (min_le_left _ _) (min_le_right _ _) hlevel' htail' hlength
    simpa only [hsum, criticalNoise_threshold_eq, criticalNoise_tail_eq hd] using h
  have hv : v.1.IsChain (· ≠ ·) := v.2
  have hvr : (reverseVertex v).1.IsChain (· ≠ ·) := (reverseVertex v).2
  have h := hraw t T htT u w huw v (n / 2) (by dsimp [n]; omega)
    (K * Real.exp (-((criticalNoiseEta d beta / 4) * ω) * n))
    (Real.exp (-(1 / (2 * ((d : ℝ) - 1))) * criticalNoiseTailBase d ^ n))
    (by positivity) (Real.exp_pos _).le
    (htail false (v.1.take (n / 2)) (hv.take _) (n - n / 2) (by omega))
    (htail true ((reverseVertex v).1.take (n - n / 2)) (hvr.take _) (n / 2) le_rfl)
  convert h using 1
  simp only [logVariance, cavityLogDifference, n, ω]
  ring

end Problem367.IsingCopyResponseRowPaths

end

end OAI
