import OAI.Geometry.NodalSets.Charts.MetricFrequencyBounds
import OAI.Geometry.NodalSets.Waves.PlaneWaveJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma planeWave_divided_frequency (k : Coord →L[ℝ] ℝ) (s : ℝ) :
    planeWave k s = planeWave (s⁻¹ • k) 1 := by
  ext v
  simp [planeWave, div_eq_mul_inv, mul_comm]

lemma planeWave_frequency_derivative_bound (k : Coord →L[ℝ] ℝ) (s : ℝ)
    {B : ℝ} (hB : 1 ≤ B)
    (hk : sourceEuclideanNorm (fun j ↦ k (Pi.single j 1)/s) ≤ B)
    (d : ℕ) (v : Coord) :
    ‖iteratedFDeriv ℝ d (planeWave k s) v‖ ≤ d.factorial*(4*B)^d := by
  have hnorm : ‖s⁻¹ • k‖ ≤ 4*B := by
    apply (covector_norm_le_source (s⁻¹ • k)).trans
    have he : (fun j ↦ (s⁻¹ • k) (Pi.single j 1)) =
        fun j ↦ k (Pi.single j 1)/s := by
      ext j
      simp [div_eq_mul_inv,mul_comm]
    rw [he]
    linarith
  rw [planeWave_divided_frequency]
  exact planeWave_derivative_bound _ (by norm_num) (by linarith) hnorm d v

lemma weighted_planeWave_derivative_bound (z : ℂ) (k : Coord →L[ℝ] ℝ) (s : ℝ)
    {B : ℝ} (hB : 1 ≤ B)
    (hk : sourceEuclideanNorm (fun j ↦ k (Pi.single j 1)/s) ≤ B)
    (d : ℕ) (v : Coord) :
    ‖iteratedFDeriv ℝ d (fun u ↦ z*planeWave k s u) v‖ ≤
      ‖z‖*(d.factorial*(4*B)^d) := by
  change ‖iteratedFDeriv ℝ d (z • planeWave k s) v‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply ((planeWave_smooth k s).of_le
    (by exact_mod_cast (show (d:ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul]
  exact mul_le_mul_of_nonneg_left (planeWave_frequency_derivative_bound k s hB hk d v) (norm_nonneg _)

end
end Yau.Geometry

end OAI
