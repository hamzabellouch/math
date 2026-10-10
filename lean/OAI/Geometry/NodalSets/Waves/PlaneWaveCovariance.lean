import OAI.Geometry.NodalSets.Waves.GaussianPairCovariance
import OAI.Geometry.NodalSets.Waves.NormalizedWaveRatio

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma complex_rotated_pairing (z : ℂ) (t : ℝ) :
    z.re*(z*Complex.exp (Complex.I*(t:ℂ))).re +
      z.im*(z*Complex.exp (Complex.I*(t:ℂ))).im = ‖z‖^2*Real.cos t := by
  simp [Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,
    Complex.sq_norm,Complex.normSq_apply]
  ring

lemma gaussianWaveField_eq_pair (V : ι → Coord → ℂ) (v : Coord) :
    (fun a ↦ gaussianWaveField V a v) = pairLinearSum (fun i ↦ V i v) := by
  funext a
  rw [pairLinearSum_eq_complex]
  simp only [gaussianWaveField,Complex.re_sum]

lemma planeWave_zero (k : Coord →L[ℝ] ℝ) (s : ℝ) : planeWave k s 0 = 1 := by
  simp [planeWave]

lemma planeWave_two_point_covariance (alpha : ι → ℂ) (k : ι → Coord →L[ℝ] ℝ)
    (s : ℝ) (v : Coord) :
    cov[(fun a ↦ gaussianWaveField (fun i z ↦ alpha i*planeWave (k i) s z) a 0),
      (fun a ↦ gaussianWaveField (fun i z ↦ alpha i*planeWave (k i) s z) a v);gaussianPairs] =
      ∑ i, ‖alpha i‖^2*Real.cos (k i v/s) := by
  rw [gaussianWaveField_eq_pair,gaussianWaveField_eq_pair,covariance_pairLinearSum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [planeWave] using complex_rotated_pairing (alpha i) (k i v/s)

lemma planeWave_value_variance (alpha : ι → ℂ) (k : ι → Coord →L[ℝ] ℝ)
    (s : ℝ) (v : Coord) :
    Var[fun a ↦ gaussianWaveField (fun i z ↦ alpha i*planeWave (k i) s z) a v;gaussianPairs] =
      ∑ i, ‖alpha i‖^2 := by
  rw [gaussianWaveField_eq_pair,variance_pairLinearSum]
  simp only [norm_mul,planeWave_norm,mul_one]

end
end Yau.Geometry

end OAI
