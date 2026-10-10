import OAI.Probability.PosteriorReplicas.Measures.GaussianDifferentiation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

lemma gaussian_scaled_constant (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (ε^q)⁻¹ * (2*Real.pi)^(-(q:ℝ)/2) = (2*Real.pi*ε^2)^(-(q:ℝ)/2) := by
  have he : (ε^2)^(-(q:ℝ)/2) = (ε^q)⁻¹ := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ) * (-(q:ℝ)/2) = -(q:ℝ) by ring, Real.rpow_neg hε.le,
      Real.rpow_natCast]
  rw [Real.mul_rpow (by positivity) (sq_nonneg ε), he, mul_comm]

lemma scaledRadial_eq {k : ℕ} (n : ℕ) (y x : Vec k) :
    scaledRadial n y x = ENNReal.ofReal
      ((2*Real.pi* ((n+1:ℝ)⁻¹)^2)^(-(k:ℝ)/2) *
        Real.exp (-‖x-y‖^2 / (2*((n+1:ℝ)⁻¹)^2))) := by
  have he := noiseScale_pos n
  simp only [scaledRadial, gaussianRadialDensity, finrank_euclideanSpace_fin]
  rw [← ENNReal.ofReal_inv_of_pos (pow_pos he _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← mul_assoc, gaussian_scaled_constant k he]
  have hexp : -(‖x-y‖/noiseScale n)^2/2 = -‖x-y‖^2/(2*(noiseScale n)^2) := by
    field_simp
  rw [hexp]
  simp only [noiseScale, one_div]

end PosteriorReplicas
end

end OAI
