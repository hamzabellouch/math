import OAI.MeasureTheory.Falconer.Estimates.PositiveDistancePushforward
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem width_pos (d : PositiveDistanceData) : 0 < d.width := by
  unfold width; positivity

theorem levelMass_pos (d : PositiveDistanceData) : 0 < d.levelMass := by
  unfold levelMass; positivity

theorem normalization_pos (d : PositiveDistanceData) : 0 < d.normalization := by
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos d.levelMass_pos _)

theorem normalization_ne_top (d : PositiveDistanceData) : d.normalization ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem normalization_inv (d : PositiveDistanceData) :
    d.normalization⁻¹ = ENNReal.ofReal
      (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) := by
  rw [normalization,← ENNReal.ofReal_inv_of_pos
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos d.levelMass_pos _)),
    inv_div,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv]

theorem coincidence_ne_top (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence ≠ ∞ :=
  ENNReal.mul_ne_top d.normalization_ne_top (measure_ne_top _ _)

theorem unnormalized_coincidence (d : PositiveDistanceData) :
    d.normalization⁻¹ * d.coincidence =
      (d.pair.prod d.pair)
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width} := by
  rw [coincidence,← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt d.normalization_pos) d.normalization_ne_top,one_mul]

theorem bin_norm_sq_le_coincidence (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    binL2Norm d.distance d.width * binL2Norm d.distance d.width ≤
      ENNReal.ofReal (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) * d.coincidence := by
  rw [← d.normalization_inv,d.unnormalized_coincidence,binL2Norm_mul_self]
  apply (real_bin_collision_bound d.distance d.width_pos).trans
  rw [d.distance_collision]
  apply measure_mono
  intro z hz
  change |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ d.width at hz
  change |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width
  exact hz.trans (by nlinarith [d.width_pos])

theorem bin_norm_le_coincidence_sqrt (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    binL2Norm d.distance d.width ≤
      (d.normalization⁻¹ * d.coincidence)^(1/2:ℝ) := by
  have h := d.bin_norm_sq_le_coincidence
  rw [← d.normalization_inv] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact hh

theorem distance_kernel_bound (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (ht : d.t = e.t) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ((d.normalization⁻¹*d.coincidence)^(1/2:ℝ) *
        (e.normalization⁻¹*e.coincidence)^(1/2:ℝ)) := by
  have hw : d.width = e.width := by simp only [width,ht]
  apply (real_bin_decaying_kernel_bound d.distance e.distance d.width_pos).trans
  apply mul_le_mul_right
  exact mul_le_mul' d.bin_norm_le_coincidence_sqrt (hw ▸ e.bin_norm_le_coincidence_sqrt)

theorem common_profile_distance_kernel_bound (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) *
        (d.coincidence*e.coincidence)^(1/2:ℝ) := by
  have h := distance_kernel_bound d e ht
  rw [← hn] at h
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)] at h ⊢
  have he (x : ℝ≥0∞) : x^(1/2:ℝ)*x^(1/2:ℝ) = x := by
    rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
    norm_num
  have hr (x y z : ℝ≥0∞) : (x*y)*(x*z) = (x*x)*(y*z) := by ring
  rw [hr,he,d.normalization_inv] at h
  simpa only [mul_assoc] using h

theorem common_profile_distance_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) *
        max d.coincidence e.coincidence := by
  apply (common_profile_distance_kernel_bound d e ht hn).trans
  apply mul_le_mul_right
  have h := ENNReal.rpow_le_rpow (mul_le_mul'
    (le_max_left d.coincidence e.coincidence) (le_max_right d.coincidence e.coincidence))
    (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at h
  norm_num at h
  simpa only [le_max_iff] using h

end PositiveDistanceData

end PlanarFalconer

end OAI
