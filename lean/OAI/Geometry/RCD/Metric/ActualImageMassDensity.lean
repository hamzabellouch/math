import OAI.Geometry.RCD.Coordinates.RegularActualImageMass
import OAI.Geometry.RCD.Metric.RescalingVolumeDensity

namespace OAI

/-! # Passing the constructed image mass to the absolute density -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.actual_image_mass_density_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hK : K≤0) {p : X} (hp : IsRegular n p)
    {θ : ℝ}
    (hdensity : ∀ s : ℕ → ℝ, (∀ k, 0 < s k) → Tendsto s atTop (𝓝 0) →
      ∀ b : ℝ, 0 < b → Tendsto
        (fun k => (hausdorff n X).real (ball p (s k*b))/(s k)^n)
        atTop (𝓝 (θ*b^n)))
    {η ζ : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/8192) (hζ : 0 < ζ)
    (hζsmall : ζ*((Real.cosh 1^(n-1)*2^n)*(16*16384)^n) < 1) :
    volume.real (ball (0 : Euclidean n) 1)/(4096:ℝ)^n -
        volume.real (ball (0 : Euclidean n) 1)*imageMassErrorConstant n*ζ ≤
      (1+32*η)^n*(θ*(1/4096+η/2)^n) := by
  obtain ⟨s,hs,hest⟩ := hX.regular_actual_image_mass_estimate hn hK hp hη hηsmall hζ hζsmall
  let r := fun k : ℕ => min (s/2) (1/((k:ℝ)+1))
  have hr (k : ℕ) : 0 < r k := lt_min (half_pos hs) (by positivity)
  have hrs (k : ℕ) : r k < s := (min_le_left _ _).trans_lt (half_lt_self hs)
  have hr0 : Tendsto r atTop (𝓝 0) := squeeze_zero (fun k => (hr k).le)
    (fun _ => min_le_right _ _) tendsto_one_div_add_atTop_nhds_zero_nat
  have hc0 : Tendsto (fun k => K*(163840*r k)^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((hr0.const_mul 163840).pow 2).const_mul K
  have hlim := (hdensity r hr hr0 (1/4096+η/2) (by positivity)).const_mul ((1+32*η)^n)
  apply ge_of_tendsto hlim
  filter_upwards [hc0.eventually (Ioi_mem_nhds (by norm_num : (-1:ℝ)<0))] with k hk
  have hh := hest (r k) (hr k) (hrs k) hk.le
  rw [euclidean_ball_real (by omega : 0 < n) 0 (by positivity)] at hh
  have hrad : r k/4096+(2*r k)*(η/4)=r k*(1/4096+η/2) := by ring
  rw [hrad] at hh
  have hscaled :
      (volume.real (ball (0 : Euclidean n) 1)/(4096:ℝ)^n -
        volume.real (ball (0 : Euclidean n) 1)*imageMassErrorConstant n*ζ)*(r k)^n ≤
      (1+32*η)^n*(hausdorff n X).real (ball p (r k*(1/4096+η/2))) := by
    convert hh using 1
    rw [div_pow]
    ring
  have hdiv := (le_div_iff₀ (pow_pos (hr k) n)).mpr hscaled
  simpa only [mul_div_assoc] using hdiv

end RegularPointCoordinates

end

end OAI
