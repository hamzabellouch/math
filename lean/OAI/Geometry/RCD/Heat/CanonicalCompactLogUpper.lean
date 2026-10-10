import OAI.Geometry.RCD.Heat.CanonicalStrictPositivity
import OAI.Geometry.RCD.Heat.CanonicalGaussianUpper
import OAI.Geometry.RCD.Heat.BoundedHeatVolumePower
import OAI.Geometry.RCD.Heat.SmallNoiseLogScale
import OAI.Geometry.RCD.Heat.GaussianLogUpper
import OAI.Geometry.RCD.Heat.GaussianActionSlack

namespace OAI

/-! # Uniform sharp upper action on bounded endpoint sets -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_bounded_log_upper
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R T η : ℝ}
    (hR : 0 ≤ R) (hT : 0 < T) (hT1 : T < 1) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ x ∈ closedBall p R, ∀ y ∈ closedBall p R,
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k*T/2) x y) ≤ -(dist x y)^2/(2*T)+η := by
  let a := η*T/(2*(R^2+1))
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨C,D,hC,_hD,hupper⟩ := hX.canonicalHeatKernel_gaussian_upper hn p ha
  obtain ⟨c,hc,hvolume⟩ := hX.bounded_heat_volume_power hn p R
  let E := fun k => ε k*Real.log (C/c) - (n:ℝ)*ε k/2*Real.log (ε k*T/2) + D*(ε k)^2*T/2
  have hlog : Tendsto (fun k => ε k*Real.log (ε k*T/2)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc] using small_noise_log_scale hε hε0 (half_pos hT)
  have hElim : Tendsto E atTop (𝓝 0) := by
    have hh := ((hε0.mul_const (Real.log (C/c))).sub (hlog.const_mul ((n:ℝ)/2))).add
      (((hε0.pow 2).const_mul D).mul_const (T/2))
    convert hh using 1
    · funext k; dsimp only [E]; ring
    · norm_num
  filter_upwards [hElim.eventually (gt_mem_nhds (half_pos hη))] with k hk
  intro x hx y hy
  have ht : 0 < ε k*T/2 := div_pos (mul_pos (hε k) hT) (by norm_num)
  have ht1 : ε k*T/2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (hε1 k) hT.le
    nlinarith
  have hp := hX.canonicalHeatKernel_pos hn p (ε k*T/2) ht x y
  have hvol := hvolume y hy (ε k*T/2) ht ht1
  have hh := gaussian_log_upper hp hC hc ht (hε k).le hvol (hupper (ε k*T/2) ht x y)
  have he : ε k*(-(dist x y)^2/((4+a)*(ε k*T/2))+D*(ε k*T/2)) =
      -2*(dist x y)^2/((4+a)*T)+D*(ε k)^2*T/2 := by
    field_simp [ne_of_gt (hε k),ne_of_gt hT,ne_of_gt (by linarith : 0 < 4+a)]
  rw [he] at hh
  simp only [neg_mul,neg_div] at hh
  have hd : dist x y ≤ 2*R := by
    have hx' : dist x p ≤ R := hx
    have hy' : dist y p ≤ R := hy
    have hd := dist_triangle x p y
    rw [dist_comm p y] at hd
    linarith
  have hs := gaussian_action_slack hT hη hR (dist_nonneg (x := x) (y := y)) hd
  change (dist x y)^2/(2*T)-2*(dist x y)^2/((4+a)*T) ≤ η/4 at hs
  dsimp only [E] at hk
  rw [neg_div]
  nlinarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
