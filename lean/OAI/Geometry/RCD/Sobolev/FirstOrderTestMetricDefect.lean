import OAI.Geometry.RCD.Heat.PrescribedHeatEndpoint
import OAI.Geometry.RCD.Heat.ScaledHeatValueError
import OAI.Geometry.RCD.Harmonic.VanishingScalarDefect

namespace OAI

/-! # Vanishing metric defect detected by actual compact Lipschitz tests -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_test_metric_defect {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k)≤r k/48) (hy : ∀ k, dist (y k) (p k)≤r k/48)
    (h : ℕ → Lp ℝ 2 (hausdorff n X)) (V : ℕ → X → ℝ) (L a : ℝ≥0) (A : ℕ → ℝ≥0)
    (hV : ∀ k, LipschitzWith L (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hrep : ∀ k, V k =ᵐ[hausdorff n X] h k)
    (hA : ∀ k, ∀ᵐ z ∂hausdorff n X, |h k z|≤A k) (hscale : ∀ k, (A k:ℝ)≤a*r k) :
    Tendsto (fun k => max 0 (|V k (y k)-V k (x k)|/r k-
      (L:ℝ)*(dist (v k (x k)) (v k (y k))/r k))) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let B k := dist (v k (x k)) (v k (y k))/r k
  have hB (k : ℕ) : 0≤B k ∧ B k≤2*(n:ℝ) := by
    refine ⟨div_nonneg dist_nonneg (hr k).le,?_⟩
    have hs : FirstOrderSplittingOn μ Q (p k) (8*(2*r k)) (ε k) (u k) (v k) := by
      simpa only [show (8:ℝ)*(2*r k)=16*r k by ring] using hsplit k
    have hLip := hX.splitting_coordinate_lipschitz hn (mul_pos (by norm_num) (hr k)) (hε k) hs
    have hh := hLip.dist_le_mul (x k) (by change dist (x k) (p k)<2*r k; linarith [hx k,hr k])
      (y k) (by change dist (y k) (p k)<2*r k; linarith [hy k,hr k])
    have hc : (n:ℝ)*(1+ε k)≤2*(n:ℝ) := by nlinarith [Nat.cast_nonneg (α:=ℝ) n,hε1 k]
    have hd : dist (x k) (y k)≤r k := by
      have ht := dist_triangle (x k) (p k) (y k)
      rw [dist_comm (p k) (y k)] at ht
      linarith [hx k,hy k,hr k]
    apply (div_le_iff₀ (hr k)).mpr
    exact (hh.trans (mul_le_mul_of_nonneg_right hc dist_nonneg)).trans
      (mul_le_mul_of_nonneg_left hd (by positivity))
  apply vanishing_scalar_defect (fun k => |V k (y k)-V k (x k)|/r k) B hB
  intro τ hτ
  let C := (L:ℝ)^2/2+(n:ℝ)*Real.exp 1
  have hnoise : Tendsto (fun j => 2*Real.sqrt (heatStep j)*C) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero,zero_mul] using (heatStep_tendsto.sqrt.const_mul 2).mul_const C
  obtain ⟨j,hj⟩ := (hnoise.eventually (gt_mem_nhds hτ)).exists
  let η := heatStep j
  have hη : 0<η := heatStep_pos j
  have hη1 : η≤1 := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
  obtain ⟨F,e,_hF,hF0,_he,he0,hbound⟩ := hX.prescribed_heat_endpoint hn hK p x y r ε hr hr0 hcurv
    hε hε1 hε0 u v hsplit hx hy hη hη1 h V L a A hV hVc hrep hA hscale
  refine ⟨F,e,hF0,he0,?_⟩
  intro k
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k)
  let φ := kernelHeat μ Q hk (η*(r k)^2) (h k)
  have hsmall : (-K)*(r k)^2≤1 := by
    have hb := hcurv k
    have hh : K*(16*r k)^2=256*(K*(r k)^2) := by ring
    rw [hh] at hb
    nlinarith
  have hdx := hX.scaled_heat_value_error hn hK hk (h k) (hV k) (hVc k) (hrep k)
    (hr k) hη hη1 hsmall (x k)
  have hdy := hX.scaled_heat_value_error hn hK hk (h k) (hV k) (hVc k) (hrep k)
    (hr k) hη hη1 hsmall (y k)
  have hs : |V k (y k)-V k (x k)|≤|φ (y k)-V k (y k)|+
      |φ (y k)-φ (x k)|+|φ (x k)-V k (x k)| := by
    have hh := dist_triangle4 (V k (y k)) (φ (y k)) (φ (x k)) (V k (x k))
    simpa only [Real.dist_eq,abs_sub_comm (V k (y k)) (φ (y k))] using hh
  have hdiv := div_le_div_of_nonneg_right hs (hr k).le
  rw [add_div,add_div] at hdiv
  have hb : |φ (y k)-φ (x k)|/r k≤F k*B k+e k := hbound k
  change |φ (x k)-V k (x k)|/r k≤Real.sqrt η*C at hdx
  change |φ (y k)-V k (y k)|/r k≤Real.sqrt η*C at hdy
  change 2*Real.sqrt η*C<τ at hj
  linarith

end RegularPointCoordinates

end

end OAI
