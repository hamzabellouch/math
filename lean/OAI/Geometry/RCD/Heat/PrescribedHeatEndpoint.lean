import OAI.Geometry.RCD.Heat.NearEndpointTransfer
import OAI.Geometry.RCD.Heat.KernelHeatSharpLipschitz
import OAI.Geometry.RCD.Coordinates.SplittingCoordinateLipschitz

namespace OAI

/-! # Actual heat estimates at the prescribed two endpoints -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.prescribed_heat_endpoint {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k)≤r k/48) (hy : ∀ k, dist (y k) (p k)≤r k/48)
    {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (h : ℕ → Lp ℝ 2 (hausdorff n X)) (V : ℕ → X → ℝ) (L a : ℝ≥0) (A : ℕ → ℝ≥0)
    (hV : ∀ k, LipschitzWith L (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hrep : ∀ k, V k =ᵐ[hausdorff n X] h k)
    (hA : ∀ k, ∀ᵐ z ∂hausdorff n X, |h k z|≤A k) (hscale : ∀ k, (A k:ℝ)≤a*r k) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let hk k := hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k)
    let φ k := kernelHeat μ Q (hk k) (η*(r k)^2) (h k)
    ∃ F e : ℕ → ℝ, (∀ k, 0≤F k) ∧ Tendsto F atTop (𝓝 (L:ℝ)) ∧
      (∀ k, 0≤e k) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ k, |φ k (y k)-φ k (x k)|/r k≤F k*(dist (v k (x k)) (v k (y k))/r k)+e k := by
  intro μ Q hk φ
  obtain ⟨γ,δ,e,z,hδ,hδ0,_hgeo,hnear,hstay,he,he0,hz,hz0,hbound⟩ :=
    hX.nearby_heat_endpoint hn hK p x y r ε hr hr0 hcurv hε hε1 hε0 u v hsplit hx hy
      hη hη1 h V L a A hV hVc hrep hA hscale
  let H k := (L:ℝ)*Real.exp (-K*(η*(r k)^2))
  let F k := Real.sqrt ((H k)^2+e k)
  have hH (k : ℕ) : 0≤H k := mul_nonneg L.coe_nonneg (Real.exp_pos _).le
  have hH0 : Tendsto H atTop (𝓝 (L:ℝ)) := by
    have ht : Tendsto (fun k => -K*(η*(r k)^2)) atTop (𝓝 0) := by
      simpa using ((hr0.pow 2).const_mul η).const_mul (-K)
    have he := (Real.continuous_exp.tendsto 0).comp ht
    simpa only [H,Function.comp_apply,Real.exp_zero,mul_one] using! he.const_mul (L:ℝ)
  have hF0 : Tendsto F atTop (𝓝 (L:ℝ)) := by
    simpa only [add_zero,Real.sqrt_sq L.coe_nonneg] using ((hH0.pow 2).add he0).sqrt
  have hφLip (k : ℕ) : LipschitzWith ⟨H k,hH k⟩ (φ k) := by
    obtain ⟨M,hM⟩ := (hVc k).exists_bound_of_continuous (hV k).continuous
    have hMb (w : X) : |V k w|≤M := by simpa only [Real.norm_eq_abs] using hM w
    exact hX.kernel_heat_sharp_lipschitz hn (hk k) (h k) (hV k) (hrep k) M hMb
      (mul_pos hη (sq_pos_of_pos (hr k)))
  have hvLip (k : ℕ) {z w : X} (hz : dist z (p k)<2*r k) (hw : dist w (p k)<2*r k) :
      dist (v k z) (v k w)≤2*(n:ℝ)*dist z w := by
    have hs : FirstOrderSplittingOn μ Q (p k) (8*(2*r k)) (ε k) (u k) (v k) := by
      simpa only [show (8:ℝ)*(2*r k)=16*r k by ring] using hsplit k
    have hl := hX.splitting_coordinate_lipschitz hn (mul_pos (by norm_num) (hr k)) (hε k) hs
    have hh := hl.dist_le_mul z hz w hw
    exact hh.trans (mul_le_mul_of_nonneg_right (by
      change (n:ℝ)*(1+ε k)≤2*(n:ℝ)
      nlinarith [Nat.cast_nonneg (α:=ℝ) n,hε1 k]) dist_nonneg)
  let err k := z k+Real.sqrt (e k)+(H k+F k*(2*(n:ℝ)))*(δ k/12)
  have herr (k : ℕ) : 0≤err k := by
    exact add_nonneg (add_nonneg (hz k) (Real.sqrt_nonneg _))
      (mul_nonneg (add_nonneg (hH k) (mul_nonneg (Real.sqrt_nonneg _) (by positivity)))
        (div_nonneg (hδ k).1.le (by norm_num)))
  have herr0 : Tendsto err atTop (𝓝 0) := by
    have hh := (hz0.add he0.sqrt).add ((hH0.add (hF0.mul_const (2*(n:ℝ)))).mul (hδ0.div_const 12))
    simpa only [Real.sqrt_zero,add_zero,zero_div,mul_zero] using hh
  refine ⟨F,err,fun k => Real.sqrt_nonneg _,hF0,herr,herr0,?_⟩
  intro k
  have hn : dist (γ k 0) (x k)+dist (γ k 1) (y k)≤(δ k/12)*r k := by
    have hh := add_lt_add (hnear k).1 (hnear k).2
    nlinarith [hh]
  have hh := near_endpoint_transfer (φ k) (v k) (x k) (y k) (γ k 0) (γ k 1)
    (F := F k) (E := z k+Real.sqrt (e k)) (δ := δ k/12)
    (hr k) (hH k) (by positivity : 0≤2*(n:ℝ)) (Real.sqrt_nonneg _) hn
    (hφLip k |>.dist_le_mul _ _) (hφLip k |>.dist_le_mul _ _)
    (hvLip k (by linarith [hstay k 0,hr k]) (by linarith [hx k,hr k]))
    (hvLip k (by linarith [hstay k 1,hr k]) (by linarith [hy k,hr k]))
    (by simpa only [F,H,add_assoc] using! hbound k)
  simpa only [err,add_assoc] using hh

end RegularPointCoordinates

end

end OAI
