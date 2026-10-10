import OAI.Geometry.RCD.Heat.CompactHeatGlobalPower
import OAI.Geometry.RCD.Heat.CompactHeatBackwardSourceFormula
import OAI.Geometry.RCD.Heat.CompactHeatPowerMomentBound
import OAI.Geometry.RCD.Heat.PowerRateBound

namespace OAI

/-! # Uniform differential inequality for the actual heat-density powers

This is the power estimate in Gigli--Tamanini, Proposition 4.6,
equations (4.19)--(4.21), on the first half of the interpolation.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationPowerMean_deriv_le (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k j : ℕ) (t : ℝ), 0 < t → t < 1/2 →
      DifferentiableAt ℝ (D.interpolationPowerMean univ (j+2) k) t ∧
      deriv (D.interpolationPowerMean univ (j+2) k) t ≤
        C*(j+1:ℝ)*(D.interpolationPowerMean univ (j+2) k t+1) := by
  obtain ⟨A,hA,hsource⟩ := D.backward_source_formula_lower hK hε1 ρ₁ hm₁ hp₁ hC₁ hν z
    (le_trans (by norm_num) hR) hT
  obtain ⟨L,hL,hmoment⟩ := D.interpolationDensity_power_moment_bound hε1 z hR hS hT
  refine ⟨A*(1+L^2),by positivity,?_⟩
  intro k j t ht ht2
  have ht1 : t < 1 := by linarith
  let τ : Ioo (0:ℝ) 1 := ⟨t,ht,ht1⟩
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let c := ε k/4
  let s := c*t
  let r := c*(1-t)
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  have hs : 0 < s := mul_pos hc ht
  have hr : 0 < r := mul_pos hc (sub_pos.mpr ht1)
  have htime : c-c*t = r := by dsimp only [r]; ring
  obtain ⟨f,g,⟨B,hf⟩,⟨E,hg⟩,hfe,hge,hder⟩ :=
    D.interpolationPowerMean_global_hasDerivAt hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν z hR hS hT k
  let u := heatSobolev m Q s hs f
  let v := heatSobolev m Q r hr g
  let d := -heatGenerator m Q s hs f
  let e := -heatGenerator m Q r hr g
  have hU : SobolevSpace.toLp m Q u =ᵐ[m] kernelHeat m Q hk s f := by
    simpa only [u,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk hs f).symm
  have hV : SobolevSpace.toLp m Q v =ᵐ[m] kernelHeat m Q hk r g := by
    simpa only [v,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk hr g).symm
  have hD : kernelHeatGeneratorSource m Q hk s f =ᵐ[m] d := by
    filter_upwards [kernelHeatGeneratorSource_represents m Q hk hs f,
      Lp.coeFn_neg (heatGenerator m Q s hs f)] with x hx hy
    rw [heatGeneratorAt_of_pos m Q s hs] at hx
    exact hx.trans hy.symm
  have hE : kernelHeatGeneratorSource m Q hk r g =ᵐ[m] e := by
    filter_upwards [kernelHeatGeneratorSource_represents m Q hk hr g,
      Lp.coeFn_neg (heatGenerator m Q r hr g)] with x hx hy
    rw [heatGeneratorAt_of_pos m Q r hr] at hx
    exact hx.trans hy.symm
  have hden : (fun x => SobolevSpace.toLp m Q u x*SobolevSpace.toLp m Q v x) =ᵐ[m]
      D.interpolationDensity k τ := by
    filter_upwards [hU,hV] with x hx hy
    change _ = hX.compactHeatFactor hn p μ (D.left k) s hs x*
      hX.compactHeatFactor hn p ν (D.right k) r hr x
    rw [hx,hy,hfe s hs x,hge r hr x]
  have hUb : ∀ᵐ x ∂m, |SobolevSpace.toLp m Q u x| ≤ B := by
    filter_upwards [hU] with x hx
    rw [hx]
    exact (hX.kernelHeat_bounded_regularity hn p hk f B hf s hs).2 x
  have hVb : ∀ᵐ x ∂m, |SobolevSpace.toLp m Q v x| ≤ E := by
    filter_upwards [hV] with x hx
    rw [hx]
    exact (hX.kernelHeat_bounded_regularity hn p hk g E hg r hr).2 x
  have hU0 : ∀ᵐ x ∂m, 0 ≤ SobolevSpace.toLp m Q u x := by
    filter_upwards [hU] with x hx
    rw [hx,← hfe s hs x]
    exact (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) s hs x).le
  have hV0 : ∀ᵐ x ∂m, 0 < SobolevSpace.toLp m Q v x := by
    filter_upwards [hV] with x hx
    rw [hx,← hge r hr x]
    exact hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) r hr x
  let H : X → ℝ := fun x => A*(1+(dist z x)^2)
  have hH : Integrable (fun x => (SobolevSpace.toLp m Q u x*
      SobolevSpace.toLp m Q v x)^(j+2)*H x) m := by
    apply ((D.interpolationDensity_weighted_power_integrable hε1 z hR hS hT k τ
      (by omega : 2 ≤ j+2)).const_mul A).congr
    filter_upwards [hden] with x hx
    dsimp only [H]
    rw [hx,dist_comm z x]
    ring
  have hlog : ∀ᵐ x ∂m, -H x ≤ (ε k/2)*(e x/SobolevSpace.toLp m Q v x-
      localGamma m Q v v x/(SobolevSpace.toLp m Q v x)^2) := by
    have hh := hsource k τ ht2.le g E hg (hge r hr)
    filter_upwards [hh,hV] with x hx hy
    dsimp only [H]
    rw [hy]
    simpa only [neg_mul] using hx
  have hrate := power_rate_le_of_log_source m Q u v d e
    (heatSobolev_weak_laplacian m Q s hs f) (heatSobolev_weak_laplacian m Q r hr g)
    B E hUb hVb hU0 hV0 (half_pos (hε k)).le H j hH hlog
  have hd := hder (j+2) (by omega) t ht ht1
  rw [htime] at hd
  have hrateEq : (∫ x, (kernelHeat m Q hk s f x*kernelHeat m Q hk r g x)^(j+1)*
      (kernelHeatGeneratorSource m Q hk s f x*kernelHeat m Q hk r g x-
        kernelHeat m Q hk s f x*kernelHeatGeneratorSource m Q hk r g x) ∂m) =
    ∫ x, (SobolevSpace.toLp m Q u x*SobolevSpace.toLp m Q v x)^(j+1)*
      (d x*SobolevSpace.toLp m Q v x-SobolevSpace.toLp m Q u x*e x) ∂m := by
    apply integral_congr_ae
    filter_upwards [hU,hV,hD,hE] with x hu hv hd he
    rw [hu,hv,hd,he]
  have hmean : D.interpolationPowerMean univ (j+2) k t =
      ∫ x, (D.interpolationDensity k τ x)^(j+2) ∂m := by
    simp only [interpolationPowerMean,setIntegral_univ]
    rfl
  have hmomentEq : (∫ x, (SobolevSpace.toLp m Q u x*SobolevSpace.toLp m Q v x)^(j+2)*H x ∂m) =
      A*∫ x, (D.interpolationDensity k τ x)^(j+2)*(1+(dist x z)^2) ∂m := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hden] with x hx
    dsimp only [H]
    rw [hx,dist_comm z x]
    ring
  refine ⟨hd.differentiableAt,?_⟩
  rw [hd.deriv]
  simp only [show j+2-1 = j+1 by omega,setIntegral_univ] at *
  rw [hrateEq]
  have hcm : ε k/2/2 = c := by dsimp only [c]; ring
  rw [hcm,hmomentEq] at hrate
  have hmom := hmoment k τ (j+2) (by omega)
  rw [hmean]
  simp only [Nat.cast_add,Nat.cast_ofNat] at hrate ⊢
  calc
    _ ≤ (j+1:ℝ)*(A*∫ x, (D.interpolationDensity k τ x)^(j+2)*(1+(dist x z)^2) ∂m) := hrate
    _ ≤ (j+1:ℝ)*(A*((1+L^2)*(∫ x, (D.interpolationDensity k τ x)^(j+2) ∂m)+1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmom hA) (by positivity)
    _ ≤ A*(1+L^2)*(j+1:ℝ)*((∫ x, (D.interpolationDensity k τ x)^(j+2) ∂m)+1) := by
      nlinarith [mul_nonneg (mul_nonneg hA (show 0 ≤ (j+1:ℝ) by positivity)) (sq_nonneg L)]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
