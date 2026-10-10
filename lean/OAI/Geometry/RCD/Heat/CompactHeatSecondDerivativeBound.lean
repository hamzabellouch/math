import OAI.Geometry.RCD.Heat.CompactHeatHessianUniformBound
import OAI.Geometry.RCD.Heat.CompactHeatScaledHessian

namespace OAI
/-! # Uniform bounds on the actual second derivatives of interpolation -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
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

theorem second_derivative_uniform_bound (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) a f
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (k : ℕ) (t : InteriorHeatTime δ),
      |deriv (deriv (D.interpolationMean H k)) (t.val:ℝ)| ≤ B := by
  intro H
  let m := hausdorff n X
  let q := hX.quadratic
  let w := heatSobolev m q a ha f
  choose u v UV WU WV hu hv hUV hWU hWV hd using fun k (s : InteriorHeatTime δ) =>
    D.interpolationMean_hessian ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν f A hf ha k s.val
  obtain ⟨B,hB,hbound⟩ := D.scaled_hessian_uniform_bound hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
    hR hδ hS hT f A hf ha u v WU WV UV hu hv hWU hWV hUV
  let C := (2*(n:ℝ)*(|K|+1/(a/2)))^2*(A:ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C+B,add_nonneg hC hB,?_⟩
  intro k t
  let F x := (ε k/2)^2*localHessianAction m q w (u k t) (v k t) (WU k t) (WV k t) (UV k t) x
  have heq : deriv (deriv (D.interpolationMean H k)) (t.val:ℝ)=
      D.laplacianRemainder f a k t.val-∫ x, F x ∂m := by
    rw [(hd k t).deriv,← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [F]; ring
  have hεsq : (ε k/4)^2 ≤ 1 := by nlinarith [hε1 k,hε k]
  have hrem : |D.laplacianRemainder f a k t.val| ≤ C :=
    (D.laplacianRemainder_bound hK f A hf ha k t.val).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hεsq hC)
  have hnorm : |∫ x, F x ∂m| ≤ ∫ x, |F x| ∂m := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := m) F
  have hI : |∫ x, F x ∂m| ≤ B := hnorm.trans (hbound k t)
  rw [heq]
  calc
    _ ≤ |D.laplacianRemainder f a k t.val|+|∫ x, F x ∂m| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (D.laplacianRemainder f a k t.val) (∫ x, F x ∂m)
    _ ≤ _ := add_le_add hrem hI

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
