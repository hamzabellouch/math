import OAI.Geometry.RCD.Heat.BoundedHeatVelocityHessian
import OAI.Geometry.RCD.Heat.CompactHeatVelocityPotential
import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # Actual local velocity and osmotic Hessian representatives -/

open Set Filter MeasureTheory TopologicalSpace
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

theorem local_velocity_hessian_data
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (k : ℕ) (t : Ioo (0:ℝ) 1) {Ω : Set X} (hΩ : IsCompact Ω) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ θ η Wθ Wη Gθ Gη : SobolevSpace m q,
      (SobolevSpace.toLp m q θ =ᵐ[m.restrict Ω] D.velocityPotential k t) ∧
      (SobolevSpace.toLp m q η =ᵐ[m.restrict Ω] D.osmoticPotential k t) ∧
      (SobolevSpace.toLp m q Wθ =ᵐ[m.restrict Ω] localGamma m q w θ) ∧
      (SobolevSpace.toLp m q Wη =ᵐ[m.restrict Ω] localGamma m q w η) ∧
      (SobolevSpace.toLp m q Gθ =ᵐ[m.restrict Ω] localGamma m q θ θ) ∧
      (SobolevSpace.toLp m q Gη =ᵐ[m.restrict Ω] localGamma m q η η) := by
  intro m q w
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let c := ε k/4
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  have hs : 0 < c*(t:ℝ) := mul_pos hc t.property.1
  have ht : 0 < c*(1-(t:ℝ)) := mul_pos hc (sub_pos.mpr t.property.2)
  obtain ⟨f₀,⟨A₀,hf₀⟩,he₀⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k)
  obtain ⟨f₁,⟨A₁,hf₁⟩,he₁⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k)
  have hpf : ∀ x ∈ Ω, 0 < kernelHeat m q hk (c*t) f₀ x := by
    intro x _
    rw [← he₀ _ hs x]
    exact hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x
  have hpg : ∀ x ∈ Ω, 0 < kernelHeat m q hk (c*(1-t)) f₁ x := by
    intro x _
    rw [← he₁ _ ht x]
    exact hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x
  obtain ⟨_,_,_,θ,η,Wθ,Wη,Gθ,Gη,_,_,_,hθ,hη,hWθ,hWη,hGθ,hGη,_⟩ :=
    hX.bounded_heat_velocity_hessian hn p f₀ f₁ f A₀ A₁ A hf₀ hf₁ hf hs ht ha c hΩ hpf hpg
  refine ⟨θ,η,Wθ,Wη,Gθ,Gη,?_,?_,hWθ,hWη,hGθ,hGη⟩
  · filter_upwards [hθ] with x hx
    rw [hx,← he₀ _ hs x,← he₁ _ ht x]
    rfl
  · filter_upwards [hη] with x hx
    rw [hx,← he₀ _ hs x,← he₁ _ ht x]
    dsimp only [osmoticPotential,interpolationDensity,c]
    rw [Real.log_mul
      (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x).ne'
      (hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x).ne']
    ring

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
