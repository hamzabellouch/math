import OAI.Geometry.RCD.Heat.BoundedHeatVelocityHessian
import OAI.Geometry.RCD.Heat.CompactHeatVelocityPotential
import OAI.Geometry.RCD.Metric.CompactFactorL2
import OAI.Geometry.RCD.Sobolev.HessianActionRepresentatives

namespace OAI

/-! # The exact scaled factor Hessian for prescribed local velocity data -/

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

theorem velocity_hessian_identity
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (k : ℕ) (t : Ioo (0:ℝ) 1) {Ω : Set X} (hΩ : IsCompact Ω)
    (u v Wu Wv uv θ η Wθ Wη Gθ Gη : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t)
        (mul_pos (div_pos (hε k) (by norm_num)) t.property.1))
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t))
        (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)))
    (hWu : SobolevSpace.toLp (hausdorff n X) hX.quadratic Wu =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) u)
    (hWv : SobolevSpace.toLp (hausdorff n X) hX.quadratic Wv =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) v)
    (huv : SobolevSpace.toLp (hausdorff n X) hX.quadratic uv =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u v)
    (hθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic θ =ᵐ[(hausdorff n X).restrict Ω] D.velocityPotential k t)
    (hη : SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[(hausdorff n X).restrict Ω] D.osmoticPotential k t)
    (hWθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic Wθ =ᵐ[(hausdorff n X).restrict Ω]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) θ)
    (hWη : SobolevSpace.toLp (hausdorff n X) hX.quadratic Wη =ᵐ[(hausdorff n X).restrict Ω]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) η)
    (hGθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic Gθ =ᵐ[(hausdorff n X).restrict Ω]
      localGamma (hausdorff n X) hX.quadratic θ θ)
    (hGη : SobolevSpace.toLp (hausdorff n X) hX.quadratic Gη =ᵐ[(hausdorff n X).restrict Ω]
      localGamma (hausdorff n X) hX.quadratic η η) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    (fun x => D.interpolationDensity k t x*
      (localHessianAction m q w θ θ Wθ Wθ Gθ x-localHessianAction m q w η η Wη Wη Gη x))
      =ᵐ[m.restrict Ω] fun x => -(ε k/2)^2*localHessianAction m q w u v Wu Wv uv x := by
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

  let u₀ := heatSobolev m q (c*t) hs f₀
  let v₀ := heatSobolev m q (c*(1-t)) ht f₁
  obtain ⟨Wu₀,Wv₀,uv₀,θ₀,η₀,Wθ₀,Wη₀,Gθ₀,Gη₀,hWu₀,hWv₀,huv₀,hθ₀,hη₀,hWθ₀,hWη₀,hGθ₀,hGη₀,hH⟩ :=
    hX.bounded_heat_velocity_hessian hn p f₀ f₁ f A₀ A₁ A hf₀ hf₁ hf hs ht ha c hΩ hpf hpg
  have hθr : SobolevSpace.toLp m q θ₀ =ᵐ[m.restrict Ω] D.velocityPotential k t := by
    filter_upwards [hθ₀] with x hx
    rw [hx,← he₀ _ hs x,← he₁ _ ht x]
    rfl
  have hηr : SobolevSpace.toLp m q η₀ =ᵐ[m.restrict Ω] D.osmoticPotential k t := by
    filter_upwards [hη₀] with x hx
    rw [hx,← he₀ _ hs x,← he₁ _ ht x]
    dsimp only [osmoticPotential,interpolationDensity,c]
    rw [Real.log_mul
      (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x).ne'
      (hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x).ne']
    ring
  have hu₀ : SobolevSpace.toLp m q u₀ =ᵐ[m.restrict Ω] SobolevSpace.toLp m q u := by
    filter_upwards [ae_restrict_of_ae (kernelHeat_represents_L2 m q hk hs f₀),ae_restrict_of_ae hu]
      with x hx hy
    exact hx.symm.trans ((he₀ _ hs x).symm.trans hy.symm)
  have hv₀ : SobolevSpace.toLp m q v₀ =ᵐ[m.restrict Ω] SobolevSpace.toLp m q v := by
    filter_upwards [ae_restrict_of_ae (kernelHeat_represents_L2 m q hk ht f₁),ae_restrict_of_ae hv]
      with x hx hy
    exact hx.symm.trans ((he₁ _ ht x).symm.trans hy.symm)
  have hθH := localHessianAction_congr_of_grams m q w θ₀ θ θ₀ θ Wθ₀ Wθ Wθ₀ Wθ Gθ₀ Gθ
    (hθr.trans hθ.symm) (hθr.trans hθ.symm) hWθ₀ hWθ hWθ₀ hWθ hGθ₀ hGθ
  have hηH := localHessianAction_congr_of_grams m q w η₀ η η₀ η Wη₀ Wη Wη₀ Wη Gη₀ Gη
    (hηr.trans hη.symm) (hηr.trans hη.symm) hWη₀ hWη hWη₀ hWη hGη₀ hGη
  have hraw := localHessianAction_congr_of_grams m q w u₀ u v₀ v Wu₀ Wu Wv₀ Wv uv₀ uv
    hu₀ hv₀ (ae_restrict_of_ae hWu₀) (ae_restrict_of_ae hWu)
    (ae_restrict_of_ae hWv₀) (ae_restrict_of_ae hWv)
    (ae_restrict_of_ae huv₀) (ae_restrict_of_ae huv)
  filter_upwards [hH,hθH,hηH,hraw] with x hx hθx hηx hrawx
  rw [hθx,hηx,hrawx,← he₀ _ hs x,← he₁ _ ht x] at hx
  change D.interpolationDensity k t x*_= -4*c^2*_ at hx
  convert hx using 1
  dsimp only [c]
  ring

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
