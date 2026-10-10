import OAI.Geometry.RCD.Heat.CompactHeatPreservedLawLimit
import OAI.Geometry.RCD.Heat.CompactHeatIntrinsicHessian
import OAI.Geometry.RCD.Heat.CompactHeatActionRealization
import OAI.Geometry.RCD.Sobolev.LocalL1WeakPairing

namespace OAI

/-! # The forward Hessian limit on the fixed common-time law subsequence

There is no further extraction after the continuous law curve has been
selected. The original spatial L1 Hessian limit is retained.
-/

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

theorem forward_hessian_intrinsic_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (τ : Ioo (0:ℝ) 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ht : (τ:ℝ)/2 ∈ Ioo δ 1)
    (φ : X → ℝ) {Lφ Bφ : ℝ≥0} (hφ : LipschitzWith Lφ φ)
    (hs : HasCompactSupport φ) (hBφ : ∀ x, |φ x| ≤ Bφ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hz : ∀ x ∉ closedBall p r, φ x = 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) τ) atTop (𝓝 Q)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (v : SobolevSpace m q) (V : X → ℝ) (Lv Av : ℝ≥0)
      (u WU UU : ℕ → SobolevSpace m q) (J : Lp ℝ 1 (m.restrict (closedBall p r))),
      LipschitzWith Lv V ∧ HasCompactSupport V ∧
      (SobolevSpace.toLp m q v =ᵐ[m] V) ∧
      (∀ᵐ x ∂m, |SobolevSpace.toLp m q v x| ≤ Av) ∧
      (SobolevSpace.toLp m q v =ᵐ[m.restrict (closedBall p r)] D.forward.potential ((τ:ℝ)/2)) ∧
      IsCanonicalHeatHessian m q w v p r φ J ∧
      (∀ k, SobolevSpace.toLp m q (u k) =ᵐ[m.restrict (closedBall p r)]
        hX.fixedGaugeScaledPotential hn p μ (D.left (D.index k)) (ε (D.index k))
          (hε (D.index k)) δ hδ p ((τ:ℝ)/2)) ∧
      (∀ k, SobolevSpace.toLp m q (WU k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (u k)) ∧
      (∀ k, SobolevSpace.toLp m q (UU k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (u k) (u k)) ∧
      Tendsto (fun k => ∫ x in closedBall p r,
        |φ x*localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x-J x| ∂m)
        atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, D.interpolationDensity (D.index (j k)) τ x*
        (φ x*localHessianAction m q w (u (j k)) (u (j k)) (WU (j k)) (WU (j k)) (UU (j k)) x) ∂m)
        atTop (𝓝 (∫ x in closedBall p r, J x ∂(Q : Measure X))) := by
  intro m q w
  obtain ⟨v,V,Lv,Av,hV,hc,hv,hAv,hvloc⟩ := hX.compact_heat_action_realization hn p hK
    μ ρ₀ hm₀ hp₀ hC₀ hμ D.left D.left_pos ε hε hε1 p D.index D.forward.potential
    D.forward_limit hr hδ ht (zero_le_one.trans hR) hS
  obtain ⟨u,WU,UU,J,hu,hWU,hUU,hcan,hJ⟩ := hX.compact_heat_intrinsic_hessian_limit hn p hK
    μ ρ₀ hm₀ hp₀ hC₀ hμ D.left D.left_pos ε hε hε1 p D.index D.forward.potential
    D.forward_limit hr hδ ht (zero_le_one.trans hR) hS φ hφ hs hBφ hφ0 hz f A hf ha v V Lv Av hV hc hv hAv hvloc
  obtain ⟨B,hB,hbound⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  let F k x := φ x*localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x
  have hFi (k : ℕ) : Integrable (F k) m :=
    (localHessianAction_integrable m q w (u k) (u k) (WU k) (WU k) (UU k)).bdd_mul
      hφ.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hBφ x)
  have hdom (k : ℕ) : (D.interpolationLaw (D.index (j k)) τ : Measure X) ≤ ENNReal.ofReal B • m := by
    rw [← withDensity_const]
    apply withDensity_mono
    exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hbound _ _ x)
  have hpair := local_L1_weak_pairing m (fun k => D.interpolationLaw (D.index (j k)) τ) Q
    hweak ENNReal.ofReal_ne_top hdom measurableSet_closedBall (F ∘ j) (fun k => hFi (j k))
    (fun k x hx => by dsimp only [F,Function.comp_apply]; rw [hz x hx,zero_mul]) J
    (hJ.comp hj.tendsto_atTop)
  refine ⟨v,V,Lv,Av,u,WU,UU,J,hV,hc,hv,hAv,hvloc,hcan,hu,hWU,hUU,hJ,?_⟩
  simpa only [D.interpolationLaw_integral,F,Function.comp_apply] using hpair


theorem forward_hessian_common_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (τ : Ioo (0:ℝ) 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ht : (τ:ℝ)/2 ∈ Ioo δ 1)
    (φ : X → ℝ) {Lφ Bφ : ℝ≥0} (hφ : LipschitzWith Lφ φ)
    (hs : HasCompactSupport φ) (hBφ : ∀ x, |φ x| ≤ Bφ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hz : ∀ x ∉ closedBall p r, φ x = 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) τ) atTop (𝓝 Q)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (u WU UU : ℕ → SobolevSpace m q) (J : Lp ℝ 1 (m.restrict (closedBall p r))),
      (∀ k, SobolevSpace.toLp m q (u k) =ᵐ[m.restrict (closedBall p r)]
        hX.fixedGaugeScaledPotential hn p μ (D.left (D.index k)) (ε (D.index k))
          (hε (D.index k)) δ hδ p ((τ:ℝ)/2)) ∧
      (∀ k, SobolevSpace.toLp m q (WU k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (u k)) ∧
      (∀ k, SobolevSpace.toLp m q (UU k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (u k) (u k)) ∧
      Tendsto (fun k => ∫ x, D.interpolationDensity (D.index (j k)) τ x*
        (φ x*localHessianAction m q w (u (j k)) (u (j k)) (WU (j k)) (WU (j k)) (UU (j k)) x) ∂m)
        atTop (𝓝 (∫ x in closedBall p r, J x ∂(Q : Measure X))) := by
  intro m q w
  obtain ⟨_v,_V,_Lv,_Av,u,WU,UU,J,_hV,_hc,_hv,_hAv,_hvloc,_hcan,hu,hWU,hUU,_hL1,hpair⟩ :=
    D.forward_hessian_intrinsic_limit hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
      hR hS hT τ hr hδ ht φ hφ hs hBφ hφ0 hz f A hf ha j hj Q hweak
  exact ⟨u,WU,UU,J,hu,hWU,hUU,hpair⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
