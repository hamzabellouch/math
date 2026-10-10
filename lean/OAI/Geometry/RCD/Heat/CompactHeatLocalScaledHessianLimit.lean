import OAI.Geometry.RCD.Heat.CompactHeatVelocityHessianIdentity
import OAI.Geometry.RCD.Heat.CompactHeatLocalVelocityHessianLimit
import OAI.Geometry.RCD.Heat.CompactHeatVelocityHessianDecomposition
import OAI.Geometry.RCD.Heat.CompactHeatMixedOsmoticHessian
import OAI.Geometry.RCD.Heat.CompactHeatCommonHessianLimit

namespace OAI

/-! # The local limit of the original scaled factor Hessian -/

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

theorem local_scaled_hessian_limit_of_forward (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R r δ : ℝ} (hR : 1 ≤ R) (hr : 0 < r) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (t : InteriorHeatTime δ) (ht : δ < (t.val:ℝ))
    (φ : X → ℝ) (Lφ : ℝ≥0) (hφ : LipschitzWith Lφ φ) (hs : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hsupp : tsupport φ ⊆ closedBall p r)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : ProbabilityMeasure X)
    (u v Wu Wv uv : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p μ (D.left (D.index (j k))) (ε (D.index (j k))/4*t.val)
        (mul_pos (div_pos (hε _) (by norm_num)) t.val.property.1))
    (hv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p ν (D.right (D.index (j k))) (ε (D.index (j k))/4*(1-t.val))
        (mul_pos (div_pos (hε _) (by norm_num)) (sub_pos.mpr t.val.property.2)))
    (hWu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wu k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hWv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wv k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k))
    (huv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (uv k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (u k) (v k))
    (g Wg Gg : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hg : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (g k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        hX.fixedGaugeScaledPotential hn p μ (D.left (D.index k)) (ε (D.index k))
          (hε (D.index k)) (δ/2) (half_pos hδ) p ((t.val:ℝ)/2))
    (hWg : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wg k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (g k))
    (hGg : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Gg k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (g k) (g k))
    (hJ : Tendsto (fun k => ∫ x, D.interpolationDensity (D.index (j k)) t.val x*
      (φ x*localHessianAction (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f)
        (g (j k)) (g (j k)) (Wg (j k)) (Wg (j k)) (Gg (j k)) x) ∂hausdorff n X)
      atTop (𝓝 (∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    Tendsto (fun k => ∫ x in closedBall p r, φ x*(ε (D.index (j k))/2)^2*
        localHessianAction m q w (u k) (v k) (Wu k) (Wv k) (uv k) x ∂m)
        atTop (𝓝 (-(1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) := by
  intro m q w
  obtain ⟨θ,η,Wθ,Wη,Gθ,Gη,hθ,hη,hWθ,hWη,hGθ,hGη,hlim⟩ :=
    D.local_velocity_hessian_limit_of_forward hK hε1 hε0
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hr hδ hS hT t ht
      φ Lφ hφ hs hφ01 hsupp f A hf ha j hj Q₀ g Wg Gg J hg hWg hGg hJ
  have hl := hlim.neg
  have heq (k : ℕ) :
      -(∫ x in closedBall p r, φ x*D.interpolationDensity (D.index (j k)) t.val x*
        (localHessianAction m q w (θ k) (θ k) (Wθ k) (Wθ k) (Gθ k) x-
          localHessianAction m q w (η k) (η k) (Wη k) (Wη k) (Gη k) x) ∂m)=
      ∫ x in closedBall p r, φ x*(ε (D.index (j k))/2)^2*
        localHessianAction m q w (u k) (v k) (Wu k) (Wv k) (uv k) x ∂m := by
    have hid := D.velocity_hessian_identity ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν f A hf ha
      (D.index (j k)) t.val (isCompact_closedBall p r) (u k) (v k) (Wu k) (Wv k) (uv k)
      (θ k) (η k) (Wθ k) (Wη k) (Gθ k) (Gη k)
      (hu k) (hv k) (hWu k) (hWv k) (huv k) (hθ k) (hη k) (hWθ k) (hWη k) (hGθ k) (hGη k)
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hid] with x hx
    have hh := congrArg (fun z : ℝ => φ x*z) hx
    nlinarith only [hh]
  simpa only [neg_mul] using hl.congr' (Eventually.of_forall heq)


theorem local_scaled_intrinsic_hessian_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R r δ : ℝ} (hR : 1 ≤ R) (hr : 0 < r) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (t : InteriorHeatTime δ) (ht : δ < (t.val:ℝ))
    (φ : X → ℝ) (Lφ : ℝ≥0) (hφ : LipschitzWith Lφ φ) (hs : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hsupp : tsupport φ ⊆ closedBall p r)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) t.val) atTop (𝓝 Q₀))
    (u v Wu Wv uv : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p μ (D.left (D.index (j k))) (ε (D.index (j k))/4*t.val)
        (mul_pos (div_pos (hε _) (by norm_num)) t.val.property.1))
    (hv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p ν (D.right (D.index (j k))) (ε (D.index (j k))/4*(1-t.val))
        (mul_pos (div_pos (hε _) (by norm_num)) (sub_pos.mpr t.val.property.2)))
    (hWu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wu k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hWv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wv k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k))
    (huv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (uv k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (u k) (v k)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (v₀ : SobolevSpace m q) (V : X → ℝ) (Lv Av : ℝ≥0)
      (J : Lp ℝ 1 (m.restrict (closedBall p r))),
      LipschitzWith Lv V ∧ HasCompactSupport V ∧
      (SobolevSpace.toLp m q v₀ =ᵐ[m] V) ∧
      (∀ᵐ x ∂m, |SobolevSpace.toLp m q v₀ x| ≤ Av) ∧
      (SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p r)]
        D.forward.potential ((t.val:ℝ)/2)) ∧
      IsCanonicalHeatHessian m q w v₀ p r φ J ∧
      Tendsto (fun k => ∫ x in closedBall p r, φ x*(ε (D.index (j k))/2)^2*
        localHessianAction m q w (u k) (v k) (Wu k) (Wv k) (uv k) x ∂m)
        atTop (𝓝 (-(1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) := by
  intro m q w
  have hδ2 : 0 < δ/2 := half_pos hδ
  have htt : (t.val:ℝ)/2 ∈ Ioo (δ/2) 1 := ⟨by linarith,by linarith [t.val.property.2]⟩
  have hz x (hx : x ∉ closedBall p r) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hsupp hm))
  have hφB x : |φ x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  obtain ⟨v₀,V,Lv,Av,g,Wg,Gg,J,hV,hc,hv₀,hAv,hvloc,hcan,hg,hWg,hGg,_hL1,hJ⟩ :=
    D.forward_hessian_intrinsic_limit hK hε1
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT t.val hr hδ2 htt
      φ hφ hs hφB (fun x => (hφ01 x).1) hz f A hf ha j hj Q₀ hweak
  refine ⟨v₀,V,Lv,Av,J,hV,hc,hv₀,hAv,hvloc,hcan,?_⟩
  exact D.local_scaled_hessian_limit_of_forward hK hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hr hδ hS hT t ht
    φ Lφ hφ hs hφ01 hsupp f A hf ha j hj Q₀
    u v Wu Wv uv hu hv hWu hWv huv g Wg Gg J hg hWg hGg hJ


theorem local_scaled_hessian_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R r δ : ℝ} (hR : 1 ≤ R) (hr : 0 < r) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (t : InteriorHeatTime δ) (ht : δ < (t.val:ℝ))
    (φ : X → ℝ) (Lφ : ℝ≥0) (hφ : LipschitzWith Lφ φ) (hs : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hsupp : tsupport φ ⊆ closedBall p r)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) t.val) atTop (𝓝 Q₀))
    (u v Wu Wv uv : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p μ (D.left (D.index (j k))) (ε (D.index (j k))/4*t.val)
        (mul_pos (div_pos (hε _) (by norm_num)) t.val.property.1))
    (hv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p ν (D.right (D.index (j k))) (ε (D.index (j k))/4*(1-t.val))
        (mul_pos (div_pos (hε _) (by norm_num)) (sub_pos.mpr t.val.property.2)))
    (hWu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wu k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hWv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wv k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k))
    (huv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (uv k) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (u k) (v k)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ J : Lp ℝ 1 (m.restrict (closedBall p r)),
      Tendsto (fun k => ∫ x in closedBall p r, φ x*(ε (D.index (j k))/2)^2*
        localHessianAction m q w (u k) (v k) (Wu k) (Wv k) (uv k) x ∂m)
        atTop (𝓝 (-(1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) := by
  intro m q w
  obtain ⟨_v,_V,_Lv,_Av,J,_hV,_hc,_hv,_hAv,_hvloc,_hcan,hlim⟩ :=
    D.local_scaled_intrinsic_hessian_limit hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
      hR hr hδ hS hT t ht φ Lφ hφ hs hφ01 hsupp f A hf ha j hj Q₀ hweak
      u v Wu Wv uv hu hv hWu hWv huv
  exact ⟨J,hlim⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
