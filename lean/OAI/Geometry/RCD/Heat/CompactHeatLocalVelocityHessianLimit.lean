import OAI.Geometry.RCD.Heat.CompactHeatVelocityHessianData
import OAI.Geometry.RCD.Heat.CompactHeatVelocityHessianDecomposition
import OAI.Geometry.RCD.Heat.CompactHeatMixedOsmoticHessian
import OAI.Geometry.RCD.Heat.CompactHeatCommonHessianLimit

namespace OAI

/-! # The actual local velocity Hessian converges on the common law subsequence

The forward diagonal has a spatial L1 limit. The mixed osmotic term tends
to zero against the actual densities. The exact physical coefficient is 1/4.
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

theorem local_velocity_hessian_limit_of_forward (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
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
    (u Wu Gu : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        hX.fixedGaugeScaledPotential hn p μ (D.left (D.index k)) (ε (D.index k))
          (hε (D.index k)) (δ/2) (half_pos hδ) p ((t.val:ℝ)/2))
    (hWu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Wu k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hGu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (Gu k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (u k) (u k))
    (hJ : Tendsto (fun k => ∫ x, D.interpolationDensity (D.index (j k)) t.val x*
      (φ x*localHessianAction (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f)
        (u (j k)) (u (j k)) (Wu (j k)) (Wu (j k)) (Gu (j k)) x) ∂hausdorff n X)
      atTop (𝓝 (∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (θ η Wθ Wη Gθ Gη : ℕ → SobolevSpace m q),
      (∀ k, SobolevSpace.toLp m q (θ k) =ᵐ[m.restrict (closedBall p r)]
        D.velocityPotential (D.index (j k)) t.val) ∧
      (∀ k, SobolevSpace.toLp m q (η k) =ᵐ[m.restrict (closedBall p r)]
        D.osmoticPotential (D.index (j k)) t.val) ∧
      (∀ k, SobolevSpace.toLp m q (Wθ k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (θ k)) ∧
      (∀ k, SobolevSpace.toLp m q (Wη k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (η k)) ∧
      (∀ k, SobolevSpace.toLp m q (Gθ k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (θ k) (θ k)) ∧
      (∀ k, SobolevSpace.toLp m q (Gη k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (η k) (η k)) ∧
      Tendsto (fun k => ∫ x in closedBall p r,
        φ x*D.interpolationDensity (D.index (j k)) t.val x*
          (localHessianAction m q w (θ k) (θ k) (Wθ k) (Wθ k) (Gθ k) x-
            localHessianAction m q w (η k) (η k) (Wη k) (Wη k) (Gη k) x) ∂m)
        atTop (𝓝 ((1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) := by
  intro m q w
  classical
  let Ω := closedBall p r
  let i k := D.index (j k)
  have hi : StrictMono i := D.strict.comp hj
  have hδ2 : 0 < δ/2 := half_pos hδ
  have htt : (t.val:ℝ)/2 ∈ Ioo (δ/2) 1 := ⟨by linarith,by linarith [t.val.property.2]⟩
  have hz x (hx : x ∉ Ω) : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (hsupp hm))
  obtain ⟨e,v,We,Wv,Gev,he,hv,hWe,hWv,hGev,herr⟩ := D.local_mixed_osmotic_hessian_vanishes
    hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hr hS hT hδ
    φ Lφ hφ hs hφ01 hsupp f A hf ha
  choose θ η Wθ Wη Gθ Gη hθ hη hWθ hWη hGθ hGη using fun k =>
    D.local_velocity_hessian_data ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν f A hf ha
      (i k) t.val (isCompact_closedBall p r)
  have heη k : SobolevSpace.toLp m q (e (i k) t) =ᵐ[m.restrict Ω] SobolevSpace.toLp m q (η k) :=
    (he (i k) t).trans (hη k).symm
  have hvu k : SobolevSpace.toLp m q (v (i k) t) =ᵐ[m.restrict Ω] SobolevSpace.toLp m q (u (j k)) :=
    (hv (i k) t).trans (hu (j k)).symm
  have hWeη k : SobolevSpace.toLp m q (We (i k) t) =ᵐ[m.restrict Ω] SobolevSpace.toLp m q (Wη k) :=
    ((hWe (i k) t).trans (localGamma_pair_congr_ae m q EventuallyEq.rfl (heη k))).trans (hWη k).symm
  have hWvu k : SobolevSpace.toLp m q (Wv (i k) t) =ᵐ[m.restrict Ω] SobolevSpace.toLp m q (Wu (j k)) :=
    ((hWv (i k) t).trans (localGamma_pair_congr_ae m q EventuallyEq.rfl (hvu k))).trans (hWu (j k)).symm
  have hmix k : localHessianAction m q w (e (i k) t) (v (i k) t)
      (We (i k) t) (Wv (i k) t) (Gev (i k) t) =ᵐ[m.restrict Ω]
      localHessianAction m q w (η k) (u (j k)) (Wη k) (Wu (j k)) (Gev (i k) t) :=
    localHessianAction_congr m q EventuallyEq.rfl (heη k) (hvu k)
      (hWeη k) (hWvu k) EventuallyEq.rfl
  let W k x := φ x*D.interpolationDensity (i k) t.val x
  let E k x := localHessianAction m q w (η k) (u (j k)) (Wη k) (Wu (j k)) (Gev (i k) t) x
  have hW0 k x : 0 ≤ W k x := mul_nonneg (hφ01 x).1 (D.interpolationDensity_pos (i k) t.val x).le
  have herr' : Tendsto (fun k => ∫ x in Ω, W k x*|E k x| ∂m) atTop (𝓝 0) := by
    have hh := (herr.tendsto_at t).comp hi.tendsto_atTop
    apply hh.congr'
    apply Eventually.of_forall
    intro k
    apply integral_congr_ae
    filter_upwards [hmix k] with x hx
    dsimp only [Function.comp_apply,W,E]
    rw [hx]
  have hElim : Tendsto (fun k => ∫ x in Ω, W k x*E k x ∂m) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ herr'
    intro k
    calc
      ‖∫ x in Ω, W k x*E k x ∂m‖ ≤ ∫ x in Ω, |W k x*E k x| ∂m := norm_integral_le_integral_norm _
      _ = _ := by simp only [abs_mul,abs_of_nonneg (hW0 k _)]
  obtain ⟨C,hC,hden⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  have hWb k x : ‖W k x‖ ≤ C := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hW0 k x)]
    exact (mul_le_of_le_one_left (D.interpolationDensity_pos (i k) t.val x).le (hφ01 x).2).trans
      (hden (i k) t.val x)
  have hWi k : AEStronglyMeasurable (W k) m :=
    (hφ.continuous.mul (D.interpolationDensity_continuous (i k) t.val)).aestronglyMeasurable
  let U k x := localHessianAction m q w (u (j k)) (u (j k)) (Wu (j k)) (Wu (j k)) (Gu (j k)) x
  have hUi k : Integrable (fun x => W k x*U k x) (m.restrict Ω) :=
    ((localHessianAction_integrable m q w (u (j k)) (u (j k)) (Wu (j k)) (Wu (j k)) (Gu (j k))).bdd_mul
      (hWi k) (Eventually.of_forall (hWb k))).integrableOn
  have hEi k : Integrable (fun x => W k x*E k x) (m.restrict Ω) :=
    ((localHessianAction_integrable m q w (η k) (u (j k)) (Wη k) (Wu (j k)) (Gev (i k) t)).bdd_mul
      (hWi k) (Eventually.of_forall (hWb k))).integrableOn
  have hUlim : Tendsto (fun k => ∫ x in Ω, W k x*U k x ∂m) atTop
      (𝓝 (∫ x in Ω, J x ∂(Q₀ : Measure X))) := by
    apply hJ.congr'
    apply Eventually.of_forall
    intro k
    dsimp only
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)]
    · apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [W,U,i]; ring
    · intro x hx
      rw [hz x hx,zero_mul,mul_zero]
  refine ⟨θ,η,Wθ,Wη,Gθ,Gη,hθ,hη,hWθ,hWη,hGθ,hGη,?_⟩
  have hh := (hUlim.const_mul (1/4:ℝ)).sub hElim
  simp only [sub_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro k
  have hGev' := (hGev (i k) t).trans (localGamma_pair_congr_ae m q (heη k) (hvu k))
  have hdecomp := D.velocity_hessian_decomposition (i k) t.val hδ2 htt.1.le p Ω
    w (θ k) (η k) (u (j k)) (Wθ k) (Wη k) (Wu (j k)) (Gθ k) (Gη k) (Gu (j k)) (Gev (i k) t)
    (hθ k) (hη k) (hu (j k)) (hWθ k) (hWη k) (hWu (j k)) (hGθ k) (hGη k) (hGu (j k)) hGev'
  dsimp only
  rw [← integral_const_mul,← integral_sub ((hUi k).const_mul (1/4:ℝ)) (hEi k)]
  apply integral_congr_ae
  filter_upwards [hdecomp] with x hx
  dsimp only [W,U,E]
  rw [hx]
  ring


theorem local_velocity_intrinsic_hessian_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
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
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) t.val) atTop (𝓝 Q₀)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (v₀ : SobolevSpace m q) (V : X → ℝ) (Lv Av : ℝ≥0)
      (θ η Wθ Wη Gθ Gη : ℕ → SobolevSpace m q)
      (J : Lp ℝ 1 (m.restrict (closedBall p r))),
      LipschitzWith Lv V ∧ HasCompactSupport V ∧
      (SobolevSpace.toLp m q v₀ =ᵐ[m] V) ∧
      (∀ᵐ x ∂m, |SobolevSpace.toLp m q v₀ x| ≤ Av) ∧
      (SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p r)]
        D.forward.potential ((t.val:ℝ)/2)) ∧
      IsCanonicalHeatHessian m q w v₀ p r φ J ∧
      (∀ k, SobolevSpace.toLp m q (θ k) =ᵐ[m.restrict (closedBall p r)]
        D.velocityPotential (D.index (j k)) t.val) ∧
      (∀ k, SobolevSpace.toLp m q (η k) =ᵐ[m.restrict (closedBall p r)]
        D.osmoticPotential (D.index (j k)) t.val) ∧
      (∀ k, SobolevSpace.toLp m q (Wθ k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (θ k)) ∧
      (∀ k, SobolevSpace.toLp m q (Wη k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (η k)) ∧
      (∀ k, SobolevSpace.toLp m q (Gθ k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (θ k) (θ k)) ∧
      (∀ k, SobolevSpace.toLp m q (Gη k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (η k) (η k)) ∧
      Tendsto (fun k => ∫ x in closedBall p r,
        φ x*D.interpolationDensity (D.index (j k)) t.val x*
          (localHessianAction m q w (θ k) (θ k) (Wθ k) (Wθ k) (Gθ k) x-
            localHessianAction m q w (η k) (η k) (Wη k) (Wη k) (Gη k) x) ∂m)
        atTop (𝓝 ((1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) := by
  intro m q w
  have hδ2 : 0 < δ/2 := half_pos hδ
  have htt : (t.val:ℝ)/2 ∈ Ioo (δ/2) 1 := ⟨by linarith,by linarith [t.val.property.2]⟩
  have hz x (hx : x ∉ closedBall p r) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hsupp hm))
  have hφB x : |φ x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  obtain ⟨v₀,V,Lv,Av,u,Wu,Gu,J,hV,hc,hv₀,hAv,hvloc,hcan,hu,hWu,hGu,_hL1,hJ⟩ :=
    D.forward_hessian_intrinsic_limit hK hε1
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT t.val hr hδ2 htt
      φ hφ hs hφB (fun x => (hφ01 x).1) hz f A hf ha j hj Q₀ hweak
  obtain ⟨θ,η,Wθ,Wη,Gθ,Gη,hθ,hη,hWθ,hWη,hGθ,hGη,hlim⟩ :=
    D.local_velocity_hessian_limit_of_forward hK hε1 hε0
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hr hδ hS hT t ht
      φ Lφ hφ hs hφ01 hsupp f A hf ha j hj Q₀ u Wu Gu J hu hWu hGu hJ
  exact ⟨v₀,V,Lv,Av,θ,η,Wθ,Wη,Gθ,Gη,J,hV,hc,hv₀,hAv,hvloc,hcan,
    hθ,hη,hWθ,hWη,hGθ,hGη,hlim⟩


theorem local_velocity_hessian_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
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
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) t.val) atTop (𝓝 Q₀)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (θ η Wθ Wη Gθ Gη : ℕ → SobolevSpace m q)
      (J : Lp ℝ 1 (m.restrict (closedBall p r))),
      (∀ k, SobolevSpace.toLp m q (θ k) =ᵐ[m.restrict (closedBall p r)]
        D.velocityPotential (D.index (j k)) t.val) ∧
      (∀ k, SobolevSpace.toLp m q (η k) =ᵐ[m.restrict (closedBall p r)]
        D.osmoticPotential (D.index (j k)) t.val) ∧
      (∀ k, SobolevSpace.toLp m q (Wθ k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (θ k)) ∧
      (∀ k, SobolevSpace.toLp m q (Wη k) =ᵐ[m.restrict (closedBall p r)] localGamma m q w (η k)) ∧
      (∀ k, SobolevSpace.toLp m q (Gθ k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (θ k) (θ k)) ∧
      (∀ k, SobolevSpace.toLp m q (Gη k) =ᵐ[m.restrict (closedBall p r)] localGamma m q (η k) (η k)) ∧
      Tendsto (fun k => ∫ x in closedBall p r,
        φ x*D.interpolationDensity (D.index (j k)) t.val x*
          (localHessianAction m q w (θ k) (θ k) (Wθ k) (Wθ k) (Gθ k) x-
            localHessianAction m q w (η k) (η k) (Wη k) (Wη k) (Gη k) x) ∂m)
        atTop (𝓝 ((1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ : Measure X)))) := by
  intro m q w
  obtain ⟨_v,_V,_Lv,_Av,θ,η,Wθ,Wη,Gθ,Gη,J,_hV,_hc,_hv,_hAv,_hvloc,_hcan,
    hθ,hη,hWθ,hWη,hGθ,hGη,hlim⟩ :=
    D.local_velocity_intrinsic_hessian_limit hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
      hR hr hδ hS hT t ht φ Lφ hφ hs hφ01 hsupp f A hf ha j hj Q₀ hweak
  exact ⟨θ,η,Wθ,Wη,Gθ,Gη,J,hθ,hη,hWθ,hWη,hGθ,hGη,hlim⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
