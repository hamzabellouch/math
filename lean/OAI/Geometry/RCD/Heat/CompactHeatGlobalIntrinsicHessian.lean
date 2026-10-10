import OAI.Geometry.RCD.Heat.CompactHeatGlobalHessianLimit
import OAI.Geometry.RCD.Sobolev.LocalHessianLimitPairing
import OAI.Geometry.RCD.Heat.CompactHeatLimitOptimalTriplets

namespace OAI

/-! # The full scaled heat Hessian has the canonical local action pairing -/

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

theorem global_scaled_intrinsic_hessian_limit (a₀ : S) (b₀ : T) (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
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
    (u v WU WV UV : ℕ → InteriorHeatTime δ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k t) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t.val)
        (mul_pos (div_pos (hε k) (by norm_num)) t.val.property.1))
    (hv : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k t) =ᵐ[hausdorff n X]
      hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t.val))
        (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.val.property.2)))
    (hWU : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WU k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k t))
    (hWV : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WV k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k t))
    (hUV : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (UV k t) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (u k t) (v k t))
    (j : ℕ → ℕ) (hj : StrictMono j) (t : InteriorHeatTime δ) (ht : δ < (t.val:ℝ))
    (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (j k)) t.val) atTop (𝓝 Q₀)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (v₀ : SobolevSpace m q) (V : X → ℝ) (Lv Av : ℝ≥0)
      (J : Lp ℝ 1 (m.restrict (closedBall p (6*R)))),
      LipschitzWith Lv V ∧ HasCompactSupport V ∧
      (SobolevSpace.toLp m q v₀ =ᵐ[m] V) ∧
      (∀ᵐ x ∂m, |SobolevSpace.toLp m q v₀ x| ≤ Av) ∧
      (SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p (6*R))]
        D.forward.potential ((t.val:ℝ)/2)) ∧
      IsCanonicalHeatHessian m q w v₀ p (6*R) (radialCutoff p (3*R)) J ∧
      Tendsto (fun k => ∫ x, (ε (D.index (j k))/2)^2*
        localHessianAction m q w (u (D.index (j k)) t) (v (D.index (j k)) t)
          (WU (D.index (j k)) t) (WV (D.index (j k)) t) (UV (D.index (j k)) t) x ∂m)
        atTop (𝓝 (-(1/4:ℝ)*(∫ x in closedBall p (6*R), J x ∂(Q₀ : Measure X)))) := by
  intro m q w
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have h3R : 0 < 3*R := by positivity
  have h6R : 0 < 6*R := by positivity
  have hδ2 : 0 < δ/2 := half_pos hδ
  have htt : (t.val:ℝ)/2 ∈ Ioo (δ/2) 1 := ⟨by linarith,by linarith [t.val.property.2]⟩
  obtain ⟨_P,_j,_hj,_hP,_hfirst,_hopt,_hgeo,hQball⟩ :=
    D.interpolation_limit_optimal_triplets a₀ b₀ hK hε1 hε0
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT t.val j hj Q₀ hweak
  obtain ⟨B,hB,hden⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  have hdom (k : ℕ) : (D.interpolationLaw (D.index (j k)) t.val : Measure X) ≤ ENNReal.ofReal B • m := by
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hden _ _ x))
  have hQac : (Q₀ : Measure X) ≪ m := Measure.absolutelyContinuous_of_le_smul
    (weak_probability_domination m _ Q₀ hweak ENNReal.ofReal_ne_top hdom)
  let φ₀ := radialCutoff p (3*R)
  have hzero₀ x (hx : x ∉ closedBall p (6*R)) : φ₀ x=0 := by
    apply radialCutoff_eq_zero p h3R
    have hh : 6*R < dist p x := by simpa only [mem_closedBall,not_le,dist_comm] using hx
    linarith
  have hbound₀ x : |φ₀ x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_bounds p (3*R) x).1]
    exact (radialCutoff_bounds p (3*R) x).2
  obtain ⟨v₀,V,Lv,Av,g₀,Wg₀,Gg₀,J₀,hV,hc,hv₀,hAv,hvloc,hcan,hg₀,hWg₀,hGg₀,hL₀,_hpair₀⟩ :=
    D.forward_hessian_intrinsic_limit hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
      hR hS hT t.val h6R hδ2 htt φ₀ (radialCutoff_lipschitz p h3R)
      (radialCutoff_hasCompactSupport p h3R) hbound₀
      (fun x => (radialCutoff_bounds p (3*R) x).1) hzero₀ f A hf ha j hj Q₀ hweak
  refine ⟨v₀,V,Lv,Av,J₀,hV,hc,hv₀,hAv,hvloc,hcan,?_⟩
  obtain ⟨L,hL,htail⟩ := D.scaled_hessian_uniform_tails hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hδ hS hT f A hf ha u v WU WV UV hu hv hWU hWV hUV
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hpowers : Tendsto (fun N : ℕ => (2:ℝ)^N*L) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hL0
  obtain ⟨M,hM⟩ := (hpowers.eventually (eventually_ge_atTop (6*R))).exists
  let r (N : ℕ) := (2:ℝ)^(N+M)*L
  have hr (N : ℕ) : 0 < r N := mul_pos (by positivity) hL0
  have hrbig (N : ℕ) : 6*R ≤ r N := hM.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left M N)) hL0.le)
  let φ (N : ℕ) := radialCutoff p (r N)
  let i (k : ℕ) := D.index (j k)
  let F k x := (ε (i k)/2)^2*localHessianAction m q w (u (i k) t) (v (i k) t)
    (WU (i k) t) (WV (i k) t) (UV (i k) t) x
  have hFi k : Integrable (F k) m :=
    (localHessianAction_integrable m q w (u (i k) t) (v (i k) t)
      (WU (i k) t) (WV (i k) t) (UV (i k) t)).const_mul _
  apply integral_tendsto_of_cutoffs m F φ (fun N => ball p (r N)) _ hFi
    (fun N => (radialCutoff_lipschitz p (hr N)).continuous.aestronglyMeasurable)
    (fun N x => radialCutoff_bounds p (r N) x)
    (fun N x hx => radialCutoff_eq_one p (hr N) (by simpa only [dist_comm] using (mem_ball.mp hx).le))
  · intro N
    have hz x (hx : x ∉ closedBall p (2*r N)) : φ N x=0 := by
      apply radialCutoff_eq_zero p (hr N)
      exact le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hx)
    have hs : tsupport (φ N) ⊆ closedBall p (2*r N) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      by_contra hn
      exact hx (hz x hn)
    have hbound x : |φ N x| ≤ (1:ℝ≥0) := by
      rw [abs_of_nonneg (radialCutoff_bounds p (r N) x).1]
      exact (radialCutoff_bounds p (r N) x).2
    obtain ⟨_vN,_VN,_LN,_AN,gN,WgN,GgN,JN,_hVN,_hcN,_hvN,_hAN,_hvlocN,_hcanN,
      hgN,hWgN,hGgN,hLN,hpairN⟩ :=
      D.forward_hessian_intrinsic_limit hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
        hR hS hT t.val (show 0 < 2*r N by positivity) hδ2 htt (φ N)
        (radialCutoff_lipschitz p (hr N)) (radialCutoff_hasCompactSupport p (hr N)) hbound
        (fun x => (radialCutoff_bounds p (r N) x).1) hz f A hf ha j hj Q₀ hweak
    have hsub : closedBall p (6*R) ⊆ closedBall p (2*r N) :=
      closedBall_subset_closedBall (by linarith [hrbig N])
    have heq : (∫ x in closedBall p (6*R), J₀ x ∂(Q₀ : Measure X)) =
        ∫ x in closedBall p (2*r N), JN x ∂(Q₀ : Measure X) := by
      apply local_hessian_limits_pairing_eq m q Q₀ hQac measurableSet_closedBall measurableSet_closedBall
        hsub w g₀ gN Wg₀ WgN Gg₀ GgN
        (fun k => (hg₀ k).trans (Filter.EventuallyEq.symm
          (ae_restrict_of_ae_restrict_of_subset hsub (hgN k))))
        hWg₀ hWgN hGg₀ hGgN φ₀ (φ N)
        (radialCutoff_lipschitz p h3R).continuous.aestronglyMeasurable
        (radialCutoff_lipschitz p (hr N)).continuous.aestronglyMeasurable 1 1
        (Eventually.of_forall hbound₀) (Eventually.of_forall hbound) hzero₀ hz _ _ J₀ JN hL₀ hLN
      · intro x hx
        exact radialCutoff_eq_one p (hr N)
          (by simpa only [dist_comm] using (mem_closedBall.mp hx).trans (hrbig N))
      · filter_upwards [hQball] with x hx
        exact radialCutoff_eq_one p h3R (by simpa only [dist_comm] using hx)
    have hlocal := D.local_scaled_hessian_limit_of_forward hK hε1 hε0
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR (show 0 < 2*r N by positivity)
      hδ hS hT t ht (φ N) _ (radialCutoff_lipschitz p (hr N))
      (radialCutoff_hasCompactSupport p (hr N)) (fun x => radialCutoff_bounds p (r N) x) hs
      f A hf ha j hj Q₀ (fun k => u (i k) t) (fun k => v (i k) t)
      (fun k => WU (i k) t) (fun k => WV (i k) t) (fun k => UV (i k) t)
      (fun k => hu (i k) t) (fun k => hv (i k) t) (fun k => hWU (i k) t)
      (fun k => hWV (i k) t) (fun k => hUV (i k) t) gN WgN GgN JN hgN hWgN hGgN hpairN
    rw [← heq] at hlocal
    apply hlocal.congr'
    refine Eventually.of_forall fun k => ?_
    calc
      _ = ∫ x, φ N x*(ε (i k)/2)^2*localHessianAction m q w (u (i k) t) (v (i k) t)
          (WU (i k) t) (WV (i k) t) (UV (i k) t) x ∂m := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [hz x hx,zero_mul,zero_mul]
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [F]; ring
  · apply Metric.tendstoUniformly_iff.mpr
    intro e he
    obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ((Metric.tendstoUniformly_iff.mp htail) e he)
    filter_upwards [eventually_ge_atTop N₀] with N hN k
    exact hN₀ (N+M) (by omega) (i k,t)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
