import OAI.Geometry.RCD.Heat.CompactHeatHessianTails

namespace OAI
/-! # A common integral bound for the actual scaled heat Hessian -/

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

theorem scaled_hessian_uniform_bound (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
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
      localGamma (hausdorff n X) hX.quadratic (u k t) (v k t)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (k : ℕ) (t : InteriorHeatTime δ),
      (∫ x, |(ε k/2)^2*localHessianAction m q w (u k t) (v k t)
        (WU k t) (WV k t) (UV k t) x| ∂m) ≤ B := by
  intro m q w
  obtain ⟨L,hL,htail⟩ := D.scaled_hessian_uniform_tails hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
    hR hδ hS hT f A hf ha u v WU WV UV hu hv hWU hWV hUV
  obtain ⟨N,hN⟩ := ((Metric.tendstoUniformly_iff.mp htail) 1 (by norm_num)).exists
  let r := (2:ℝ)^N*L
  have hr : 0 < r := mul_pos (by positivity) (lt_of_lt_of_le (by norm_num) hL)
  obtain ⟨M,C,E,_hM,hC,hE,hmeasure⟩ := D.scaled_hessian_density_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν (zero_le_one.trans hR) hδ hS hT f A hf ha
  obtain ⟨σ,hσ,_hmass,hpoint⟩ := hmeasure r hr
  let := hσ
  obtain ⟨Dρ,hDρ,hden⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  let P := Real.exp |K| *(4*C/δ+16*E*(R+r)^2/δ^2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  let B := Dρ*P*(m.real (closedBall p r)+σ.real (closedBall p r))+1
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro k t
  let F x := (ε k/2)^2*localHessianAction m q w (u k t) (v k t) (WU k t) (WV k t) (UV k t) x
  have hFi : Integrable F m := (localHessianAction_integrable m q w (u k t) (v k t)
    (WU k t) (WV k t) (UV k t)).const_mul _
  have hb : ∀ᵐ x ∂m.restrict (closedBall p r), |F x| ≤ Dρ*P*(1+(σ.rnDeriv m x).toReal) := by
    filter_upwards [hpoint k t (u k t) (v k t) (WU k t) (WV k t) (UV k t)
      (hu k t) (hv k t) (hWU k t) (hWV k t) (hUV k t),ae_restrict_mem measurableSet_closedBall]
      with x hx hm
    have hd : dist p x ≤ r := by simpa only [dist_comm] using mem_closedBall.mp hm
    have hp : Real.exp |K| *(4*C/δ+16*E*(R+dist p x)^2/δ^2) ≤ P := by
      dsimp only [P]
      gcongr
    have hn : 0 ≤ Real.exp |K| *(4*C/δ+16*E*(R+dist p x)^2/δ^2) := by positivity
    exact hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (hden k t.val x) hp hn hDρ.le) (by positivity))
  have hi := (integral_abs_le_full_mass m σ (isCompact_closedBall p r).measure_lt_top.ne
    hFi.aestronglyMeasurable.restrict (mul_nonneg hDρ.le hP) hb).2
  have htailk : (∫ x in (ball p r)ᶜ, |F x| ∂m) < 1 := by
    have hh := hN (k,t)
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] using hh
  have hcomp : (∫ x in (closedBall p r)ᶜ, |F x| ∂m) ≤ ∫ x in (ball p r)ᶜ, |F x| ∂m :=
    setIntegral_mono_set hFi.abs.integrableOn (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun x hx => (compl_subset_compl.mpr ball_subset_closedBall) hx)
  change (∫ x, |F x| ∂m) ≤ B
  rw [← integral_add_compl measurableSet_closedBall hFi.abs]
  dsimp only [B]
  linarith

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
