import OAI.Geometry.RCD.Heat.CompactHeatIntrinsicSecondVariation
import OAI.Geometry.RCD.Sobolev.CanonicalHessianLocality
import OAI.Geometry.RCD.Heat.UniformHeatActionRealization
import OAI.Geometry.RCD.Harmonic.UniformLocalL1Pairing
import OAI.Geometry.RCD.Heat.HeatCanonicalHessianVanishing

namespace OAI

/-! # Vanishing second variation for the heat approximations of an original harmonic coordinate -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} {hX : NoncollapsedRCD 0 n X} {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem harmonic_heat_second_variation (a₀ : S) (b₀ : T)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : Ioo (0:ℝ) 1 → ProbabilityMeasure X)
    (hweak : ∀ t, Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop (𝓝 (Q₀ t)))
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {b : ℝ} (hb : 24*R < b)
    (hd0 : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => 0) (c : ℝ)
    (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hs0 : Tendsto s atTop (𝓝 0)) :
    let H k := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) (s k)
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic u)
    let F k t := if ht : t ∈ Ioo (0:ℝ) 1 then ∫ x, H k x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    ∃ G : ℕ → ℝ → ℝ,
      (∀ k t, t ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ (F k) t) ∧
      (∀ k a b, 0 < a → a ≤ b → b < 1 →
        IntervalIntegrable (G k) volume a b ∧
          (∫ t in a..b, G k t) = deriv (F k) b-deriv (F k) a) ∧
      ∀ a b, 0 < a → a ≤ b → b < 1 →
        TendstoUniformlyOn G (fun _ => 0) atTop (Icc a b) := by
  intro H F
  let m := hausdorff n X
  let q := hX.quadratic
  let f := SobolevSpace.toLp m q u
  choose G hdiff _hLip hident hint using fun k => D.intrinsic_limit_mean_second_variation
    a₀ b₀ le_rfl hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT j hj Q₀ hweak f A hA (hs k)
  refine ⟨G,hdiff,hint,?_⟩
  intro a e ha _hae he
  have h6R : 0 < 6*R := by linarith
  have h3R : 0 < 3*R := by linarith
  have hδ : 0 < a/4 := by positivity
  let Y := Icc a e
  have htime (t : Y) : (t:ℝ)/2 ∈ Ioo (a/4) 1 := by
    constructor <;> linarith [t.property.1,t.property.2]
  have ht01 (t : Y) : (t:ℝ) ∈ Ioo (0:ℝ) 1 := by
    constructor <;> linarith [t.property.1,t.property.2]
  obtain ⟨Lv,Av,hreal⟩ := hX.uniform_compact_heat_action_realization hn p le_rfl
    μ ρ₀ hm₀ hp₀ hC₀ hμ D.left D.left_pos ε hε hε1 p D.index D.forward.potential
    D.forward_limit h6R hδ (zero_le_one.trans hR) hS
  choose v V hV hVc hvr hAv hvloc using fun t : Y => hreal ((t:ℝ)/2) (htime t)
  let φ := radialCutoff p (3*R)
  have hφ : AEStronglyMeasurable φ m := (radialCutoff_lipschitz p h3R).continuous.aestronglyMeasurable
  have hφb : ∀ᵐ x ∂m, |φ x| ≤ (1:ℝ≥0) := Eventually.of_forall fun x => by
    rw [abs_of_nonneg (radialCutoff_bounds p (3*R) x).1]
    exact (radialCutoff_bounds p (3*R) x).2
  have hφz (x : X) (hx : x ∉ closedBall p (6*R)) : φ x=0 := by
    apply radialCutoff_eq_zero p h3R
    have hh : 6*R < dist p x := by simpa only [mem_closedBall,dist_comm,not_le] using hx
    linarith
  have hex (k : ℕ) (t : Y) : ∃ J : Lp ℝ 1 (m.restrict (closedBall p (6*R))),
      IsCanonicalHeatHessian m q (heatSobolev m q (s k) (hs k) f) (v t) p (6*R) φ J := by
    obtain ⟨J,hJ,_⟩ := hX.exists_canonical_heat_hessian hn p le_rfl f A hA (hs k) h6R
      (v t) (V t) Lv Av (hV t) (hVc t) (hvr t) (hAv t) φ hφ 1 hφb hφz
    exact ⟨J,hJ⟩
  choose J hJ using hex
  have hnorm := hX.heat_canonical_hessian_vanishes hn p u d hd U L A hU hUc hu hA h6R
    (show 4*(6*R)<b by linarith) hd0 c hc s hs hs0 v V Lv (fun _ => Av) hV hVc hvr hAv
    φ hφ 1 hφb J hJ
  obtain ⟨B,_hB,hden⟩ := D.interpolationDensity_uniform_bound le_rfl hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  have hQ (t : Y) : (Q₀ ⟨t,ht01 t⟩ : Measure X) ≤ ENNReal.ofReal B • m := by
    apply weak_probability_domination m _ _ (hweak ⟨t,ht01 t⟩) ENNReal.ofReal_ne_top
    intro k
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hden _ _ x))
  have hlaw := uniform_local_L1_pairing m (fun t : Y => (Q₀ ⟨t,ht01 t⟩ : Measure X))
    ENNReal.ofReal_ne_top hQ J hnorm
  have hG (k : ℕ) (t : Y) : G k t=(1/4:ℝ)*(∫ x in closedBall p (6*R), J k t x ∂(Q₀ ⟨t,ht01 t⟩ : Measure X)) := by
    obtain ⟨v₀,V₀,L₀,A₀,I,hV₀,hVc₀,hv₀,hA₀,hvloc₀,hcan₀,hGi⟩ := hident k ⟨t,ht01 t⟩
    have hvz := hvloc₀.trans (Filter.EventuallyEq.symm (hvloc t))
    have heq := hX.canonical_hessian_locality hn p le_rfl f A hA (hs k) h6R
      v₀ (v t) V₀ (V t) L₀ Lv A₀ Av hV₀ (hV t) hVc₀ (hVc t) hv₀ (hvr t) hA₀ (hAv t)
      hvz φ hφ 1 hφb hφz I (J k t) hcan₀ (hJ k t)
    rwa [heq] at hGi
  apply tendstoUniformlyOn_iff_restrict.mpr
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [(Metric.tendstoUniformly_iff.mp hlaw) δ hδ] with k hk t
  have hh := hk t
  change dist (0:ℝ) (G k t) < δ
  rw [hG k t]
  simp only [dist_zero_left,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/4)] at hh ⊢
  nlinarith [abs_nonneg (∫ x in closedBall p (6*R), J k t x ∂(Q₀ ⟨t,ht01 t⟩ : Measure X))]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
