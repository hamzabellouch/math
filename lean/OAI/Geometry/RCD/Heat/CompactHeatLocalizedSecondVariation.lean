import OAI.Geometry.RCD.Heat.CompactHeatIntrinsicSecondVariation
import OAI.Geometry.RCD.Sobolev.CanonicalHessianInnerPairing

namespace OAI

/-! # Second variation localized to an arbitrary positive physical radius -/

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

theorem localized_limit_mean_second_variation (a₀ : S) (b₀ : T) (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : Ioo (0:ℝ) 1 → ProbabilityMeasure X)
    (hweak : ∀ t, Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop (𝓝 (Q₀ t)))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ 3*R)
    (hstay : ∀ t, ∀ᵐ x ∂(Q₀ t : Measure X), x∈closedBall p (r/2))
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s : ℝ} (hs : 0 < s) :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f
    let F t := if ht : t ∈ Ioo (0:ℝ) 1 then ∫ x, H x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q s hs f
    ∃ G : ℝ → ℝ,
      (∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ F t) ∧
      (∀ a b : ℝ, 0 < a → b < 1 → ∃ L : ℝ≥0, LipschitzOnWith L (deriv F) (Icc a b)) ∧
      (∀ t : Ioo (0:ℝ) 1, ∃ (v₀ : SobolevSpace m q) (V : X → ℝ) (Lv Av : ℝ≥0)
        (J : Lp ℝ 1 (m.restrict (closedBall p r))),
        LipschitzWith Lv V ∧ HasCompactSupport V ∧
        (SobolevSpace.toLp m q v₀ =ᵐ[m] V) ∧
        (∀ᵐ x ∂m, |SobolevSpace.toLp m q v₀ x| ≤ Av) ∧
        (SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p r)]
          D.forward.potential ((t:ℝ)/2)) ∧
        IsCanonicalHeatHessian m q w v₀ p r (radialCutoff p (r/2)) J ∧
        G t = (1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ t : Measure X))) ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
        IntervalIntegrable G volume a b ∧ (∫ t in a..b, G t) = deriv F b-deriv F a := by
  intro H F m q w
  obtain ⟨G,hder,hLip,hident,hint⟩ := D.intrinsic_limit_mean_second_variation
    a₀ b₀ hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT
    j hj Q₀ hweak f A hf hs
  obtain ⟨B,_hB,hden⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  have hQ (t : Ioo (0:ℝ) 1) : (Q₀ t : Measure X) ≪ m := by
    apply Measure.absolutelyContinuous_of_le_smul
    apply weak_probability_domination m _ _ (hweak t) ENNReal.ofReal_ne_top
    intro k
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hden _ _ x))
  have h3R : 0 < 3*R := by linarith
  let ψ := radialCutoff p (3*R)
  let φ := radialCutoff p (r/2)
  have hψ : AEStronglyMeasurable ψ m := (radialCutoff_lipschitz p h3R).continuous.aestronglyMeasurable
  have hφ : AEStronglyMeasurable φ m := (radialCutoff_lipschitz p (half_pos hr)).continuous.aestronglyMeasurable
  have hψb : ∀ᵐ x ∂m, |ψ x| ≤ (1:ℝ≥0) := Eventually.of_forall fun x => by
    rw [abs_of_nonneg (radialCutoff_bounds p (3*R) x).1]
    exact (radialCutoff_bounds p (3*R) x).2
  have hφb : ∀ᵐ x ∂m, |φ x| ≤ (1:ℝ≥0) := Eventually.of_forall fun x => by
    rw [abs_of_nonneg (radialCutoff_bounds p (r/2) x).1]
    exact (radialCutoff_bounds p (r/2) x).2
  have hψone : ∀ x∈closedBall p r, ψ x=1 := by
    intro x hx
    apply radialCutoff_eq_one p h3R
    have hx' : dist p x ≤ r := by simpa only [mem_closedBall,dist_comm] using hx
    exact hx'.trans hrR
  have hφz : ∀ x∉closedBall p r, φ x=0 := by
    intro x hx
    apply radialCutoff_eq_zero p (half_pos hr)
    have hh : r < dist p x := by simpa only [mem_closedBall,dist_comm,not_le] using hx
    linarith
  refine ⟨G,hder,hLip,?_,hint⟩
  intro t
  obtain ⟨v₀,V₀,L₀,A₀,J₀,hV₀,hVc₀,hv₀,hA₀,hvloc₀,hcan₀,hGi⟩ := hident t
  have hδ : 0 < (t:ℝ)/4 := by linarith [t.property.1]
  have htt : (t:ℝ)/2 ∈ Ioo ((t:ℝ)/4) 1 := by constructor <;> linarith [t.property.1,t.property.2]
  obtain ⟨v,V,Lv,Av,hV,hVc,hv,hAv,hvloc⟩ := hX.compact_heat_action_realization hn p hK
    μ ρ₀ hm₀ hp₀ hC₀ hμ D.left D.left_pos ε hε hε1 p D.index D.forward.potential
    D.forward_limit hr hδ htt (zero_le_one.trans hR) hS
  obtain ⟨J,hcan,_⟩ := hX.exists_canonical_heat_hessian hn p hK f A hf hs hr
    v V Lv Av hV hVc hv hAv φ hφ 1 hφb hφz
  have hvz : SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p r)] SobolevSpace.toLp m q v :=
    by
      have hold : SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p r)]
          D.forward.potential ((t:ℝ)/2) :=
        ae_restrict_of_ae_restrict_of_subset (closedBall_subset_closedBall (by linarith : r ≤ 6*R)) hvloc₀
      exact hold.trans hvloc.symm
  have hpair := hX.canonical_hessian_inner_pairing hn p hK f A hf hs hr (by linarith : r ≤ 6*R)
    v₀ v V₀ V L₀ Lv A₀ Av hV₀ hV hVc₀ hVc hv₀ hv hA₀ hAv hvz
    ψ φ hψ hφ 1 1 hψb hφb hψone hφz J₀ J hcan₀ hcan (Q₀ t : Measure X) (hQ t)
    ((hstay t).mono fun x hx => (closedBall_subset_closedBall (by linarith : r/2 ≤ r)) hx)
    ((hstay t).mono fun x hx => radialCutoff_eq_one p (half_pos hr)
      (by simpa only [mem_closedBall,dist_comm] using hx))
  exact ⟨v,V,Lv,Av,J,hV,hVc,hv,hAv,hvloc,hcan,hGi.trans (congrArg (fun z : ℝ => (1/4:ℝ)*z) hpair.symm)⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
