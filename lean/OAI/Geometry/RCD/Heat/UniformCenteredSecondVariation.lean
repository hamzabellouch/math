import OAI.Geometry.RCD.Heat.CompactHeatLocalizedSecondVariation
import OAI.Geometry.RCD.Heat.HeatActionBasepoint
import OAI.Geometry.RCD.Sobolev.CanonicalHessianConstantShift

namespace OAI

/-! # A common second-variation constant for moving physical centers -/

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

theorem centered_limit_mean_second_variation_uniform (p₀ : X) (a₀ : S) (b₀ : T) (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
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
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hS₀ : ∀ y:S, dist p y ≤ R₀)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s : ℝ} (hs : 0 < s) :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f
    let F t := if ht : t ∈ Ioo (0:ℝ) 1 then ∫ x, H x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q s hs f
    let C := hX.centeredActionBound hn p₀
    ∃ G : ℝ → ℝ,
      (∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ F t) ∧
      (∀ a b : ℝ, 0 < a → b < 1 → ∃ L : ℝ≥0, LipschitzOnWith L (deriv F) (Icc a b)) ∧
      (∀ (δ : ℝ) (hδ : 0 < δ),
        let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| * (16*C*(R₀+32*r)^2/(δ/2)^2)),Real.sqrt_nonneg _⟩
        ∀ (t : ℝ) (ht : t ∈ Ioo δ 1), ∃ (v₀ : SobolevSpace m q) (V : X → ℝ)
        (J : Lp ℝ 1 (m.restrict (closedBall p r))),
        LipschitzWith (3*L) V ∧ HasCompactSupport V ∧
        (SobolevSpace.toLp m q v₀ =ᵐ[m] V) ∧
        (∀ x, |V x| ≤ 2*r*(L:ℝ)) ∧
        (SobolevSpace.toLp m q v₀ =ᵐ[m.restrict (closedBall p r)]
          fun x => D.forward.potential (t/2) x-D.forward.potential (t/2) p) ∧
        IsCanonicalHeatHessian m q w v₀ p r (radialCutoff p (r/2)) J ∧
        G t = (1/4:ℝ)*(∫ x in closedBall p r, J x ∂(Q₀ ⟨t,lt_trans hδ ht.1,ht.2⟩ : Measure X))) ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
        IntervalIntegrable G volume a b ∧ (∫ t in a..b, G t) = deriv F b-deriv F a := by
  intro H F m q w C
  have hreal := (Classical.choose_spec
    (hX.uniform_centered_heat_action_realization hn p₀)).2 p μ
  obtain ⟨G,hder,hLip,hident,hint⟩ := D.localized_limit_mean_second_variation
    a₀ b₀ hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT
    j hj Q₀ hweak hr hrR hstay f A hf hs
  refine ⟨G,hder,hLip,?_,hint⟩
  intro δ hδ L t ht
  let t' : Ioo (0:ℝ) 1 := ⟨t,hδ.trans ht.1,ht.2⟩
  obtain ⟨v₀,V₀,L₀,A₀,J₀,hV₀,hVc₀,hv₀,hA₀,hvloc₀,hcan₀,hGi⟩ := hident t'
  have htt : t/2 ∈ Ioo (δ/2) 1 := by constructor <;> linarith [ht.1,ht.2]
  obtain ⟨v,V,hV,hVc,hv,hVb,hvloc⟩ := hreal ρ₀ hm₀ hp₀ hC₀ hμ
    D.left D.left_pos ε hε hε1 hε0 p D.index D.forward.potential D.strict.tendsto_atTop
    D.forward_limit hR₀ hS₀ hr (half_pos hδ) (t/2) htt
  let Av : ℝ≥0 := ⟨2*r*(L:ℝ),by positivity⟩
  have hAv : ∀ᵐ x ∂m, |SobolevSpace.toLp m q v x| ≤ Av := by
    filter_upwards [hv] with x hx
    rw [hx]
    exact hVb x
  let φ := radialCutoff p (r/2)
  have hφ : AEStronglyMeasurable φ m :=
    (radialCutoff_lipschitz p (half_pos hr)).continuous.aestronglyMeasurable
  have hφb : ∀ᵐ x ∂m, |φ x| ≤ (1:ℝ≥0) := Eventually.of_forall fun x => by
    rw [abs_of_nonneg (radialCutoff_bounds p (r/2) x).1]
    exact (radialCutoff_bounds p (r/2) x).2
  have hφz : ∀ x∉closedBall p r, φ x=0 := by
    intro x hx
    apply radialCutoff_eq_zero p (half_pos hr)
    have hh : r < dist p x := by simpa only [mem_closedBall,dist_comm,not_le] using hx
    linarith
  obtain ⟨J,hcan,_⟩ := hX.exists_canonical_heat_hessian hn p hK f A hf hs hr
    v V (3*L) Av hV hVc hv hAv φ hφ 1 hφb hφz
  have hshift : (fun x => SobolevSpace.toLp m q v x-SobolevSpace.toLp m q v₀ x)
      =ᵐ[m.restrict (closedBall p r)] fun _ => -D.forward.potential (t/2) p := by
    filter_upwards [hvloc,hvloc₀] with x hx hy
    change SobolevSpace.toLp m q v₀ x=D.forward.potential (t/2) x at hy
    rw [hx,hy]
    ring
  have heq := hX.canonical_hessian_locality_of_constant hn p hK f A hf hs hr
    v₀ v V₀ V L₀ (3*L) A₀ Av hV₀ hV hVc₀ hVc hv₀ hv hA₀ hAv
    (-D.forward.potential (t/2) p) hshift φ hφ 1 hφb hφz J₀ J hcan₀ hcan
  refine ⟨v,V,J,hV,hVc,hv,hVb,hvloc,hcan,?_⟩
  simpa only [heq] using hGi

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
