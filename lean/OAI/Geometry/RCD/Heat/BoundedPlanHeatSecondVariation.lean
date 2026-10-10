import OAI.Geometry.RCD.Heat.UniformCenteredSecondVariation
import OAI.Geometry.RCD.Heat.CompactHeatActualPlanLimit
import OAI.Geometry.RCD.Metric.DominatedCompactProbability
import OAI.Geometry.RCD.Transport.CompressedFiniteUnique

namespace OAI

/-! # Local heat second variation on the prescribed compressed optimal plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_plan_heat_second_variation (p₀ p : X) (hK : K ≤ 0)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ B • hausdorff n X)
    {R₀ r : ℝ} (hR₀ : 0 ≤ R₀) (hr : 0 < r) (hsmall : 6*R₀ ≤ r)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R₀)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R₀)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s : ℝ} (hs : 0 < s) :
    let m := hausdorff n X
    let q := hX.quadratic
    let H := kernelHeat m q (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f
    let F t := if ht : t ∈ Ioo (0:ℝ) 1 then
      ∫ x, H x ∂π.map (fun γ => γ (⟨t,ht.1.le,ht.2.le⟩ : Time)) else 0
    let w := heatSobolev m q s hs f
    let C := hX.centeredActionBound hn p₀
    ∃ G : ℝ → ℝ,
      (∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ F t) ∧
      (∀ a b : ℝ, 0 < a → b < 1 → ∃ L : ℝ≥0, LipschitzOnWith L (deriv F) (Icc a b)) ∧
      (∀ (δ : ℝ) (hδ : 0 < δ),
        let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| * (16*C*(R₀+32*r)^2/(δ/2)^2)),Real.sqrt_nonneg _⟩
        ∀ (t : ℝ) (ht : t ∈ Ioo δ 1), ∃ (v : SobolevSpace m q) (V : X → ℝ)
        (J : Lp ℝ 1 (m.restrict (closedBall p r))),
        LipschitzWith (3*L) V ∧ HasCompactSupport V ∧
        (SobolevSpace.toLp m q v =ᵐ[m] V) ∧
        (∀ x, |V x| ≤ 2*r*(L:ℝ)) ∧
        IsCanonicalHeatHessian m q w v p r (radialCutoff p (r/2)) J ∧
        G t = (1/4:ℝ)*(∫ x in closedBall p r, J x ∂π.map
          (fun γ => γ (⟨t,(hδ.trans ht.1).le,ht.2.le⟩ : Time)))) ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
        IntervalIntegrable G volume a b ∧ (∫ t in a..b, G t) = deriv F b-deriv F a := by
  intro m q H F w C
  let S := closedBall p R₀
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall p R₀)
  have hsupport (t : Time) (ht : ∀ᵐ x ∂π.map (fun γ => γ t), dist x p ≤ R₀) :
      ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ S := by
    simpa only [S,mem_closedBall] using ht
  obtain ⟨μ,ρ₀,B₀,hprob₀,hμ,hm₀,hp₀,hC₀,hd₀⟩ :=
    dominated_supported_probability_law m (π.map (fun γ => γ 0)) S measurableSet_closedBall
      (hsupport 0 hs₀) hB (hcomp 0)
  obtain ⟨ν,ρ₁,B₁,hprob₁,hν,hm₁,hp₁,hC₁,hd₁⟩ :=
    dominated_supported_probability_law m (π.map (fun γ => γ 1)) S measurableSet_closedBall
      (hsupport 1 hs₁) hB (hcomp 1)
  let := hprob₀
  let := hprob₁
  obtain ⟨a₀⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨b₀⟩ := nonempty_of_isProbabilityMeasure ν
  let R := max 1 r
  have hR : 1 ≤ R := le_max_left _ _
  have hS₀ (y : S) : dist p y ≤ R₀ := by
    simpa only [S,mem_closedBall,dist_comm] using y.property
  have hS (y : S) : dist p y ≤ R := (hS₀ y).trans
    ((by linarith : R₀ ≤ r).trans (le_max_right _ _))
  have he1 (k : ℕ) : heatStep k ≤ 1 := by
    unfold heatStep
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨D⟩ := hX.exists_compact_heat_scaling_data hn p hK a₀ b₀ μ ν
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hd₀ hd₁ heatStep heatStep_pos he1 heatStep_tendsto
    (zero_le_one.trans hR) hS hS
  obtain ⟨π',j,B',_A,hj,hB',hg',hop',_hlen,hcomp',_hfor,_hback,hweak,_hcal⟩ :=
    D.exists_actual_heat_limit_plan a₀ b₀ hK he1 heatStep_tendsto
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hd₀ hd₁ hR hS hS
  have hop : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))) := by rw [hμ,hν]; exact hopt
  have heq : π=(π' : Measure C(Time,X)) :=
    hX.compressed_plan_unique_finite hn p hR₀ π π' hgeo hg' hop hop' hB hB' hcomp hcomp'
      (hμ.symm ▸ hs₀) (hν.symm ▸ hs₁)
  let Q₀ (t : Ioo (0:ℝ) 1) : ProbabilityMeasure X :=
    ⟨π.map (fun γ => γ (⟨t,t.property.1.le,t.property.2.le⟩ : Time)),
      inferInstance⟩
  have hQ (t : Ioo (0:ℝ) 1) :
      Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop (𝓝 (Q₀ t)) := by
    have hqt : Q₀ t=π'.map (fun γ => γ (⟨t,t.property.1.le,t.property.2.le⟩ : Time)) := by
      apply ProbabilityMeasure.toMeasure_injective
      exact congrArg (fun ρ : Measure C(Time,X) => ρ.map
        (fun γ => γ (⟨t,t.property.1.le,t.property.2.le⟩ : Time))) heq
    rw [hqt]
    exact (hweak t).1
  have hbound := optimal_geodesic_plan_bounded (π.map (fun γ => γ 0))
    (π.map (fun γ => γ 1)) π hgeo hopt p hR₀ hs₀ hs₁
  have hstay (t : Ioo (0:ℝ) 1) : ∀ᵐ x ∂(Q₀ t : Measure X), x∈closedBall p (r/2) := by
    apply (ae_map_iff (measurable_path_eval _).aemeasurable measurableSet_closedBall).mpr
    filter_upwards [hbound] with γ hγ
    exact (hγ.2 _).trans (by linarith)
  obtain ⟨G,hder,hLip,hident,hint⟩ := D.centered_limit_mean_second_variation_uniform p₀
    a₀ b₀ hK he1 heatStep_tendsto ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hd₀ hd₁ hR hS hS
    j hj Q₀ hQ hr ((le_max_right 1 r).trans (by linarith)) hstay hR₀ hS₀ f A hf hs
  refine ⟨G,hder,hLip,?_,hint⟩
  intro δ hδ L t ht
  obtain ⟨v,V,J,hV,hVc,hv,hVb,_hloc,hcan,hGi⟩ := hident δ hδ t ht
  exact ⟨v,V,J,hV,hVc,hv,hVb,hcan,hGi⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
