import OAI.Geometry.RCD.Transport.DimensionalSubgradient

namespace OAI

/-! # An actual compact optimal potential with the dimensional subgradient bound

This is the bounded square-root-core specialization of EKS Theorem 3.17,
equation (3.24). The potential and the transport plan are constructed from
the original RCD structure; no dimensional evolution inequality is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem sqrt_core_dimensional_potential (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hhn : ∀ x, 0 ≤ h x)
    (hi : Integrable h (hausdorff n X))
    (hrep : (SobolevSpace.toLp _ hX.quadratic ρ : X → ℝ) =ᵐ[hausdorff n X] fun x => h x^2)
    (hν : ν₀=(hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x))) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (φ ψ : X → ℝ),
      LipschitzWith ⟨5*R,by positivity⟩ φ ∧ LipschitzWith ⟨5*R,by positivity⟩ ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 10*R^2) ∧ (∀ x, -10*R^2 ≤ ψ x ∧ ψ x ≤ 0) ∧
      tsupport φ ⊆ closedBall p (R+(5*R)) ∧ tsupport ψ ⊆ closedBall p (R+(5*R)) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁)=(wassersteinSq ν₀ ν₁).toReal/2 ∧
      -energyForm (hausdorff n X) hX.quadratic u ρ ≤
        entropyPowerRate N (-(K*(wassersteinSq ν₀ ν₁).toReal/N))
          (Real.exp (-boltzmannEntropy (hausdorff n X) ν₀/N))
          (Real.exp (-boltzmannEntropy (hausdorff n X) ν₁/N)) := by
  let μ := hausdorff n X
  let : μ.Regular := inferInstance
  obtain ⟨π,hπ,hg,hp,hdi,hall⟩ := hX.exists_bounded_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1
  let := hπ
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  obtain ⟨u,φ,ψ,hφ,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,hu,had,hcontact,hb⟩ :=
    hp.linear_radius_bounded_sobolev_potential μ hX.quadratic hX.geodesic ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0) p hR hs0 hs1
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hcontactπ := ae_of_ae_map hm.aemeasurable hcontact
  have hbπ := ae_of_ae_map hm.aemeasurable hb
  let a : RenyiTransportNode n X :=
    ⟨ν₀,ν₁,inferInstance,inferInstance,p,R,hR,hs0,hs1,C,hC,h0,h1,2*R,
      mul_nonneg (by norm_num) hR,optimalPlanDistanceBound_of_bounded ν₀ ν₁ p hs0 hs1⟩
  let D := compressionBudget K n (2*R) C
  have hD : D ≠ ∞ := compressionBudget_ne_top K n (2*R) hC
  let M : ℝ≥0 := ⟨D.toReal+1,by positivity⟩
  have hM : 0 < M := by change 0 < D.toReal+1; positivity
  have hDM : D ≤ ENNReal.ofReal M := by
    rw [←ENNReal.ofReal_toReal hD]
    exact ENNReal.ofReal_le_ofReal (by change D.toReal ≤ D.toReal+1; linarith)
  have hcM (t : Time) : π.map (fun γ => γ t) ≤ ENNReal.ofReal M • μ := by
    apply (hall t).1.trans
    intro S
    exact mul_le_mul' hDM le_rfl
  have hbound := hX.entropic_plan_subgradient hn hK hN a π hg hp hM hcM u ρ hh hhn hi hrep hν
    hu had hcontactπ hbπ
  refine ⟨u,φ,ψ,hφ,hψ,hφb,hψb,htφ,htψ,hsφ,hsψ,hu,had,?_,hbound⟩
  have hφi : Integrable φ ν₀ := hφ.continuous.integrable_of_hasCompactSupport hsφ
  have hψi : Integrable ψ ν₁ := hψ.continuous.integrable_of_hasCompactSupport hsψ
  have hφπ : Integrable (fun γ : C(Time,X) => φ (γ 0)) π := by
    apply Integrable.comp_measurable _ (measurable_path_eval 0)
    rwa [he.1]
  have hψπ : Integrable (fun γ : C(Time,X) => ψ (γ 1)) π := by
    apply Integrable.comp_measurable _ (measurable_path_eval 1)
    rwa [he.2]
  have hcost : (wassersteinSq ν₀ ν₁).toReal=∫γ, dist (γ 0) (γ 1)^2 ∂π := by
    rw [wassersteinSq_eq_cost hp,transportCost_plan_eq_integral π hdi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [←he.1,←he.2,integral_map (measurable_path_eval 0).aemeasurable hφ.continuous.measurable.aestronglyMeasurable,
    integral_map (measurable_path_eval 1).aemeasurable hψ.continuous.measurable.aestronglyMeasurable,
    ←integral_add hφπ hψπ,integral_congr_ae hcontactπ,integral_div,he.1,he.2,hcost]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
