import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.CostSmooth
import OAI.Analysis.BiholderTransport.Coordinates.ChartCostJets

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_half_cost_hessian (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm x),
      p∈minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm x) →
      ∀ z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
        ContDiffAt ℝ 2 (chartCost a (riemannianExp _ ((1/2:ℝ) • p))) z ∧
        ‖fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp _ ((1/2:ℝ) • p)))) z‖≤B := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let z₀ := χ a
  let Y : TangentBundle 𝓘(ℝ,Model n) M → M := fun V => riemannianExp V.1 ((1/2:ℝ) • V.2)
  have hY : Continuous Y := contMDiff_riemannianExp.continuous.comp
    (contMDiff_tangentScale.continuous.comp (continuous_const.prodMk continuous_id))
  have haT : z₀∈χ.target := χ.map_source (mem_extChartAt_source a)
  have hχ : ContinuousAt χ.symm z₀ :=
    (continuousOn_extChartAt_symm a z₀ haT).continuousAt ((isOpen_extChartAt_target a).mem_nhds haT)
  have hproj : Continuous (fun V : TangentBundle 𝓘(ℝ,Model n) M => V.1) :=
    FiberBundle.continuous_proj _ _
  have hg : ContinuousAt (fun q : Model n×Model n => χ.symm q.1) (z₀,z₀) :=
    hχ.comp (x := (z₀,z₀)) (f := fun q : Model n×Model n => q.1) continuousAt_fst
  have hloc : ∀ V : TangentBundle 𝓘(ℝ,Model n) M,
      V.2∈minimizingVectors V.1 → V.1=χ.symm z₀ →
      ContinuousAt (fun q : Model n×M => fderiv ℝ (fderiv ℝ (chartCost a q.2)) q.1) (z₀,Y V) ∧
      ∀ᶠ q : Model n×M in 𝓝 (z₀,Y V), ContDiffAt ℝ 2 (chartCost a q.2) q.1 := by
    intro V hV he
    apply chartCost_jet_continuous haT
    have hc := cost_contMDiffAt_of_injectivityDomain
      (⟨V.1,(1/2:ℝ) • V.2⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      (contracted_minimizer_mem_injectivityDomain hV (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1))
    change ContMDiffAt _ _ ∞ (fun q : M×M => cost q.1 q.2) (χ.symm z₀,Y V)
    rw [←he]
    exact hc
  let H := fun q : (Model n×Model n)×TangentBundle 𝓘(ℝ,Model n) M =>
    fderiv ℝ (fderiv ℝ (chartCost a (Y q.2))) q.1.2
  have hc : Continuous (fun q : (Model n×Model n)×TangentBundle 𝓘(ℝ,Model n) M =>
      (q.1.2,Y q.2)) := continuous_fst.snd.prodMk (hY.comp continuous_snd)
  obtain ⟨B,hB,hBnear⟩ := compact_eventually_fiberwise_bound isCompact_total_minimizingVectors
    hproj hg (h := H) (fun V hV he => by
      convert (hloc V hV he).1.comp
        (x := ((z₀,z₀),V)) (f := fun q : (Model n×Model n)×TangentBundle 𝓘(ℝ,Model n) M => (q.1.2,Y q.2)) hc.continuousAt using 1
      rfl)
  have hSnear : ∀ᶠ q : Model n×Model n in 𝓝 (z₀,z₀),
      ∀ V : TangentBundle 𝓘(ℝ,Model n) M, V.2∈minimizingVectors V.1 → V.1=χ.symm q.1 →
      ContDiffAt ℝ 2 (chartCost a (Y V)) q.2 := by
    apply compact_eventually_fiberwise isCompact_total_minimizingVectors hproj hg
    intro V hV he
    exact (hc.continuousAt (x := ((z₀,z₀),V))).tendsto.eventually (hloc V hV he).2
  obtain ⟨r₁,hr₁,hr⟩ := Metric.eventually_nhds_iff.mp (hSnear.and hBnear)
  obtain ⟨r₂,hr₂,hrT⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target a).mem_nhds haT)
  refine ⟨B,hB,min r₁ r₂,lt_min hr₁ hr₂,?_,?_⟩
  · exact fun x hx => hrT (ball_subset_ball (min_le_right _ _) hx)
  · intro x hx p hp z hz
    have hpair : dist (x,z) (z₀,z₀)<r₁ := by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨lt_of_lt_of_le hx (min_le_left _ _),lt_of_lt_of_le hz (min_le_left _ _)⟩
    exact ⟨(hr hpair).1 ⟨χ.symm x,p⟩ hp rfl,(hr hpair).2 ⟨χ.symm x,p⟩ hp rfl⟩

end WeakMTWTransport

end

end OAI
