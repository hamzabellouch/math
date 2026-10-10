import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition
import OAI.Analysis.BiholderTransport.Regularity.ActualCenterRay
import OAI.Analysis.BiholderTransport.Contact.PhaseContact

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mdifferentiable_of_fixed_chart {a z:M} {f:M → ℝ}
    (hz:z∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:DifferentiableAt ℝ (fun q=>f ((extChartAt 𝓘(ℝ,Model n) a).symm q))
      (extChartAt 𝓘(ℝ,Model n) a z)) :
    MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z := by
  have H:=hd.hasFDerivAt.hasMFDerivAt.comp z
    (mdifferentiableAt_extChartAt (I:=𝓘(ℝ,Model n))
      (show z∈(chartAt (Model n) a).source from by simpa only [extChartAt_source] using hz)).hasMFDerivAt
  apply (H.congr_of_eventuallyEq ?_).mdifferentiableAt
  filter_upwards [(isOpen_extChartAt_source a).mem_nhds hz] with y hy
  simp only [Function.comp_apply,(extChartAt 𝓘(ℝ,Model n) a).left_inv hy]

lemma WeakMTW.modified_phase_subgradient (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℝ → ℝ} (hφc:Continuous φ)
    {a y z:M} {l τ:ℝ} (hφ:HasDerivAt φ l (v y))
    (hl:0<l) (hl1:l<1) (hτ:0<τ) (hτ1:τ<1)
    (hval:hopfLax τ (fun w=>φ (v w)) z=φ (v y)+cost y z/τ)
    (hy:y∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hz:z∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:DifferentiableAt ℝ (fun q=>hopfLax τ (fun w=>φ (v w))
      ((extChartAt 𝓘(ℝ,Model n) a).symm q)) (extChartAt 𝓘(ℝ,Model n) a z))
    {s:Set (Model n)} {K:ℝ} (hys:extChartAt 𝓘(ℝ,Model n) a y∈s)
    (hsem:ConvexOn ℝ s (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    let Q:=coordinatePhaseFlow a (τ,extChartAt 𝓘(ℝ,Model n) a z,
      fderiv ℝ (fun q=>hopfLax τ (fun w=>φ (v w)) ((extChartAt 𝓘(ℝ,Model n) a).symm q))
        (extChartAt 𝓘(ℝ,Model n) a z))
    Q.1=extChartAt 𝓘(ℝ,Model n) a y ∧
      IsSemiconvexSubgradientOn (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))) s K
        (extChartAt 𝓘(ℝ,Model n) a y) ((InnerProductSpace.toDual ℝ (Model n)).symm Q.2) := by
  obtain ⟨p,_,he,_,_,hp⟩:=hmtw.exists_center_ray_of_minimizer hu hv hdual hφc hφ hl hl1 hτ hτ1 hval
  have he':(sprayFlow τ (⟨y,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=z := by
    rwa [riemannianExp_smul] at he
  have HH:=phase_contact_semiconvex (hφc.comp hv.continuous)
    (injectivityDomain_subset_minimizingVectors y hp) hτ hτ1
    (he'.symm ▸ hval) hy (he'.symm ▸ hz)
    (he'.symm ▸ mdifferentiable_of_fixed_chart hz hd) hys hsem
  rw [he'] at HH
  dsimp only at HH ⊢
  exact ⟨HH.1,HH.1 ▸ HH.2⟩

end WeakMTWTransport

end

end OAI
