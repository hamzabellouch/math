import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ActualCenterSemibound
import OAI.Analysis.BiholderTransport.Convexity.JensenPackage

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section SampleCenterFamilies
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.coordinateBackward_graph_pole (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : subgradientGraph (n := n) (cTransform v)) {c : M}
    (hz : graphProjection (cTransform v) t q∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    coordinateBackward c (t,extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform v) t q),
      fderiv ℝ (chartOuterEnvelope v t c)
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform v) t q)))=q.1.1 := by
  have HH := hmtw.coordinateBackward_eq_pole (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) ⟨(cTransform_triple hv).symm,rfl⟩ ht ht1
      ((extChartAt 𝓘(ℝ,Model n) c).map_source hz)
  rw [(extChartAt 𝓘(ℝ,Model n) c).left_inv hz] at HH
  have HP := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  exact HH.trans HP

def WeakMTW.center_sequence_of_graph (hmtw : WeakMTW (n := n) (M := M))
    {a c : M} {u v : M → ℝ} {Φ : ℝ×ℝ → ℝ}
    {γj lj τj tj : ℕ → ℝ} {xj : ℕ → Model n} {wj : ℕ → M → ℝ}
    (hw : ∀ i,Continuous (wj i)) (ht : ∀ i,0<tj i) (ht1 : ∀ i,tj i<1)
    (q : ∀ i,subgradientGraph (n := n) (cTransform (wj i)))
    (ha : ∀ i,(q i).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hc : ∀ i,graphProjection (cTransform (wj i)) (tj i) (q i)∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (R : ∀ i,TrueCenterRow c u v (fun s=>Φ (γj i,s)) (xj i)
      (graphProjection (cTransform (wj i)) (tj i) (q i)) (τj i) (lj i))
    (hd : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i))),
        DifferentiableAt ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y))
          ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y))
        ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i))))
    (hg : Tendsto (fun i=>fderiv ℝ (chartOuterEnvelope (wj i) (tj i) c)
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i)))+
      fderiv ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y))
        ((extChartAt 𝓘(ℝ,Model n) c).symm z))
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i)))) atTop (𝓝 0)) :
    CenterSequenceData a c u v Φ γj lj τj tj xj
      (fun i=>graphBaseCoordinate a (q i).1) (fun i=>graphVelocityCoordinate a (q i).1)
      (fun i=>graphProjection (cTransform (wj i)) (tj i) (q i))
      (fun i=>chartOuterEnvelope (wj i) (tj i) c) where
  row := R
  endpoint i := movingPrefix_graph_coordinates (ha i) (tj i)
  derivative := hd
  gradient := hg
  backward := Eventually.of_forall (fun i=>by
    rw [hmtw.coordinateBackward_graph_pole (hw i) (ht i) (ht1 i) (q i) (hc i)]
    exact ((extChartAt 𝓘(ℝ,Model n) a).left_inv (ha i)).symm)

end SampleCenterFamilies
end WeakMTWTransport

end
end

end OAI
