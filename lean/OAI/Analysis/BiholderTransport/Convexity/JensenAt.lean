import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.SimultaneousC11Jensen
import OAI.Analysis.BiholderTransport.LinearAlgebra.C11HessianLimits
import OAI.Analysis.BiholderTransport.Convexity.JensenPackage

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure JensenSamplesAt (v g : M → ℝ) (t : ℝ) (a c : M) (N : Set (Model n)) where
  z : ℕ → Model n
  Y : Model n → M
  Af : Model n →L[ℝ] Model n →L[ℝ] ℝ
  Ac : Model n →L[ℝ] Model n →L[ℝ] ℝ
  points : Tendsto z atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a c))
  outerHessians : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (chartOuterEnvelope v t a)) (z i)) atTop (𝓝 Af)
  centerHessians : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (chartCenterEnvelope g t a)) (z i)) atTop (𝓝 Ac)
  gradients : Tendsto (fun i=>fderiv ℝ (chartOuterEnvelope v t a) (z i)+
    fderiv ℝ (chartCenterEnvelope g t a) (z i)) atTop (𝓝 0)
  upper : ∀ d:Model n,Af d d+Ac d d≤0
  region : Set (Model n)
  openRegion : IsOpen region
  centerInRegion : extChartAt 𝓘(ℝ,Model n) a c∈region
  sampleInRegion : ∀ i,z i∈region
  outerDifferentiable : ∀ z∈region,DifferentiableAt ℝ (chartOuterEnvelope v t a) z
  centerDifferentiable : ∀ z∈region,DifferentiableAt ℝ (chartCenterEnvelope g t a) z
  outerGradientContinuous : ContinuousOn (fderiv ℝ (chartOuterEnvelope v t a)) region
  centerGradientContinuous : ContinuousOn (fderiv ℝ (chartCenterEnvelope g t a)) region
  selectorContinuous : ContinuousOn (fun z=>extChartAt 𝓘(ℝ,Model n) a (Y z)) region
  actual : ∀ z∈region,
    let χ := extChartAt 𝓘(ℝ,Model n) a
    let P : Model n → M := chartActualPole v t a
    let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
    Y z∈χ.source ∧ P z∈χP.source ∧
    (∀ y:M,chartCenterEnvelope g t a z=g y+cost y (χ.symm z)/(1-t) ↔ y=Y z) ∧
    chartOuterEnvelope v t a z=cTransform v (P z)+cost (P z) (χ.symm z)/t
  samples : ∀ i,
    let χ := extChartAt 𝓘(ℝ,Model n) a
    let P : Model n → M := chartActualPole v t a
    let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
    let F : Model n → ℝ := chartOuterEnvelope v t a
    let C := chartCenterEnvelope g t a
    Y (z i)∈χ.source ∧ P (z i)∈χP.source ∧
    (∀ y:M,C (z i)=g y+cost y (χ.symm (z i))/(1-t) ↔ y=Y (z i)) ∧
    F (z i)=cTransform v (P (z i))+cost (P (z i)) (χ.symm (z i))/t ∧
    HasFDerivAt (fun w=>χ (Y w)) (fderiv ℝ (fun w=>χ (Y w)) (z i)) (z i) ∧
    HasFDerivAt (fun w=>χP (P w)) (fderiv ℝ (fun w=>χP (P w)) (z i)) (z i) ∧
    ((fderiv ℝ (fun w=>χ (Y w)) (z i)).det≠0 → χ (Y (z i))∉N) ∧
    DifferentiableAt ℝ (fderiv ℝ F) (z i) ∧ DifferentiableAt ℝ (fderiv ℝ C) (z i) ∧
    HasSecondTaylor (fun h=>F (z i+h)) (fderiv ℝ F (z i)) (fderiv ℝ (fderiv ℝ F) (z i)) ∧
    HasSecondTaylor (fun h=>C (z i+h)) (fderiv ℝ C (z i)) (fderiv ℝ (fderiv ℝ C) (z i))

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma jensen_samples_at {v g : M → ℝ} {t : ℝ} {a c : M}
    {S : Set (Model n)} (hS : IsOpen S) (hz0 : extChartAt 𝓘(ℝ,Model n) a c∈S)
    {Y : Model n → M} {JF JG JY JP : ℝ≥0}
    (hF : ∀ z∈S,DifferentiableAt ℝ (chartOuterEnvelope v t a) z)
    (hG : ∀ z∈S,DifferentiableAt ℝ (chartCenterEnvelope g t a) z)
    (hFL : LipschitzOnWith JF (fderiv ℝ (chartOuterEnvelope v t a)) S)
    (hGL : LipschitzOnWith JG (fderiv ℝ (chartCenterEnvelope g t a)) S)
    (hYL : LipschitzOnWith JY (fun z=>extChartAt 𝓘(ℝ,Model n) a (Y z)) S)
    (hPL : LipschitzOnWith JP (fun z=>extChartAt 𝓘(ℝ,Model n)
      (chartActualPole v t a (extChartAt 𝓘(ℝ,Model n) a c)) (chartActualPole v t a z)) S)
    (hactual : ∀ z∈S,
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let P : Model n → M := chartActualPole v t a
      let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
      Y z∈χ.source ∧ P z∈χP.source ∧
      (∀ y:M,chartCenterEnvelope g t a z=g y+cost y (χ.symm z)/(1-t) ↔ y=Y z) ∧
      chartOuterEnvelope v t a z=cTransform v (P z)+cost (P z) (χ.symm z)/t)
    (hmax : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) a c),
      chartOuterEnvelope v t a z+chartCenterEnvelope g t a z≤
      chartOuterEnvelope v t a (extChartAt 𝓘(ℝ,Model n) a c)+
        chartCenterEnvelope g t a (extChartAt 𝓘(ℝ,Model n) a c))
    {N : Set (Model n)} (hN : volume N=0) : Nonempty (JensenSamplesAt (n := n) v g t a c N) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let F : Model n → ℝ := chartOuterEnvelope v t a
  let G : Model n → ℝ := chartCenterEnvelope g t a
  let P : Model n → M := chartActualPole v t a
  let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
  let R := fun z:Model n=>
    Y z∈χ.source ∧ P z∈χP.source ∧
    (∀ y:M,G z=g y+cost y (χ.symm z)/(1-t) ↔ y=Y z) ∧
    F z=cTransform v (P z)+cost (P z) (χ.symm z)/t ∧
    HasFDerivAt (fun q=>χ (Y q)) (fderiv ℝ (fun q=>χ (Y q)) z) z ∧
    HasFDerivAt (fun q=>χP (P q)) (fderiv ℝ (fun q=>χP (P q)) z) z ∧
    ((fderiv ℝ (fun q=>χ (Y q)) z).det≠0 → χ (Y z)∉N) ∧
    DifferentiableAt ℝ (fderiv ℝ F) z ∧ DifferentiableAt ℝ (fderiv ℝ G) z ∧
    HasSecondTaylor (fun h=>F (z+h)) (fderiv ℝ F z) (fderiv ℝ (fderiv ℝ F) z) ∧
    HasSecondTaylor (fun h=>G (z+h)) (fderiv ℝ G z) (fderiv ℝ (fderiv ℝ G) z)
  have hselect : ∀ rho eta:ℝ,0<rho → 0<eta → ∃ z∈S,
      dist z (χ c)<rho ∧ R z ∧ ‖fderiv ℝ F z+fderiv ℝ G z‖≤eta ∧
      ∀ e:Model n,fderiv ℝ (fderiv ℝ F) z e e+fderiv ℝ (fderiv ℝ G) z e e≤eta*‖e‖^2 := by
    intro rho eta hrho heta
    have haF := ae_secondTaylor_of_C11 volume hS hF hFL
    have haG := ae_secondTaylor_of_C11 volume hS hG hGL
    have hP : ∀ᵐ z ∂volume,z∈S → z∈S ∧ DifferentiableAt ℝ (fderiv ℝ F) z ∧
        DifferentiableAt ℝ (fderiv ℝ G) z := by
      filter_upwards [haF,haG] with z hf hg hz
      exact ⟨hz,(hf hz).1,(hg hz).1⟩
    obtain ⟨z,hz,hact,hy,hp,hn,hf,hg,hsmall,hupp⟩ := simultaneous_C11_jensen_near volume
      hS hz0 hF hG hFL hGL hYL hPL hmax hN hP hrho heta
    have hdata := hactual z hact.1
    exact ⟨z,hact.1,hz,⟨hdata.1,hdata.2.1,hdata.2.2.1,hdata.2.2.2,
      hy,hp,hn,hact.2.1,hact.2.2,hf,hg⟩,hsmall,hupp⟩
  obtain ⟨z,H,K,hz,hzlim,hH,hK,hgrad,hquad⟩ :=
    exists_C11_hessian_limit_samples hS hFL hGL hselect
  exact ⟨⟨z,Y,H,K,hzlim,hH,hK,hgrad,hquad,S,hS,hz0,fun i=>(hz i).1,
    hF,hG,hFL.continuousOn,hGL.continuousOn,hYL.continuousOn,hactual,fun i=>(hz i).2⟩⟩
end WeakMTWTransport

end

end OAI
