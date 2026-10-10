import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.JointMovingPrefix
import OAI.Analysis.BiholderTransport.Calculus.TrueCenterJetBuild
import OAI.Analysis.BiholderTransport.Regularity.TrueCenterLimit

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section OriginalCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance originalLimitFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance originalLimitDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance originalLimitDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance originalLimitBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance originalLimitBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_original_center_limit : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u:M → ℝ) (a c:M) (φ:ℕ → ℝ → ℝ) (lj:ℕ → ℝ) (yj:ℕ → M),
    ∀(pj:(j:ℕ) → TangentSpace 𝓘(ℝ,Model n) (yj j))
      (Aj:(j:ℕ) → TangentSpace 𝓘(ℝ,Model n) (yj j) →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (yj j))
      (sj:ℕ → Model n) (Sj:ℕ → Model n →L[ℝ] Model n),
    ∀(l κ χ:ℝ) (q r:Model n) (g:Model n →L[ℝ] ℝ) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    l∈U → 0<l → l<1 → 0<χ →
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a → riemannianExp a q=c →
    Tendsto lj atTop (𝓝 l) →
    Tendsto (fun j=>(⟨yj j,pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto (fun j=>reverseRay (⟨yj j,lj j • pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto (fun j=>iteratedDeriv 2 (φ j) (cTransform u (yj j))) atTop (𝓝 κ) →
    Tendsto (fun j=>innerSL ℝ (sj j)) atTop (𝓝 g) →
    Tendsto (fun j=>(innerSL ℝ).comp (Sj j)) atTop (𝓝 H) →
    (∀ᶠ j in atTop,NormalAlexandrovContact (n:=n) u (yj j) (pj j) (Aj j) ∧
      (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator (yj j) (pj j)+Aj j) d) d) ∧
      χ≤expJacobian (yj j) (pj j)*(normalHessianOperator (yj j) (pj j)+Aj j).det ∧
      ContDiffAt ℝ 2 (φ j) (cTransform u (yj j)) ∧
      deriv (φ j) (cTransform u (yj j))=lj j ∧
      (∀d e,inner ℝ (Sj j d) e=inner ℝ d (Sj j e)) ∧
      HasQuadraticExpansion (fun h=>φ j (cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
        (extChartAt 𝓘(ℝ,Model n) c (yj j)+h)))) (sj j) (Sj j)) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤
          chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g H d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  classical
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_true_center_limit (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro u a c φ lj yj pj Aj sj Sj l κ χ q r g H hlu hl hl1 hχ hq he hlj hfull hshort hκ hg hH hgood
  let z:=fun j=>reverseRay (⟨yj j,lj j • pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hy:Tendsto yj atTop (𝓝 c):=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).continuousAt.tendsto.comp hfull
  have hz:Tendsto (fun j=>(z j).1) atTop (𝓝 a):=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).continuousAt.tendsto.comp hshort
  have hccharts:=hy.eventually ((isOpen_extChartAt_source (I:=𝓘(ℝ,Model n)) c).mem_nhds (mem_extChartAt_source c))
  have hacharts:=hz.eventually ((isOpen_extChartAt_source (I:=𝓘(ℝ,Model n)) a).mem_nhds (mem_extChartAt_source a))
  have hpos:=hlj.eventually (Ioo_mem_nhds hl hl1)
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hgood.and (hpos.and (hccharts.and hacharts)))
  let σ:=fun j:ℕ=>j+N
  have hσ:Tendsto σ atTop atTop:=tendsto_add_atTop_nat N
  have hn (j:ℕ):N≤σ j:=Nat.le_add_left _ _
  let J (j:ℕ):TrueCenterJet (n:=n) u a c (φ (σ j)) (lj (σ j)):=
    trueCenterJetOfOriginal (hN _ (hn j)).1.1 (hN _ (hn j)).1.2.1
      (hN _ (hn j)).2.1.1 (hN _ (hn j)).2.1.2
      (hN _ (hn j)).2.2.1 (hN _ (hn j)).2.2.2
      (hN _ (hn j)).1.2.2.2.1 (hN _ (hn j)).1.2.2.2.2.1
      (hN _ (hn j)).1.2.2.2.2.2.1 (hN _ (hn j)).1.2.2.2.2.2.2
  obtain ⟨hb,hqq⟩:=graph_coordinates_tendsto hshort
  have hbj:Tendsto (fun j=>(J j).b) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)):=hb.comp hσ
  have hqj:Tendsto (fun j=>(J j).q) atTop (𝓝 q):=hqq.comp hσ
  have hc:movingPrefix a 1 (extChartAt 𝓘(ℝ,Model n) a a) q∈(extChartAt 𝓘(ℝ,Model n) c).source:=by
    rw [movingPrefix_at_center,one_smul,he]
    exact mem_extChartAt_source c
  have hmatrix:Tendsto (fun j=>(J j).matrix) atTop
      (𝓝 (chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g H)):=
    chartJetMatrix_tendsto (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a) hc hbj hqj (hg.comp hσ) (hH.comp hσ)
  exact Hδ u a c (φ ∘ σ) (lj ∘ σ) J l κ χ q r _ hlu hl hl1 hχ hq
    (hlj.comp hσ) hbj hqj (hfull.comp hσ) (hκ.comp hσ) hmatrix
    (Eventually.of_forall (fun j=>(hN _ (hn j)).1.2.2.1))
end OriginalCenterLimit
end WeakMTWTransport

end
end

end OAI
