import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OriginalCenterLimit
import OAI.Analysis.BiholderTransport.Volume.DensityOriginalJets
import OAI.Analysis.BiholderTransport.Regularity.CenterTrueRayCompact
import OAI.Analysis.BiholderTransport.Regularity.CenterRegularCompact
import OAI.Analysis.BiholderTransport.Calculus.ScalarSecond

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterSequenceOriginalLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance sequenceOrigDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance sequenceOrigDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance sequenceOrigBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance sequenceOrigBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

omit [MeasurableSpace M] [BorelSpace M] in
lemma exists_center_sequence_original_limit : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(a c:M) (u v:M → ℝ) (Φ:ℝ×ℝ → ℝ) (γ l χ:ℝ),
    Continuous u → Continuous v → IsCostDualPair u v → ContDiff ℝ ∞ Φ →
    deriv (fun s=>Φ (γ,s)) (v c)=l → l∈U → 0<l → l<1 → 0<χ →
    ∀(γj lj τj tj:ℕ → ℝ) (xj bj qj:ℕ → Model n) (zj:ℕ → M) (F:ℕ → Model n → ℝ),
    CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F →
    ∀q:Model n,
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
    Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
    Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
    Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
    (∀ᶠ j in atTop,0<τj j) → ∀L:ℝ≥0,
    (∀ᶠ j in atTop,LipschitzWith L (fun y=>Φ (γj j,v y))) →
    ∀(sj:ℕ → Model n) (Sj:ℕ → Model n →L[ℝ] Model n)
      (g:Model n →L[ℝ] ℝ) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun j=>innerSL ℝ (sj j)) atTop (𝓝 g) →
    Tendsto (fun j=>(innerSL ℝ).comp (Sj j)) atTop (𝓝 H) →
    (∀ᶠ j in atTop,OriginalCenterGood (n:=n) u χ ((extChartAt 𝓘(ℝ,Model n) c).symm (xj j)) ∧
      deriv (fun s=>Φ (γj j,s)) (v ((extChartAt 𝓘(ℝ,Model n) c).symm (xj j)))=lj j ∧
      (∀d e,inner ℝ (Sj j d) e=inner ℝ d (Sj j e)) ∧
      HasQuadraticExpansion (fun h=>Φ (γj j,v ((extChartAt 𝓘(ℝ,Model n) c).symm (xj j+h)))) (sj j) (Sj j)) →
    ∃r:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
          (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤
            chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g H d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  classical
  let : T2Space (TangentBundle 𝓘(ℝ,Model n) M) := bundle_totalSpace_t2
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_original_center_limit (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro a c u v Φ γ l χ hu hv hd hΦ hder hlu hl hl1 hχ γj lj τj tj xj bj qj zj F D q hq he
    hγ hlm hτ ht hx hb hτpos L hLip sj Sj g H hg hH hgood
  let yj:=fun j=>(extChartAt 𝓘(ℝ,Model n) c).symm (xj j)
  let pj (j:ℕ):TangentSpace 𝓘(ℝ,Model n) (yj j):=
    if h:OriginalCenterGood (n:=n) u χ (yj j) then Classical.choose h else 0
  let Aj (j:ℕ):TangentSpace 𝓘(ℝ,Model n) (yj j) →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (yj j):=
    if h:OriginalCenterGood (n:=n) u χ (yj j) then Classical.choose (Classical.choose_spec h) else 0
  have hPA:∀ᶠ j in atTop,NormalAlexandrovContact (n:=n) u (yj j) (pj j) (Aj j) ∧
      (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator (yj j) (pj j)+Aj j) d) d) ∧
      χ≤expJacobian (yj j) (pj j)*(normalHessianOperator (yj j) (pj j)+Aj j).det:=by
    filter_upwards [hgood] with j hj
    have hj0 : OriginalCenterGood (n:=n) u χ (yj j) := hj.1
    simpa only [pj,Aj,dite_eq_left hj0] using Classical.choose_spec (Classical.choose_spec hj0)
  have hray:∀ᶠ j in atTop,(⟨yj j,pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)=chartRay c (xj j) (D.row j).r:=by
    filter_upwards [hPA] with j hj
    exact congrArg (fun p:TangentSpace 𝓘(ℝ,Model n) (yj j)=>
      (⟨yj j,p⟩:TangentBundle 𝓘(ℝ,Model n) M))
      ((hj.1.active_eq hu ((D.row j).active hd)).symm)
  obtain ⟨σ,hσ,r,hr,hrr,hshort⟩:=D.true_ray_compact hv (hΦ.contDiffAt) hder hl hl1 hq he
    hγ hlm hτ ht hx hb hτpos L hLip
  have hreg:=D.regular_compact hv hΦ.contDiffAt hder hl hl1 hq he hγ hlm hτ ht hx hb hτpos L hLip
  have hfull:Tendsto (fun j=>(⟨yj (σ j),pj (σ j)⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)):=
    (chartRay_tendsto (hx.comp hσ.tendsto_atTop) hrr).congr'
      (Filter.EventuallyEq.symm (hσ.tendsto_atTop.eventually hray))
  have hshort':Tendsto (fun j=>reverseRay (⟨yj (σ j),lj (σ j) • pj (σ j)⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)):=by
    apply hshort.congr'
    filter_upwards [hσ.tendsto_atTop.eventually hray] with j hj
    exact congrArg (fun w:TangentBundle 𝓘(ℝ,Model n) M=>reverseRay (tangentScale (lj (σ j)) w)) hj.symm
  have hrev:reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩:=
    tendsto_nhds_unique (modified_reverseRay_tendsto (hx.comp hσ.tendsto_atTop) hrr
      (hlm.comp hσ.tendsto_atTop)) hshort
  have hy:Tendsto yj atTop (𝓝 c):=by
    have HH:=(continuousAt_extChartAt_symm'' (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) c)).tendsto.comp hx
    rwa [(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)] at HH
  have hvy:Tendsto (fun j=>v (yj j)) atTop (𝓝 (v c)):=hv.continuousAt.tendsto.comp hy
  have hκ:=((continuous_scalar_family_second hΦ).tendsto (γ,v c)).comp (hγ.prodMk_nhds hvy)
  have hgood':∀ᶠ j in atTop,NormalAlexandrovContact (n:=n) u (yj j) (pj j) (Aj j) ∧
      (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator (yj j) (pj j)+Aj j) d) d) ∧
      χ≤expJacobian (yj j) (pj j)*(normalHessianOperator (yj j) (pj j)+Aj j).det ∧
      ContDiffAt ℝ 2 (fun s=>Φ (γj j,s)) (cTransform u (yj j)) ∧
      deriv (fun s=>Φ (γj j,s)) (cTransform u (yj j))=lj j ∧
      (∀d e,inner ℝ (Sj j d) e=inner ℝ d (Sj j e)) ∧
      HasQuadraticExpansion (fun h=>Φ (γj j,cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
        (extChartAt 𝓘(ℝ,Model n) c (yj j)+h)))) (sj j) (Sj j):=by
    filter_upwards [hgood,hPA] with j hj hP
    refine ⟨hP.1,hP.2.1,hP.2.2,?_,?_,hj.2.2.1,?_⟩
    · exact ((hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
    · rw [←hd.2]
      exact hj.2.1
    · rw [←hd.2]
      dsimp only [yj]
      rw [(extChartAt 𝓘(ℝ,Model n) c).right_inv (D.row j).chart]
      exact hj.2.2.2
  refine ⟨r,hr,hrev,?_⟩
  apply Hδ u a c (fun j s=>Φ (γj (σ j),s)) (lj ∘ σ) (yj ∘ σ)
    (fun j=>pj (σ j)) (fun j=>Aj (σ j)) (sj ∘ σ) (Sj ∘ σ)
    l _ χ q r g H hlu hl hl1 hχ hreg he (hlm.comp hσ.tendsto_atTop) hfull hshort'
  · rw [←hd.2]
    exact hκ.comp hσ.tendsto_atTop
  · exact hg.comp hσ.tendsto_atTop
  · exact hH.comp hσ.tendsto_atTop
  · exact hσ.tendsto_atTop.eventually hgood'
end CenterSequenceOriginalLimit
end WeakMTWTransport

end
end

end OAI
