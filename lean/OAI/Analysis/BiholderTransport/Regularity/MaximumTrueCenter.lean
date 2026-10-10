import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.CenterSequenceOriginalLimit
import OAI.Analysis.BiholderTransport.Regularity.MaximumEndpoint
import OAI.Analysis.BiholderTransport.Calculus.MaximumScalarJets
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterLimit
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterRegular

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumTrueCenter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance maximumTrueDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

omit [MeasurableSpace M] [BorelSpace M] in
lemma exists_maximum_true_center : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u v:M → ℝ),Continuous u → ∀Lv:ℝ≥0,∀hv:LipschitzWith Lv v,
    IsCostDualPair u v → ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
    ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc →
    (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    (∀y,v y∈Icc A₀ B₀) →
    (∀b∈Icc bminus bplus,∀y:M,0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1) →
    ∀K:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith K (modifiedDatum v α D b Bc)) →
    ∀hmtw:WeakMTW (n:=n) (M:=M),
    ∀F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo,
    ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0<χ → 0<r₀ →
    (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
      OriginalCenterGood (n:=n) u χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
    ∀J:MaximumJensenFamily hmtw hv.continuous ho F a c N,
    ∀(ε:ℕ → ℝ) (P:ℕ → ℕ → Prop) (S:MaximumDiagonal J ε P),
    Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β l:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
    l∈U → 0<l → l<1 →
    ∀(g:Model n →L[ℝ] ℝ) (H L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g) →
    Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∃r:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
          (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤L d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_center_sequence_original_limit (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro u v hu Lv hv hd α D bminus bplus A₀ B₀ Bc Bo ho hBc hmono hrange hslope K hLip
    hmtw F a c χ N r₀ hχ hr₀ hgood J ε P S hε q β l hq he hQ hβ hder hlu hl hl1 g H L hg hH hL
  obtain ⟨hb,hp,hx,hgrad⟩:=S.limits J hε hQ he
  have hz:=S.endpoint_tendsto he hb hp
  obtain ⟨sj,Sj,hsj,hsg,hSH⟩:=S.scalar_jets hu hv hd hBc hmono hrange hslope hr₀ hgood hx hz hg hH
  have hls (k:ℕ):0<J.sampleSlope k (S.ν k) ∧ J.sampleSlope k (S.ν k)<1:=
    hslope _ (Ioo_subset_Icc_self (F.parameter k)) _
  let CD:=S.center_sequence hu hv hd hBc hmono hls hgrad
  have hlj:=S.slope_tendsto hBc hβ hx
  rw [hder] at hlj
  have hτ:Tendsto (fun k=>1-F.t k) atTop (𝓝 (0:ℝ)):=by
    simpa only [sub_self] using (tendsto_const_nhds.sub F.time:
      Tendsto (fun k=>(1:ℝ)-F.t k) atTop (𝓝 (1-1)))
  have hgood':∀ᶠ k in atTop,OriginalCenterGood (n:=n) u χ
      ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k))) ∧
      deriv (fun s=>modifiedScalar α D Bc (F.b k,s))
        (v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k))))=J.sampleSlope k (S.ν k) ∧
      (∀d e,inner ℝ (Sj k d) e=inner ℝ d (Sj k e)) ∧
      HasQuadraticExpansion (fun h=>modifiedScalar α D Bc (F.b k,
        v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k)+h)))) (sj k) (Sj k):=by
    filter_upwards [hsj] with k hk
    have hY:(extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k))=
        (J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k))):=
      (extChartAt 𝓘(ℝ,Model n) c).left_inv ((J.sample k).samples (J.sampleIndex k (S.ν k))).1
    exact ⟨hY.symm ▸ hk.1,by rw [hY]; rfl,hk.2⟩
  obtain ⟨r,hr,hrev,V,hVs,hVp,hgain,hσ,hdet⟩:=Hδ a c u v (modifiedScalar α D Bc) β l χ
    hu hv.continuous hd (modifiedScalar_contDiff hBc α D) hder hlu hl hl1 hχ
    _ _ _ _ _ _ _ _ _ CD q hq he hβ hlj hτ F.time hx hb
    (Eventually.of_forall (fun k=>sub_pos.mpr (F.prefixTime k).2)) K
    (Eventually.of_forall (fun k=>hLip _ (Ioo_subset_Icc_self (F.parameter k))))
    sj Sj g H hsg hSH hgood'
  have hreg:=J.center_regular hu hv hd hBc hmono K hLip hq he hQ hβ hder hl hl1
  have hmat:=S.center_matrix_limit hε hreg he hQ hg hH
  refine ⟨r,hr,hrev,V,hVs,hVp,?_,hσ,hdet⟩
  intro d
  exact (hgain d).trans (S.center_matrix_le_pole_limit hε hmat hL d)
end MaximumTrueCenter
end WeakMTWTransport

end
end

end OAI
