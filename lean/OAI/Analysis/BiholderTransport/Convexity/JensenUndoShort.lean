import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.JensenPhase
import OAI.Analysis.BiholderTransport.Calculus.PhaseJet

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

lemma WeakMTW.jensen_undo_short (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℕ → ℝ → ℝ} (hφ:∀k,ContDiff ℝ ∞ (φ k))
    (hslope:∀k,∀y:M,0<deriv (φ k) (v y) ∧ deriv (φ k) (v y)<1)
    {a:M} {N:Set (Model n)} {t:ℕ → ℝ} (ht:∀k,0<t k) (ht1:∀k,t k<1)
    {w:ℕ → M → ℝ} {c:ℕ → M}
    (J:∀k,JensenSamplesAt (w k) (fun y=>φ k (v y)) (t k) a (c k) N)
    (i:ℕ → ℕ) (hti:Tendsto t atTop (𝓝 1))
    {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hz:Tendsto (fun k=>(J k).z (i k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hg:Tendsto (fun k=>fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a)
      ((J k).z (i k))) atTop (𝓝 g))
    (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a))
      ((J k).z (i k))) atTop (𝓝 H))
    (hexp:∀ᶠ k in atTop,∃p:Model n,∃A:Model n →L[ℝ] Model n,
      (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm
        (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h))) p A)
    (hsem:∀ᶠ k in atTop,∃r>0,∃K:ℝ,
      ConvexOn ℝ (Metric.ball (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))) r)
      (fun q=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
      (∀ᶠ k in atTop,(∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
        HasQuadraticExpansion (fun h=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm
          (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h)))) (p k) (A k)) ∧
      Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H) ∧
      Tendsto (fun k=>fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a ((J k).Y z))
        ((J k).z (i k))) atTop (𝓝 1) := by
  classical
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let P:=fun k (p:Model n) (A:Model n →L[ℝ] Model n)=>
    (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>φ k (v (χ.symm (χ ((J k).Y ((J k).z (i k)))+h)))) p A
  have hP:∀ᶠ k in atTop,∃p A,P k p A := by
    filter_upwards [hexp] with k hk
    obtain ⟨p,A,hs,hA⟩:=hk
    exact quadratic_expansion_scalar_exists hA ((hφ k).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top : (2:WithTop ℕ∞)≤∞))
  have hchoice:∀k,∃p A,(∃p A,P k p A) → P k p A := by
    intro k
    by_cases hk:∃p A,P k p A
    · obtain ⟨p,A,h⟩:=hk
      exact ⟨p,A,fun _=>h⟩
    · exact ⟨0,0,fun h=>False.elim (hk h)⟩
  choose p A hPA using hchoice
  have hPA':∀ᶠ k in atTop,P k (p k) (A k):=hP.mono (fun k hk=>hPA k hk)
  have hτ:Tendsto (fun k=>1-t k) atTop (𝓝 (0:ℝ)):=by
    simpa only [sub_self] using (tendsto_const_nhds.sub hti : Tendsto (fun k=>(1:ℝ)-t k) atTop (𝓝 (1-1)))
  have hq:Tendsto (fun k=>((J k).z (i k),fderiv ℝ
      (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a) ((J k).z (i k))))
      atTop (𝓝 (χ a,g)):=hz.prodMk_nhds hg
  have hflow:∀ᶠ k in atTop,DifferentiableAt ℝ
      (fun q:Phase n=>coordinatePhaseFlow a (1-t k,q))
      ((J k).z (i k),fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a) ((J k).z (i k))) := by
    have HH:=((coordinatePhaseFlow_contDiffAt (q := (χ a,g))
      (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)).of_le
        (by norm_num : (1:WithTop ℕ∞)≤∞)).eventually (by norm_num)
    filter_upwards [(hτ.prodMk_nhds hq).eventually HH] with k hk
    exact (hk.differentiableAt (by norm_num)).comp _
      ((contDiffAt_const.prodMk contDiffAt_id : ContDiffAt ℝ 1 (fun q:Phase n=>(1-t k,q)) _).differentiableAt (by norm_num))
  have hi:∀ᶠ k in atTop,(J k).z (i k)∈χ.target:=
    hz.eventually ((isOpen_extChartAt_target a).mem_nhds (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a))
  have hid:∀ᶠ k in atTop,
      (fderiv ℝ (fun q:Phase n=>coordinatePhaseFlow a (1-t k,q))
        ((J k).z (i k),fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a) ((J k).z (i k)))).comp
          ((ContinuousLinearMap.id ℝ (Model n)).prod
            (fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a)) ((J k).z (i k))))=
      (fderiv ℝ (fun z=>χ ((J k).Y z)) ((J k).z (i k))).prod
        (((innerSL ℝ).comp (A k)).comp (fderiv ℝ (fun z=>χ ((J k).Y z)) ((J k).z (i k)))) := by
    filter_upwards [hi,hPA',hsem,hflow] with k hik hk hs hf
    obtain ⟨r,hr,K,hK⟩:=hs
    exact hmtw.jensen_phase_graph_identity hu hv hdual (hφ k) (hslope k) (ht k) (ht1 k)
      (J k) (i k) hik hr hk.1 hk.2 hK hf
  have HH:=coordinate_phase_jet_limit (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a) hτ hq hH hid
  exact ⟨p,A,hPA',HH.2,HH.1⟩
end WeakMTWTransport

end

end OAI
