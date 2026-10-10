import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OriginalOuterLimit
import OAI.Analysis.BiholderTransport.Regularity.MaximumActiveLimits
import OAI.Analysis.BiholderTransport.Regularity.MaximumOuterSamples

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumTrueOuter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance maximumOuterFinite (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance maximumOuterComplete (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
local instance maximumOuterDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma WeakMTW.exists_maximum_true_outer
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
    uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀(α D bminus bplus:ℝ) (Bc Bo:ℝ → ℝ),∀ho:Continuous Bo,ContDiff ℝ ∞ Bo →
    (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
    ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
    ∀(a c:M) (N:Set (Model n)),
    ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
    ∀(ε:ℕ → ℝ),MaximumDiagonal J ε J.OuterSampleGood →
    Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β:ℝ),riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) →
    ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
      (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
      (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
    Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
    0 < m i → ∀l κ:ℝ,
    deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=l →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κ →
    1 < l → κ < 0 →
    (∀d,d≠0 → 0 < m i*L d d-(κ/l^2)*
        (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
      (∀d,m i*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2 ≤ V d d) ∧
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (l⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
          (expJacobian (n:=n) a (r i))^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_original_outer_limit hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv huv α D bminus bplus Bc Bo ho hBo hmono F a c N J ε S hε q β he hQ hβ
    r m L hr hm hL i hmin hmi l κ hd hdd hl hκ hp
  obtain ⟨hb,_,_,_⟩:=S.limits J hε hQ he
  obtain ⟨hri,hwi⟩:=S.active_weight_limits hε hr hm
  have hLi:=S.sample_pole_limit hε hL
  apply HK x0 uv (modifiedScalar α D Bo) huv (modifiedScalar_contDiff hBo α D)
    a (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
    (fun k=>(J.first k).pj (S.ν k) i) F.b (fun k=>(J.first k).w (S.ν k) i)
    (fun k=>J.sampleL k (S.ν k)) β (m i) l κ (r i) L hmin hb
    (tendsto_pi_nhds.mp hri i) hβ (tendsto_pi_nhds.mp hwi i) hLi hd hdd hl hκ hp
  filter_upwards [(tendsto_pi_nhds.mp hwi i).eventually (lt_mem_nhds hmi)] with k hk
  have hS:=S.extra k
  have htarget:(graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)∈
      (extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (S.poleSource k)
  exact ⟨htarget,hmono _ (Ioo_subset_Icc_self (F.parameter k)),hS.2.2.2.1 i,
    hS.2.2.1 i,hS.1,hS.2.1,hS.2.2.2.2 i hk⟩
end MaximumTrueOuter
end WeakMTWTransport

end
end

end OAI
