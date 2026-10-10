import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ActualCenterSemibound
import OAI.Analysis.BiholderTransport.Regularity.CenterRayLimit
import OAI.Analysis.BiholderTransport.Regularity.CenterSequenceCompact
import OAI.Analysis.BiholderTransport.Regularity.CenterPoleStationary
import OAI.Analysis.BiholderTransport.Calculus.TrueCenterGradient

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterTrueRayCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma CenterSequenceData.true_ray_compact {a c:M} {u v:M → ℝ} {Φ:ℝ×ℝ → ℝ} {γ l:ℝ}
    (hv:Continuous v) (hΦ:ContDiffAt ℝ ∞ Φ (γ,v c))
    (hder:deriv (fun s=>Φ (γ,s)) (v c)=l) (hl:0 < l) (hl1:l < 1)
    {γj lj τj tj:ℕ → ℝ} {xj bj qj:ℕ → Model n} {zj:ℕ → M}
    {F:ℕ → Model n → ℝ}
    (D:CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
    {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a)
    (he:riemannianExp a q=c)
    (hγ:Tendsto γj atTop (𝓝 γ)) (hlm:Tendsto lj atTop (𝓝 l))
    (hτ:Tendsto τj atTop (𝓝 0)) (ht:Tendsto tj atTop (𝓝 1))
    (hx:Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hτpos:∀ᶠ i in atTop,0 < τj i) (L:ℝ≥0)
    (hLip:∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧ ∃r:Model n,
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      Tendsto (fun i=>(D.row (σ i)).r) atTop (𝓝 r) ∧
      Tendsto (fun i=>reverseRay (tangentScale (lj (σ i))
        (chartRay c (xj (σ i)) (D.row (σ i)).r))) atTop
        (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  obtain ⟨σ,hσ,r,hr,hrr⟩:=center_support_family_subseq D.row hx
  have HP: a=riemannianExp c (l • r):=
    (D.comp σ hσ.tendsto_atTop).pole hv hΦ hder hl hl1 hr
      (hγ.comp hσ.tendsto_atTop) (hlm.comp hσ.tendsto_atTop)
      (hτ.comp hσ.tendsto_atTop) (ht.comp hσ.tendsto_atTop)
      (hx.comp hσ.tendsto_atTop) (hb.comp hσ.tendsto_atTop) hrr
      (hσ.tendsto_atTop.eventually hτpos) L (hσ.tendsto_atTop.eventually hLip)
  have HE:=reverse_minimizer_eq (contracted_minimizer_mem_injectivityDomain hr hl hl1)
    hq HP.symm he
  refine ⟨σ,hσ,r,hr,hrr,?_⟩
  have HT:=modified_reverseRay_tendsto (hx.comp hσ.tendsto_atTop) hrr
    (hlm.comp hσ.tendsto_atTop)
  have HE' : reverseRay (⟨c,l • r⟩ : TangentBundle 𝓘(ℝ,Model n) M) =
      (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M) := by exact HE
  rw [HE'] at HT
  exact HT

end CenterTrueRayCompact
end WeakMTWTransport

end
end

end OAI
