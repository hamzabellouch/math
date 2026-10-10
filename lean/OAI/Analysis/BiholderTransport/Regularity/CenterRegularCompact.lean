import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ActualCenterSemibound
import OAI.Analysis.BiholderTransport.Regularity.CenterSequenceCompact
import OAI.Analysis.BiholderTransport.Regularity.CenterSequenceRegular

namespace OAI

section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterSequenceRegular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma CenterSequenceData.regular_compact {a c:M} {u v:M → ℝ} {Φ:ℝ×ℝ → ℝ} {γ l:ℝ}
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
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a := by
  obtain ⟨σ,hσ,r,hr,hrr⟩:=center_support_family_subseq D.row hx
  exact (D.comp σ hσ.tendsto_atTop).regular hv hΦ hder hl hl1 hr hq he
    (hγ.comp hσ.tendsto_atTop) (hlm.comp hσ.tendsto_atTop)
    (hτ.comp hσ.tendsto_atTop) (ht.comp hσ.tendsto_atTop)
    (hx.comp hσ.tendsto_atTop) (hb.comp hσ.tendsto_atTop) hrr
    (hσ.tendsto_atTop.eventually hτpos) L (hσ.tendsto_atTop.eventually hLip)

end CenterSequenceRegular
end WeakMTWTransport

end
end

end OAI
