import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensenFamily
import OAI.Analysis.BiholderTransport.Regularity.ConfigurationCompact

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumActiveCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.active_subseq
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} {β:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    (i:ℕ → Fin (Module.finrank ℝ (Model n)+1)) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
      ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
      ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
      ∃i₀:Fin (Module.finrank ℝ (Model n)+1),
        Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
        Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
        (∀ᶠ k in atTop,i (σ k)=i₀) ∧
        (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈
          activeLogs (modifiedDatum v α D β Bo) a) ∧
        (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q := by
  obtain ⟨hbase,hvel,_,_⟩:=F.limit_coordinates hQ
  exact active_configuration_subseq hv ho hb hbase hvel
    (fun k=>(extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)) i
    (fun k j=>(J.first k).activeLimit j) (fun k j=>(J.first k).nonnegLimit j)
    (fun k=>(J.first k).totalLimit) (fun k=>(J.first k).baryLimit)

end MaximumActiveCompact
end WeakMTWTransport

end
end

end OAI
