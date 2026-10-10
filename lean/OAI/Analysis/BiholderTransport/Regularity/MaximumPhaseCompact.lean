import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterCompact
import OAI.Analysis.BiholderTransport.Duality.DualCompact

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumPhaseCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

local instance maximumPhaseDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma MaximumDiagonal.center_phase_compact {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C U:ℝ} (hC:0 ≤ C) (hU:0 ≤ U)
    (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d)
    (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
    ∃g:Model n →L[ℝ] ℝ,∃B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      ∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (fun i=>fderiv ℝ
        (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c)
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 g) ∧
      Tendsto (fun i=>fderiv ℝ
        (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c))
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 B) := by
  obtain ⟨B,σ,hσ,HB⟩:=S.center_compact hε hq he hQ hC hU hH hL
  obtain ⟨hb,hp,hx,hg⟩:=S.limits J hε hQ he
  have hz:=S.endpoint_tendsto he hb hp
  obtain ⟨K,hK,HK⟩:=S.center_gradient_bound hg hz
  obtain ⟨g,τ,hτ,HG⟩:=exists_dual_limit (hσ.tendsto_atTop.eventually HK)
  exact ⟨g,B,σ ∘ τ,hσ.comp hτ,HG,HB.comp hτ.tendsto_atTop⟩

end MaximumPhaseCompact
end WeakMTWTransport

end
end

end OAI
