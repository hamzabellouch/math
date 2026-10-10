import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumDiagonal

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumActiveLimits
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

local instance activeLimitDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance activeLimitDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance activeLimitBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance activeLimitBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma MaximumDiagonal.active_weight_limits {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0))
    {r:Fin (Module.finrank ℝ (Model n)+1) → Model n}
    {m:Fin (Module.finrank ℝ (Model n)+1) → ℝ}
    (hr:Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r))
    (hm:Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m)) :
    Tendsto (fun k=>(J.first k).pj (S.ν k)) atTop (𝓝 r) ∧
    Tendsto (fun k=>(J.first k).w (S.ν k)) atTop (𝓝 m) := by
  exact ⟨diagonal_tendsto_of_close hr hε (Eventually.of_forall (fun k=>(S.activeClose k).le)),
    diagonal_tendsto_of_close hm hε (Eventually.of_forall (fun k=>(S.weightClose k).le))⟩

lemma MaximumDiagonal.sample_pole_limit {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {L:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hL:Tendsto (fun k=>(J.first k).L) atTop (𝓝 L)) :
    Tendsto (fun k=>J.sampleL k (S.ν k)) atTop (𝓝 L) := by
  apply diagonal_tendsto_of_close hL hε
  exact Eventually.of_forall (fun k=>by simpa only [dist_eq_norm] using (S.LClose k).le)

end MaximumActiveLimits
end WeakMTWTransport

end
end

end OAI
