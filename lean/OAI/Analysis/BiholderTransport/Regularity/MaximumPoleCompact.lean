import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearCompact
import OAI.Analysis.BiholderTransport.Convexity.MaximumJensenFamily

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumPoleCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

local instance poleCompactDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma MaximumJensenFamily.pole_compact (J:MaximumJensenFamily hmtw hv ho F a c N)
    {U:ℝ} (hU:0 ≤ U) (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
    ∃L:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (fun k=>(J.first (σ k)).L) atTop (𝓝 L) := by
  apply exists_bilinear_limit (Bj:=fun k=>(J.first k).L) (C:=U)
  filter_upwards [hL] with k hk
  apply symmetric_bilinear_norm_bound (J.first k).symmetric hU
  intro d
  rw [abs_of_nonneg ((J.first k).positive d)]
  exact hk d

lemma MaximumJensenFamily.pole_limit_properties (J:MaximumJensenFamily hmtw hv ho F a c N)
    {L:Model n →L[ℝ] Model n →L[ℝ] ℝ} {q:Model n}
    {r:Fin (Module.finrank ℝ (Model n)+1) → Model n}
    (hL:Tendsto (fun k=>(J.first k).L) atTop (𝓝 L))
    (hp:Tendsto (fun k=>graphVelocityCoordinate a (F.row k).q.1) atTop (𝓝 q))
    (hr:Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r)) :
    (∀d,0 ≤ L d d) ∧ (∀d e,L d e=L e d) ∧ (∀i d,L (r i-q) d=0) := by
  refine ⟨bilinear_limit_nonneg hL (Eventually.of_forall (fun k=>(J.first k).positive)),
    bilinear_limit_symm hL (Eventually.of_forall (fun k=>(J.first k).symmetric)),?_⟩
  intro i d
  exact bilinear_limit_kernel hL ((tendsto_pi_nhds.mp hr i).sub hp)
    (Eventually.of_forall (fun k=>(J.first k).kernel i)) d
end MaximumPoleCompact
end WeakMTWTransport

end
end

end OAI
