import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.BranchJets
import OAI.Analysis.BiholderTransport.LinearAlgebra.PositiveBilinearBound

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section BranchDividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_branch_hessian_inward_limit {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    (ξ : TangentSpace 𝓘(ℝ,Model n) a) :
    Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
      (𝓝 (fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ)) := by
  have H := cost_branch_normal_jets (r := r) (T := (1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs => contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have HH := (H.2.2 ξ).div (tendsto_id.mono_left nhdsWithin_le_nhds) (by norm_num : (1:ℝ)≠0)
  change Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
    (𝓝 ((fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a ((1:ℝ) • r))))) 0 ξ ξ / 1)) at HH
  simpa only [one_smul,div_one] using HH

lemma exists_branch_divided_baseline {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t:ℝ} (ht : 0 < t) (ht1 : t < 1)
    {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ m>0,∀ ξ:TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-
        fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ := by
  let s0 := (t+1)/2
  have hts : t < s0 := by dsimp [s0]; linarith
  have hs0 : s0 < 1 := by dsimp [s0]; linarith
  obtain ⟨m,hm,Hm⟩ := exists_divided_hessian_baseline hr ht hts hs0
  refine ⟨m,hm,?_⟩
  intro ξ
  have H := ((tendsto_const_nhds (x := hessianValue a (t • r) ξ/t)).sub (cost_branch_hessian_inward_limit hr hG hagree ξ))
  apply ge_of_tendsto H
  filter_upwards [(eventually_gt_nhds hs0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs1
  exact Hm s hs.le hs1 ξ

end BranchDividedBaseline
end WeakMTWTransport

end

end

end

end OAI
