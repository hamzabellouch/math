import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.LocalBranchJetBound

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section BranchJetSecond
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_branch_jet_bound_second (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {a:M}
    {r:TangentSpace 𝓘(ℝ,Model n) a} (hr:r∈minimizingVectors a)
    {G:M×M → ℝ}
    (hG:ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G (a,riemannianExp a r))
    (hagree:∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 → (fun q:M×M=>cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    {l:ℝ} (hl:1 < l) :
    let d:=extChartAt 𝓘(ℝ,Model n) a
    ∃ U:Set ((Model n×M)×ℝ),U∈𝓝 ((d a,riemannianExp a r),l) ∧ ∃ C≥0,
      ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (d.symm q.1.1)) →
      HasDerivAt φ q.2 (uv.2 (d.symm q.1.1)) →
      iteratedDeriv 2 φ (uv.2 (d.symm q.1.1)) ≤ 0 →
      ∀H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀w,0 ≤ H w w) →
      HasLowerSecondTaylor (fun w=>φ (uv.2 (d.symm (q.1.1+w)))+G (d.symm (q.1.1+w),q.1.2)) 0 H →
      ∀w,H w w ≤ C*‖w‖^2 := by
  dsimp only
  obtain ⟨U,hU,C,hC,HC⟩:=hmtw.exists_local_branch_jet_bound hlam hcap hr hG hagree hl
  refine ⟨U,hU,C,hC,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc H hH hjet w
  let vu:=reverseNormalizedPair x0 uv
  let ψ:=fun s:ℝ=>φ (uv.2 x0+s)
  have heq (y:M):uv.2 x0+vu.1 y=uv.2 y := by
    change uv.2 x0+(uv.2 y+-uv.2 x0)=uv.2 y
    ring
  have hψ:ContDiffAt ℝ 2 ψ (vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) :=
    ((heq _).symm ▸ hφ).comp _ (contDiffAt_const.add contDiffAt_id)
  have hdψ:HasDerivAt ψ q.2 (vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) := by
    have hd':HasDerivAt φ q.2 (uv.2 x0+vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) := (heq _).symm ▸ hd
    have HH:=hd'.comp _ ((hasDerivAt_id _).const_add (uv.2 x0))
    simpa only [mul_one,Function.comp_def,ψ] using HH
  have hcψ:iteratedDeriv 2 ψ (vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) ≤ 0 := by
    dsimp only [ψ]
    rw [iteratedDeriv_comp_const_add]
    dsimp only
    rw [heq]
    exact hconc
  apply HC q hq x0 vu (densityDualClass_reverse hlam huv) ψ
    (fun _ _ h=>hmono (by linarith)) hψ hdψ hcψ H hH _ w
  simpa only [ψ,heq] using hjet

end BranchJetSecond
end WeakMTWTransport

end
end

end OAI
