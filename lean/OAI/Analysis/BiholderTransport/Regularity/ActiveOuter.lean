import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.CostGeometry.OuterNonconjugacy
import OAI.Analysis.BiholderTransport.Regularity.ParametricActive

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ActiveOuter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.active_outer_nonconjugate (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {φ:ℝ → ℝ} (hφc:Continuous φ) (hmono:StrictMono φ)
    {z:TangentBundle 𝓘(ℝ,Model n) M}
    (ha:z.2∈activeLogs (φ ∘ uv.2) z.1)
    (hφ:ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)))
    {l:ℝ} (hd:HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2))) (hl:1 < l)
    (hconc:iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0) :
    Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2) := by
  let w:=reverseRay z
  let vu:=reverseNormalizedPair x0 uv
  let ψ:=fun s:ℝ=>φ (uv.2 x0+s)
  have hnorm (y:M):uv.2 x0+vu.1 y=uv.2 y := by
    change uv.2 x0+(uv.2 y+-uv.2 x0)=uv.2 y
    ring
  have hbase:uv.2 x0+vu.1 w.1=uv.2 (riemannianExp z.1 z.2) := by
    rw [hnorm,show w.1=riemannianExp z.1 z.2 from reverseRay_base z]
  have hψ:ContDiffAt ℝ 2 ψ (vu.1 w.1) := by
    exact (hbase.symm ▸ hφ).comp _ (contDiffAt_const.add contDiffAt_id)
  have hψD:HasDerivAt ψ l (vu.1 w.1) := by
    have hd':HasDerivAt φ l (uv.2 x0+vu.1 w.1) := hbase.symm ▸ hd
    have H:=hd'.comp (vu.1 w.1) ((hasDerivAt_id (vu.1 w.1)).const_add (uv.2 x0))
    simpa only [mul_one,Function.comp_def,ψ] using H
  have hψC:iteratedDeriv 2 ψ (vu.1 w.1) ≤ 0 := by
    dsimp only [ψ]
    rw [iteratedDeriv_comp_const_add]
    dsimp only
    rw [hbase]
    exact hconc
  have hψmono:StrictMono ψ := fun _ _ h=>hmono (by linarith)
  have hm:∀y:M,ψ (vu.1 w.1)+cost w.1 (riemannianExp w.1 w.2)-
      cost y (riemannianExp w.1 w.2) ≤ ψ (vu.1 y) := by
    intro y
    have H:=((activeLogs_iff_minimum (hφc.comp uv.2.continuous)).mp ha).2 y
    dsimp only [Function.comp_apply] at H
    dsimp only [ψ]
    rw [hnorm,hnorm,show riemannianExp w.1 w.2=z.1 from reverseRay_endpoint z,
      show w.1=riemannianExp z.1 z.2 from reverseRay_base z,cost_symm _ z.1,cost_symm y z.1]
    linarith only [H]
  have H:=hmtw.modified_outer_nonconjugate hlam hcap (densityDualClass_reverse hlam huv)
    (reverseRay_minimizing ha.1) hψmono hψ hψD hl hψC hm
  have H':=reverseRay_nonconjugate w H
  have hw:reverseRay w=z := reverseRay_involutive z
  rw [hw] at H'
  exact H'

end ActiveOuter
end WeakMTWTransport

end
end

end OAI
