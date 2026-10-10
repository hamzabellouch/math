import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingCoordinateLimit
import OAI.Analysis.BiholderTransport.Regularity.ParametricActive

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ConfigurationCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma active_configuration_subseq {ι : Type*} [Fintype ι] [Nonempty ι]
    [TopologicalSpace ι] [DiscreteTopology ι]
    {a:M} {v:M → ℝ} (hv:Continuous v) {α D:ℝ} {B:ℝ → ℝ} (hB:Continuous B)
    {β:ℕ → ℝ} {β₀:ℝ} (hβ:Tendsto β atTop (𝓝 β₀))
    {bj p:ℕ → Model n} {p₀:Model n}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto p atTop (𝓝 p₀))
    (hbt:∀k,bj k∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {pj:ℕ → ι → Model n} {w:ℕ → ι → ℝ} (i:ℕ → ι)
    (ha:∀k j,chartFiberInverse a (bj k) (pj k j)∈
      activeLogs (modifiedDatum v α D (β k) B) ((extChartAt 𝓘(ℝ,Model n) a).symm (bj k)))
    (hw:∀k j,0 ≤ w k j) (hs:∀k,∑j,w k j=1)
    (hbar:∀k,∑j,w k j • pj k j=p k) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧ ∃r:ι → Model n,∃m:ι → ℝ,∃i₀:ι,
      Tendsto (pj ∘ σ) atTop (𝓝 r) ∧ Tendsto (w ∘ σ) atTop (𝓝 m) ∧
      (∀ᶠ k in atTop,i (σ k)=i₀) ∧
      (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈activeLogs (modifiedDatum v α D β₀ B) a) ∧
      (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=p₀ := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  have hat:χ a∈χ.target := mem_extChartAt_target a
  have hy:Tendsto (fun k=>χ.symm (bj k)) atTop (𝓝 a) := by
    have H:=(continuousAt_extChartAt_symm'' hat).tendsto.comp hb
    rwa [χ.left_inv (mem_extChartAt_source a)] at H
  obtain ⟨K,hK,hKs,N,hN⟩:=compact_in_chart_tail (n := n) (a := a) hy (mem_extChartAt_source a)
  let shift:=fun k:ℕ=>k+N
  have hshift:Tendsto shift atTop atTop := tendsto_add_atTop_nat N
  let C:=minimizingChartParameters (n := n) a K
  have hC:IsCompact C := isCompact_minimizingChartParameters hK hKs
  let S:= {q:EnvelopeData (Model n) ι | (∀j,(q.1.1,q.1.2 j)∈C) ∧
    (∀j,0 ≤ q.2.1 j) ∧ ∑j,q.2.1 j=1 ∧ q.2.2∈Icc 0 0}
  have hc:IsCompact (S×ˢ(univ:Set ι)) := (compact_common_base_configurations hC 0).prod isCompact_univ
  let f:ℕ → EnvelopeData (Model n) ι × ι := fun k=>(((bj (shift k),pj (shift k)),(w (shift k),0)),i (shift k))
  have hf:∀k,f k∈S×ˢ(univ:Set ι) := by
    intro k
    refine ⟨⟨?_,hw _,hs _,le_rfl,le_rfl⟩,mem_univ _⟩
    intro j
    exact inverse_mem_minimizingChartParameters (hbt _) (hN k) (ha _ j).1
  obtain ⟨q,hq,τ,hτ,hlim⟩:=hc.isSeqCompact hf
  let σ:=shift ∘ τ
  have hσ:StrictMono σ := fun k l h=>Nat.add_lt_add_right (hτ h) N
  have hr:Tendsto (pj ∘ σ) atTop (𝓝 q.1.1.2) := hlim.fst_nhds.fst_nhds.snd_nhds
  have hm:Tendsto (w ∘ σ) atTop (𝓝 q.1.2.1) := hlim.fst_nhds.snd_nhds.fst_nhds
  have hi:∀ᶠ k in atTop,i (σ k)=q.2 := by
    exact hlim.snd_nhds.eventually ((isOpen_discrete {q.2}).mem_nhds rfl)
  refine ⟨σ,hσ,q.1.1.2,q.1.2.1,q.2,hr,hm,hi,?_,hq.1.2.1,hq.1.2.2.1,?_⟩
  · intro j
    apply modified_active_coordinates_limit hv hB (hβ.comp hσ.tendsto_atTop)
      (hb.comp hσ.tendsto_atTop) ((tendsto_pi_nhds.mp hr) j)
      (Eventually.of_forall (fun k=>hbt (σ k)))
      (Eventually.of_forall (fun k=>ha (σ k) j))
  · have H:Tendsto (fun k=>∑j,w (σ k) j • pj (σ k) j) atTop
        (𝓝 (∑j,q.1.2.1 j • q.1.1.2 j)) := by
      apply tendsto_finsetSum
      intro j _
      exact ((tendsto_pi_nhds.mp hm) j).smul ((tendsto_pi_nhds.mp hr) j)
    simp only [hbar] at H
    exact tendsto_nhds_unique H (hp.comp hσ.tendsto_atTop)
end ConfigurationCompact
end WeakMTWTransport

end
end

end OAI
