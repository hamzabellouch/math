import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ActiveGraphLimit
import OAI.Analysis.BiholderTransport.Coordinates.ChartActiveLimit

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inverse_mem_minimizingChartParameters {a : M} {K : Set M} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hK : (extChartAt 𝓘(ℝ,Model n) a).symm b∈K)
    (hp : chartFiberInverse a b p∈minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    (b,p)∈minimizingChartParameters (n := n) a K := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  refine ⟨χ.symm (b,p),?_,χ.right_inv ((tangent_chart_target_iff _ _).mpr hb)⟩
  rw [tangent_chart_symm_trivialization hb]
  exact ⟨hp,hK⟩

omit [Nonempty M] in
lemma minimizing_coordinates_tail_subseq {a : M} {bj pj : ℕ → Model n}
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hbt : ∀ i,bj i∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hpm : ∀ i,chartFiberInverse a (bj i) (pj i)∈
      minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm (bj i))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ p : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) a from p)∈minimizingVectors a ∧
      Tendsto (pj ∘ σ) atTop (𝓝 p) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have ha := χ.map_source (mem_extChartAt_source a)
  have hy : Tendsto (fun i=>χ.symm (bj i)) atTop (𝓝 a) := by
    have H := (continuousAt_extChartAt_symm'' ha).tendsto.comp hb
    rwa [χ.left_inv (mem_extChartAt_source a)] at H
  obtain ⟨K,hK,hKs,N,hN⟩ := compact_in_chart_tail (n := n) (a := a) hy (mem_extChartAt_source a)
  have hshift : Tendsto (fun k:ℕ=>k+N) atTop atTop := tendsto_add_atTop_nat N
  have hin (k : ℕ) : (bj (k+N),pj (k+N))∈minimizingChartParameters (n := n) a K :=
    inverse_mem_minimizingChartParameters (hbt _) (hN k) (hpm _)
  obtain ⟨q,hq,σ,hσ,hlim⟩ :=
    (isCompact_minimizingChartParameters hK hKs).isSeqCompact hin
  have hbase : q.1=χ a := tendsto_nhds_unique hlim.fst_nhds ((hb.comp hshift).comp hσ.tendsto_atTop)
  have hmin := (mem_minimizingChartParameters hKs hq).2.2
  change chartFiberInverse a q.1 q.2∈minimizingVectors (χ.symm q.1) at hmin
  rw [hbase,chartFiberInverse_at_center,χ.left_inv (mem_extChartAt_source a)] at hmin
  exact ⟨fun k=>σ k+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,q.2,hmin,hlim.snd_nhds⟩

end WeakMTWTransport

end

end OAI
