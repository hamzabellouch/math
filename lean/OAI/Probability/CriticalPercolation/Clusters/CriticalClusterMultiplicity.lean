import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.SubcriticalLocalRateBound
import OAI.Probability.CriticalPercolation.Clusters.ClusterNumber

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurable_infinitelyManyInfiniteClusters [Countable V] [Countable E] :
    Measurable (fun ω => G.infinitelyManyInfiniteClusters ω) := by
  simp_rw [G.infinitelyManyInfiniteClusters_iff_no_finite_cover]
  exact .forall fun S => (G.measurable_infiniteClusterCover (S : Set V)).not

lemma infinitelyManyInfiniteClusters.exists_pairwise {ω : Set E}
    (h : G.infinitelyManyInfiniteClusters ω) (n : ℕ) :
    ∃ f : Fin n → V, (∀ i, (G.cluster ω (f i)).Infinite) ∧
      Pairwise (fun i j => ¬ (G.openGraph ω).Reachable (f i) (f j)) := by
  induction n with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨f,hf,hpair⟩ := ih
    obtain ⟨v,hv,hnew⟩ := h (Finset.univ.image f)
    refine ⟨Fin.cons v f,?_,?_⟩
    · intro i
      refine Fin.cases hv (fun j => ?_) i
      exact hf j
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun a => ?_) i
      · refine Fin.cases ?_ (fun b hij => ?_) j
        · exact fun hij => False.elim (hij rfl)
        · exact hnew (f b) (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)
      · refine Fin.cases ?_ (fun b hij => ?_) j
        · exact fun _ hab => hnew (f a) (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) hab.symm
        · exact hpair (fun he => hij (congrArg Fin.succ he))

theorem exponential_critical_infinitelyMany_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
    (hper : G.law G.criticalProbability G.percolates ≠ 0) :
    ∀ᵐ ω ∂G.law G.criticalProbability, G.infinitelyManyInfiniteClusters ω := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hp : (0 : ℝ) < G.criticalProbability := by
    have hpc : 0 < G.criticalProbability := by
      by_contra h
      have he : G.criticalProbability = 0 := le_antisymm (not_lt.mp h) bot_le
      exact hper (he ▸ G.law_zero_percolates)
    exact hpc
  rcases G.unique_or_infinitely_many_ae hc hl hq G.criticalProbability hp with hu | hm
  · exact False.elim (hper (Sharpness.critical_null_of_unique G hc hl hq o γ hγ N hgrowth hu))
  · exact hm

end CriticalPercolation.BondGraph
end
end

end OAI
