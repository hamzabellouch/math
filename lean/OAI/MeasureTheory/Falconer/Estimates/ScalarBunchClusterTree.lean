import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterBunching

namespace OAI

/-! The bunch ledger realized as a tree of entire terminal fibers. -/
namespace Falconer.Regularization

noncomputable def scalarBunchClusterTree {N top lo m : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d k : ℕ → ℕ) (hd : Monotone d) (hdtop : d top ≤ N) (hm : 0 < m)
    (g : ScalarBunch → ℝ)
    (hlevels : ∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
      (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (g b))
    (hgap : ∀ b ∈ bs, 5*(1/2:ℝ)^(d b.stop) < g b)
    (hleaf : ∀ p ∈ Q.image (List.take (d top)), (prefixFiber Q (d top) p).card = m) :
    ScalarClusterTree ((1/2:ℝ)^N) bs.length := by
  let depth := fun i => d (scalarBunchBoundary lo bs i)
  let branch := fun i => (bs.map (fun b => 2^(∑ j ∈ Finset.Ico b.start b.cut, k j))).getD i 1
  let gap := fun i => (bs.map g).getD i 1
  apply scalarClusterPathTreeOfLevels Q hQ depth branch gap
  · intro i _
    exact (hd (hchain.boundary_bounds i).2).trans hdtop
  · exact hm
  · intro i hi
    dsimp [branch]
    rw [scalarBunchValue_at _ _ hi]
    positivity
  · intro i hi
    have he := hchain.boundary_edges i hi
    dsimp [depth,branch,gap]
    rw [he.1,he.2,scalarBunchValue_at _ _ hi,scalarBunchValue_at _ _ hi]
    exact hlevels bs[i] (List.getElem_mem hi)
  · intro i hi
    have he := hchain.boundary_edges i hi
    dsimp [depth,gap]
    rw [he.1,scalarBunchValue_at _ _ hi]
    exact hgap bs[i] (List.getElem_mem hi)
  · dsimp [depth]
    rw [hchain.boundary_zero]
    exact hleaf


end Falconer.Regularization

end OAI
