import OAI.MeasureTheory.Falconer.Measures.ScalarBunchPruning
import Mathlib.Data.List.GetD

namespace OAI

/-! The realized ledger, ordered from fine to coarse scales, is the
 separated tree consumed by the porous projection estimate. -/
namespace Falconer

def scalarBunchBoundary (lo : ℕ) (bs : List ScalarBunch) (i : ℕ) : ℕ :=
  (bs.map ScalarBunch.stop).getD i lo

 theorem ScalarBunchChain.boundary_zero {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) : scalarBunchBoundary lo bs 0 = top := by
  cases h <;> simp [scalarBunchBoundary]

 theorem ScalarBunchChain.boundary_edges {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) : ∀ i (hi : i < bs.length),
    scalarBunchBoundary lo bs i = (bs[i]).stop ∧
      scalarBunchBoundary lo bs (i+1) = (bs[i]).start := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    intro i hi
    cases i with
    | zero =>
      constructor
      · simp [scalarBunchBoundary]
      · simpa only [scalarBunchBoundary,List.map_cons,List.getD_cons_succ,List.getElem_cons_zero]
          using h.boundary_zero
    | succ i =>
      simpa only [scalarBunchBoundary,List.map_cons,List.getD_cons_succ,List.getElem_cons_succ]
        using ih i (show i < bs.length by simpa using hi)

 theorem ScalarBunchChain.boundary_bounds {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) (i : ℕ) :
    lo ≤ scalarBunchBoundary lo bs i ∧ scalarBunchBoundary lo bs i ≤ top := by
  by_cases hi : i < bs.length
  · rw [(h.boundary_edges i hi).1]
    have hb := h.mem_bounds bs[i] (List.getElem_mem hi)
    exact ⟨hb.1.trans ((bs[i]).start_lt_cut.le.trans (bs[i]).cut_le_stop),hb.2⟩
  · have hx : (bs.map ScalarBunch.stop).length ≤ i := by simpa using Nat.le_of_not_gt hi
    simp only [scalarBunchBoundary,List.getD_eq_default _ _ hx]
    exact ⟨le_rfl,h.start_le⟩

 theorem scalarBunchValue_at {α : Type*} (f : ScalarBunch → α) (z : α)
    {bs : List ScalarBunch} {i : ℕ} (hi : i < bs.length) :
    (bs.map f).getD i z = f bs[i] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map]

namespace Regularization

noncomputable def scalarBunchSeparatedTreeOfLeaves {N top lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d k : ℕ → ℕ) (hd : Monotone d) (hdtop : d top ≤ N)
    (g : ScalarBunch → ℝ)
    (hlevels : ∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
      (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (g b))
    (hgap : ∀ b ∈ bs, 5*(1/2:ℝ)^(d b.stop) < g b)
    (hleaf : ∀ p ∈ Q.image (List.take (d top)), (prefixFiber Q (d top) p).card = 1) :
    ScalarSeparatedTree ((1/2:ℝ)^N) bs.length := by
  let depth := fun i => d (scalarBunchBoundary lo bs i)
  let branch := fun i => (bs.map (fun b => 2^(∑ j ∈ Finset.Ico b.start b.cut, k j))).getD i 1
  let gap := fun i => (bs.map g).getD i 1
  apply scalarSeparatedPathTreeOfLeafFibers Q hQ depth branch gap
  · intro i _
    exact (hd (hchain.boundary_bounds i).2).trans hdtop
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

noncomputable def scalarBunchSeparatedTree {N top lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d k : ℕ → ℕ) (hd : Monotone d) (hdtop : d top = N)
    (g : ScalarBunch → ℝ)
    (hlevels : ∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
      (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (g b))
    (hgap : ∀ b ∈ bs, 5*(1/2:ℝ)^(d b.stop) < g b) :
    ScalarSeparatedTree ((1/2:ℝ)^N) bs.length := by
  apply scalarBunchSeparatedTreeOfLeaves hchain Q hQ d k hd hdtop.le g hlevels hgap
  rw [hdtop]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 1 N q).mp (hQ hq)
  have htake : q.take N = q := by rw [← hlen,List.take_length]
  rw [htake,prefixFiber_leaf hQ hq]
  simp

end Regularization
end Falconer

end OAI
