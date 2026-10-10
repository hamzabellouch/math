import OAI.Combinatorics.Ramsey.CycleClique.Construction.BfsBranchPath
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ConnectedLongPath

namespace OAI

/-! If all vertices of a layer subgraph share one predecessor, a long path closes through it. -/

namespace CycleClique.Construction
theorem layer_cycle_of_one_predecessor {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d s k : ℕ}
    (hk : 3 ≤ k) (hks : k ≤ 2 * s + 1) (hcard : k ≤ Y.card) (hd : 1 ≤ d)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d)
    (hconn : (G.induce (Y : Set V)).Connected)
    (hdegree : ∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard)
    (c : V) (hcommon : ∀ v : Y, (bfsParent G root)^[1] v.val = c) :
    HasCycle G (k + 1) := by
  classical
  obtain ⟨r, f, hf, hr⟩ := connected_long_path hconn hdegree hks
    (hcard.trans_eq (Fintype.card_coe Y).symm)
  let ℓ := k - 1
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; omega
  have hℓr : ℓ ≤ r := by dsimp [ℓ]; omega
  let g : Fin (ℓ + 1) → Y := fun i => f (Fin.castLE (by omega) i)
  have hg : IsIndexedPath (G.induce (Y : Set V)) g := indexedPath_prefix hf hℓr
  let F : Fin (ℓ + 1) → V := fun i => (g i).val
  have hF : IsIndexedPath G F := ⟨fun i j h => hg.1 (Subtype.ext h), fun i => hg.2 i⟩
  let u := g (Fin.last ℓ)
  let v := g 0
  have hu := hlayer u.val u.property
  have hv := hlayer v.val v.property
  have hsplit : ∀ j < 1, (bfsParent G root)^[j] u.val ≠ (bfsParent G root)^[j] v.val := by
    intro j hj
    have hjzero : j = 0 := by omega
    simp only [hjzero, Function.iterate_zero, id_eq]
    intro heq
    have hindex := hg.1 (Subtype.ext heq)
    have hval := congrArg Fin.val hindex
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  let B := bfsBranchPath G root u.val v.val 1
  have hB : IsIndexedPath G B := bfsBranchPath_isPath hu.1 hv.1 hu.2 hv.2 hd
    ((hcommon u).trans (hcommon v).symm) hsplit
  have hcycle : HasCycle G (ℓ + 2 * 1) := cycle_of_two_indexed_paths (by omega)
    F B hF hB (bfsBranchPath_start _ _ _ _ _) (bfsBranchPath_end _ _ _ _ (by omega)) (by
      intro i hi hilast j heq
      have hlevel := (hlayer (g j).val (g j).property).2
      have hBlevel := bfsBranchPath_internal_level hu.1 hv.1 hu.2 hv.2 hd i hi hilast
      change G.dist root (B i) < d at hBlevel
      change G.dist root (F j) = d at hlevel
      rw [← heq, hlevel] at hBlevel
      omega)
  have hsum : ℓ + 2 * 1 = k + 1 := by dsimp [ℓ]; omega
  simpa only [hsum] using hcycle

end CycleClique.Construction

end OAI
