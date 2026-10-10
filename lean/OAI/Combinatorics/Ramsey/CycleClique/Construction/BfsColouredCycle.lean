import OAI.Combinatorics.Ramsey.CycleClique.Construction.BfsBranchPath
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ColouredPathFull

namespace OAI

/-! A coloured path in one layer closes through its two predecessor branches. -/

namespace CycleClique.Construction
theorem layer_cycle_of_two_branches {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d p s k : ℕ}
    (hs : 4 ≤ s) (hk : 2 * s ≤ k) (hk' : k ≤ 2 * s + 1)
    (hp : 2 ≤ p) (hps : p ≤ s) (hpd : p ≤ d)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d)
    (hconn : (G.induce (Y : Set V)).Connected)
    (hnonbip : ¬ (G.induce (Y : Set V)).IsBipartite)
    (hno : G.cliqueNum < s)
    (hdegree : ∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard)
    (hpair : ∀ a b : Y, a ≠ b → ¬ G.Adj a.val b.val →
      2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {a, b}).card)
    (c : V) (χ : Y → Fin 2) (hnonconstant : ∃ a b, χ a ≠ χ b)
    (hcommon : ∀ v : Y, (bfsParent G root)^[p] v.val = c)
    (hsplit : ∀ u v : Y, χ u ≠ χ v → ∀ j < p,
      (bfsParent G root)^[j] u.val ≠ (bfsParent G root)^[j] v.val) :
    HasCycle G (k + 1) := by
  classical
  let ℓ := k + 1 - 2 * p
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; omega
  have hℓmax : ℓ ≤ 2 * s - 2 := by dsimp [ℓ]; omega
  have hHno : (G.induce (Y : Set V)).cliqueNum < s :=
    (G.cliqueNum_induce_le _).trans_lt hno
  obtain ⟨f, hf, hfχ⟩ := colored_path_prescribed_length hs hconn hnonbip hHno
    hdegree hpair χ hnonconstant hℓ hℓmax
  let F : Fin (ℓ + 1) → V := fun i => (f i).val
  have hF : IsIndexedPath G F := by
    refine ⟨fun i j h => hf.1 (Subtype.ext h), fun i => hf.2 i⟩
  let u := f (Fin.last ℓ)
  let v := f 0
  have hu := hlayer u.val u.property
  have hv := hlayer v.val v.property
  let B := bfsBranchPath G root u.val v.val p
  have hB : IsIndexedPath G B := bfsBranchPath_isPath hu.1 hv.1 hu.2 hv.2 hpd
    ((hcommon u).trans (hcommon v).symm) (hsplit u v hfχ.symm)
  have hcycle : HasCycle G (ℓ + 2 * p) := cycle_of_two_indexed_paths (by omega)
    F B hF hB (bfsBranchPath_start _ _ _ _ _) (bfsBranchPath_end _ _ _ _ (by omega)) (by
      intro i hi hilast j heq
      have hlevel := (hlayer (f j).val (f j).property).2
      have hBlevel := bfsBranchPath_internal_level hu.1 hv.1 hu.2 hv.2 hpd i hi hilast
      change G.dist root (B i) < d at hBlevel
      change G.dist root (F j) = d at hlevel
      rw [← heq, hlevel] at hBlevel
      omega)
  have hsum : ℓ + 2 * p = k + 1 := by dsimp [ℓ]; omega
  simpa only [hsum] using hcycle

end CycleClique.Construction

end OAI
