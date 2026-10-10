import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteLayout
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TemplateMatrix
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteBad

namespace OAI

/-! Apply a checked finite-layout obstruction to an actual optimal path
system. The numerical profile supplies the amount and assigned-path count. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V}

theorem initial_layout_refutation (hCE : CEAlphaTwo) {k t n : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    {S : ExpandedPathSystem G Q} (hopt : S.IsOptimal k)
    (U : RawPathSystem G Q) (hUv : U.vertices = Q ∪ S.vertices)
    (hUa : U.amount = S.amount) (hUe : U.assignedCount = S.assignedCount)
    {P : List (List ℕ)} (hp : List.Forall₂ (AssignedAmounts Q) U.chains P)
    (hne : ∀ l ∈ U.chains, l ≠ [])
    (D : List (List (Fin n))) (Q₀ : Finset (Fin n))
    (hindex : D.flatten = List.finRange n)
    (hlength : D.map List.length = P.map (fun w => w.sum + w.length + 1))
    (hmask : D.map (cliqueMask Q₀) = P.map profileMask)
    (E : List (TemplateData (Fin n)))
    (hE : ∀ T ∈ E, T.Check (layoutGraph Q₀ D) Q₀ k (patternAmount P) (P.map List.length).sum)
    (R : List (RequiredPathData (Fin n))) (hR : ∀ p ∈ R, p.Check (layoutGraph Q₀ D) k)
    (b : BadData n)
    (hb : b.Check (layoutGraph Q₀ D)
      (fun i j => templateMatrix E i j ∪ requiredMatrix k R i j) k t) : False := by
  classical
  obtain ⟨f, hf, hmap, hfQ, hfG⟩ := U.realize_layout hp hne hQ D Q₀ hindex hlength hmask
  let F : layoutGraph Q₀ D →g G := ⟨f, fun h => hfG h⟩
  have hfX : ∀ i, f i ∈ Q ∪ S.vertices := by
    intro i
    rw [← hUv]
    apply List.mem_toFinset.mpr
    rw [← hmap, ← List.map_flatten, hindex]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have hX : (Q ∪ S.vertices).card = n := by
    rw [← hUv]
    change U.chains.flatten.toFinset.card = n
    rw [List.toFinset_card_of_nodup U.flatten_nodup, ← hmap,
      ← List.map_flatten, List.length_map, hindex, List.length_finRange]
  have ha : S.amount = patternAmount P := by
    rw [← hUa, U.amount_eq_outside_count, ← ChainProfiles.amount hp]
  have he : S.assignedCount = (P.map List.length).sum := by
    rw [← hUe]
    exact (ChainProfiles.assignedCount hp).symm
  have hT := templateMatrix_sound hopt (by omega) hQk hQ hcycle ha he f hf hfQ hfG
    (fun i => Finset.mem_union.mp (hfX i)) E hE
  have hR' := requiredMatrix_sound (by omega) hcycle F hf hfX R hR
  exact b.false_of_check hCE hk ht hcycle hclique hbound F hf hfX hX
    (hT.union hR') hexpand hb

end CycleClique.Construction

end OAI
