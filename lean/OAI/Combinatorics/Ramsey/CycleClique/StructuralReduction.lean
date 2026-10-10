import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.DenseCycles
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.ExteriorFrames
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.FrameProperties
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.LargeSystems
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.ThreeCycles

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph

 
theorem Frame.exists_of_cliqueNum {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (ht : t ≤ G.cliqueNum) : Nonempty (Frame G t) := by
  obtain ⟨f⟩ := (complete_isContained_iff_le_cliqueNum G t).mpr ht
  exact ⟨⟨f.toEmbedding, fun i j hij => f.toHom.map_rel' (by simpa using hij)⟩⟩

 
theorem reduced_small_impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (hk' : k ≤ 4) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k*a+1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard) : False := by
  obtain ⟨hl,hu⟩ := counterexample_clique_bound hk ha hak horder hα hcycle hexp
  have hthree : 3 ≤ G.cliqueNum := (le_max_left _ _).trans hl
  obtain ⟨T⟩ := Frame.exists_of_cliqueNum hthree
  interval_cases k
  · exact (show ThreeHyp G a from ⟨horder,hα,hak,hcycle,hu,hexp⟩).contradiction T
  · have ho : Fintype.card V ≤ 17 := by omega
    by_cases hfour : 4 ≤ G.cliqueNum
    · obtain ⟨S⟩ := Frame.exists_of_cliqueNum hfour
      exact small_four_clique ho hcycle hexp S
    · exact (show FourHyp G from ⟨ho,hcycle,by omega,hexp⟩).contradiction T

 

theorem reduced_large_impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k*a+1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    (hnine : 9 ≤ G.cliqueNum) : False := by
  classical
  obtain ⟨hl,hu⟩ := counterexample_clique_bound hk ha hak horder hα hcycle hexp
  obtain ⟨Q,hQ⟩ := G.exists_isNClique_cliqueNum
  have hc : (Q : Set V).ncard = G.cliqueNum := by
    rw [Set.ncard_coe_finset,hQ.card_eq]
  obtain ⟨P,hP⟩ := PathSystem.exists_optimal G (Q : Set V) (k:=k) (by omega)
  have hhalf : k/2 ≤ G.cliqueNum := (le_max_right _ _).trans hl
  have H : LargeSystem G (Q : Set V) k P :=
    ⟨hP,hQ.isClique,hcycle,by omega,by omega,by omega,by omega,hα.trans hak,hexp⟩
  exact H.contradiction

end CycleClique

end OAI
