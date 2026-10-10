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
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.FrameProperties
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.LowerBound
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.Minimality
import OAI.Combinatorics.Ramsey.CycleClique.PatternReduction
import OAI.Combinatorics.Ramsey.CycleClique.Patterns10x5
import OAI.Combinatorics.Ramsey.CycleClique.Patterns10x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns10x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns10x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns11x5
import OAI.Combinatorics.Ramsey.CycleClique.Patterns11x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns11x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns11x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns12x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns12x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns12x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns13x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns13x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns13x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns14x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns14x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns15x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns15x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns16x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns17x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns5x3
import OAI.Combinatorics.Ramsey.CycleClique.Patterns5x4
import OAI.Combinatorics.Ramsey.CycleClique.Patterns5x5
import OAI.Combinatorics.Ramsey.CycleClique.Patterns6x3
import OAI.Combinatorics.Ramsey.CycleClique.Patterns6x4
import OAI.Combinatorics.Ramsey.CycleClique.Patterns6x5
import OAI.Combinatorics.Ramsey.CycleClique.Patterns6x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns7x3
import OAI.Combinatorics.Ramsey.CycleClique.Patterns7x4
import OAI.Combinatorics.Ramsey.CycleClique.Patterns7x5
import OAI.Combinatorics.Ramsey.CycleClique.Patterns7x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns7x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns8x4
import OAI.Combinatorics.Ramsey.CycleClique.Patterns8x5
import OAI.Combinatorics.Ramsey.CycleClique.Patterns8x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns8x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns8x8
import OAI.Combinatorics.Ramsey.CycleClique.Patterns9x4
import OAI.Combinatorics.Ramsey.CycleClique.Patterns9x5
import OAI.Combinatorics.Ramsey.CycleClique.Patterns9x6
import OAI.Combinatorics.Ramsey.CycleClique.Patterns9x7
import OAI.Combinatorics.Ramsey.CycleClique.Patterns9x8
import OAI.Combinatorics.Ramsey.CycleClique.StructuralReduction

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph

 
theorem finite_range_verified {k t : ℕ} (hk : 5 ≤ k) (ht : 3 ≤ t)
    (htk : t ≤ k) (ht8 : t ≤ 8) (hhalf : k/2 ≤ t) :
    ∀ D ∈ patternChoices t (k-t) [], PatternVerified k t D := by
  have hk17 : k ≤ 17 := by omega
  interval_cases k
  · have htmin : 3 ≤ t := by omega
    have htmax : t ≤ 5 := by omega
    interval_cases t
    · exact finite_patterns_5_3
    · exact finite_patterns_5_4
    · exact finite_patterns_5_5
  · have htmin : 3 ≤ t := by omega
    have htmax : t ≤ 6 := by omega
    interval_cases t
    · exact finite_patterns_6_3
    · exact finite_patterns_6_4
    · exact finite_patterns_6_5
    · exact finite_patterns_6_6
  · have htmin : 3 ≤ t := by omega
    have htmax : t ≤ 7 := by omega
    interval_cases t
    · exact finite_patterns_7_3
    · exact finite_patterns_7_4
    · exact finite_patterns_7_5
    · exact finite_patterns_7_6
    · exact finite_patterns_7_7
  · have htmin : 4 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_8_4
    · exact finite_patterns_8_5
    · exact finite_patterns_8_6
    · exact finite_patterns_8_7
    · exact finite_patterns_8_8
  · have htmin : 4 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_9_4
    · exact finite_patterns_9_5
    · exact finite_patterns_9_6
    · exact finite_patterns_9_7
    · exact finite_patterns_9_8
  · have htmin : 5 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_10_5
    · exact finite_patterns_10_6
    · exact finite_patterns_10_7
    · exact finite_patterns_10_8
  · have htmin : 5 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_11_5
    · exact finite_patterns_11_6
    · exact finite_patterns_11_7
    · exact finite_patterns_11_8
  · have htmin : 6 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_12_6
    · exact finite_patterns_12_7
    · exact finite_patterns_12_8
  · have htmin : 6 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_13_6
    · exact finite_patterns_13_7
    · exact finite_patterns_13_8
  · have htmin : 7 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_14_7
    · exact finite_patterns_14_8
  · have htmin : 7 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_15_7
    · exact finite_patterns_15_8
  · have htmin : 8 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_16_8
  · have htmin : 8 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_17_8

 

theorem finite_verification {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k t : ℕ} (hk : 5 ≤ k) (_ : k ≤ 17)
    (hl : max 3 (k/2) ≤ t) (hu : t ≤ min 8 k)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G) (hclique : G.cliqueNum = t)
    (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard) : False := by
  classical
  obtain ⟨Q,hQ⟩ := G.exists_isNClique_cliqueNum
  have hc : (Q : Set V).ncard = t := by
    rw [Set.ncard_coe_finset,hQ.card_eq,hclique]
  have ht : 3 ≤ t := (le_max_left _ _).trans hl
  have ht8 : t ≤ 8 := hu.trans (min_le_left _ _)
  have htk : t ≤ k := hu.trans (min_le_right _ _)
  have hhalf : k/2 ≤ t := (le_max_right _ _).trans hl
  have H : FiniteHyp G k t := ⟨hk,ht,htk,hcycle,le_of_eq hclique,hα,hexp⟩
  exact finite_verified_of_patterns H hQ.isClique hc
    (finite_range_verified hk ht htk ht8 hhalf)

 

theorem reduced_counterexample_impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k*a+1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard) : False := by
  classical
  by_cases hsmall : k ≤ 4
  · exact reduced_small_impossible hk hsmall ha hak horder hα hcycle hexp
  by_cases hnine : 9 ≤ G.cliqueNum
  · exact reduced_large_impossible hk ha hak horder hα hcycle hexp hnine
  obtain ⟨hl,hu⟩ := counterexample_clique_bound hk ha hak horder hα hcycle hexp
  exact finite_verification (by omega) (by omega) hl (by omega) hcycle rfl
    (hα.trans hak) hexp

 
theorem ramsey_upper {k a₀ : ℕ} (hk : 3 ≤ k) (ha₀ : 2 ≤ a₀) (ha₀k : a₀ ≤ k) :
    RamseyProperty (k+1) (a₀+1) (k*a₀+1) := by
  by_contra hfailure
  obtain ⟨a,ha,hak,G,hcycle,hα,hexp⟩ := minimal_expanding_counterexample ha₀ ha₀k hfailure
  exact reduced_counterexample_impossible hk ha hak (Fintype.card_fin _) hα hcycle hexp

 

theorem main (m n : ℕ) (hmn : n ≤ m) (hn : 3 ≤ n)
    (hne : (m, n) ≠ (3, 3)) :
    cycleCliqueRamsey m n = (m - 1) * (n - 1) + 1 := by
  have hm : 4 ≤ m := by
    by_contra hh
    have hm3 : m=3 := by omega
    have hn3 : n=3 := by omega
    exact hne (by simp [hm3,hn3])
  have hupper : RamseyProperty m n ((m-1)*(n-1)+1) := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega),
      Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      (ramsey_upper (k:=m-1) (a₀:=n-1) (by omega) (by omega) (by omega))
  apply le_antisymm
  · exact Nat.sInf_le hupper
  · have hmem : RamseyProperty m n (cycleCliqueRamsey m n) :=
      Nat.sInf_mem (s:={N | RamseyProperty m n N}) ⟨(m-1)*(n-1)+1,hupper⟩
    exact ramsey_property_lower_bound (by omega) (by omega) hmem

end CycleClique

end OAI
