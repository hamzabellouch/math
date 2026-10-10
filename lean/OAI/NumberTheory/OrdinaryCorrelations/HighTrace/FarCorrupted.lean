import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CorruptWitness
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorPath
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DisconnectedErrorSum
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PackedGapPrefactorMonoPath

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.NumericalSubtrees Finset Classical Filter
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}

def farCorrupted (w : NumericalLine D h ℓ) (K : ℕ) : Finset S.Index :=
  (univ.filter (freeCorrupted w.line)) \ shortCorrupted w K

lemma short_far_corrupted_card (w : NumericalLine D h ℓ) (K : ℕ) :
    (shortCorrupted w K).card+(farCorrupted w K).card=corruptedCount S w.line := by
  have hs : shortCorrupted w K ⊆ univ.filter (freeCorrupted w.line) := by
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hp).2.1⟩
  simpa only [farCorrupted,corruptedCount,Nat.add_comm] using card_sdiff_add_card_eq_card hs

lemma farCorrupted_walk_long (w : NumericalLine D h ℓ) (hh : 0<h) (p : S.Index)
    (hp : p ∈ farCorrupted w K) (c : CorruptWitness w p)
    {s : ℤ} (hs : s=w.line.offset c.edge.castSucc ∨ s=w.line.offset c.edge.succ)
    (q : (edgeGraph w.line hh w.line.treeSteps).Walk s (w.line.offset c.vertex)) :
    K<q.length := by
  by_contra hlen
  have hfree := (mem_filter.mp (mem_sdiff.mp hp).1).2
  obtain ⟨P,hP0,hPL,hPa,hPd⟩ := c.near_path hh hfree.1 hs q (le_of_not_gt hlen)
  apply (mem_sdiff.mp hp).2
  exact mem_filter.mpr ⟨mem_univ _,hfree,⟨⟨P,hPa,hPd⟩⟩⟩

namespace NumericalLine

def farCorruptSum {B τ T C₀ : ℝ} (D : (sourceSystem B).DivisorFamily B τ C₀)
    (h ℓ : ℕ) (cut : (sourceSystem B).Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ,avg (fun r : (sourceSystem B).Residues =>
    if (1/2)*B^(1-2*rho) ≤ ((farCorrupted w (corruptPathLength B)).card:ℝ) then
      |(sourceSystem B).chronologicalKernel w.line cut r*allowedIndicator w.line D (pathLength B) r|
    else 0)

lemma corrupted_near_far_of_threshold {B τ T C₀ : ℝ} {h ℓ : ℕ}
    (D : (sourceSystem B).DivisorFamily B τ C₀) (cut : (sourceSystem B).Cutoffs T)
    (hthreshold : (((2*(corruptPathLength B*⌈C₀*Real.log B⌉₊)+1)*listCutoff B:ℕ):ℝ) ≤
      (1/2)*B^(1-2*rho)) :
      corruptedErrorSum D (h:=h) (ℓ:=ℓ) cut ≤
        nearCorruptSum D h ℓ (pathLength B) (corruptPathLength B) (listCutoff B) cut+
        farCorruptSum D h ℓ cut := by
  unfold corruptedErrorSum nearCorruptSum farCorruptSum
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro w hw
  rw [←OrdinaryCorrelations.SourceCylinder.avg_add']
  apply avg_mono
  intro r
  by_cases hc : B^(1-2*rho) ≤ (corruptedCount (sourceSystem B) w.line:ℝ)
  · rw [ite_eq_left hc]
    by_cases hn : w.ManyShortCorrupted (corruptPathLength B) (listCutoff B)
    · rw [ite_eq_left hn]
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    · have hnf : ((shortCorrupted w (corruptPathLength B)).card:ℝ)<(1/2)*B^(1-2*rho) := by
        have ht : (shortCorrupted w (corruptPathLength B)).card <
            (2*(corruptPathLength B*⌈C₀*Real.log B⌉₊)+1)*listCutoff B := lt_of_not_ge hn
        exact (Nat.cast_lt.mpr ht).trans_le hthreshold
      have hsum := congrArg (fun n : ℕ => (n:ℝ)) (short_far_corrupted_card w (corruptPathLength B))
      push_cast at hsum
      have hf : (1/2)*B^(1-2*rho) ≤ ((farCorrupted w (corruptPathLength B)).card:ℝ) := by linarith
      rw [ite_eq_left hf]
      exact le_add_of_nonneg_left (by split_ifs; positivity)
  · rw [ite_eq_right hc]
    apply add_nonneg <;> split_ifs <;> positivity

theorem source_full_trace_near_far (h : ℕ) (hh : 0<h) (τ T C₀ : ℝ)
    (hτ : 1≤τ) (hτ2 : τ<2) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ))+3*Real.exp (-B^(1+epsilon/2))+
          disconnectedErrorSum D (ℓ:=sourceLength B) hh cut+
          farCorruptSum D h (sourceLength B) cut := by

  filter_upwards [source_full_trace_two_errors h hh τ T C₀ hτ hτ2 hC₀,
    source_near_corrupt_small h τ T C₀ hC₀,
    source_near_corrupt_threshold C₀ hC₀,eventually_ge_atTop (1:ℝ)] with B ht hn hthreshold hB
  intro D cut
  have he : corruptedErrorSum D (h:=h) (ℓ:=sourceLength B) cut ≤
      nearCorruptSum D h (sourceLength B) (pathLength B) (corruptPathLength B) (listCutoff B) cut+
      farCorruptSum D h (sourceLength B) cut := by
    
    exact corrupted_near_far_of_threshold D cut hthreshold
  have hs := hn D cut (corruptPathLength B) (corruptPathLength_le B hB)
  linarith [ht D cut]

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
