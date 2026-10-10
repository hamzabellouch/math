import OAI.NumberTheory.Jacobsthal.Analysis.SourceCompactSingletons
import OAI.NumberTheory.Jacobsthal.Estimates.SourceFirstCrossing
import OAI.NumberTheory.Jacobsthal.Partitions.RegularityDefectPartition
import OAI.NumberTheory.Jacobsthal.Primes.CrossingPrimeBin

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GoodCrossingVisit
open _root_.Set _root_.MeasureTheory FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeTiltGeometry
open RegeneratingInverseBands ArrivalKernelGeometry ActualFlagInvariant CrossingPrimeBin CrossingBandGeometry
open IsolatedBinGeometry LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

noncomputable def crossingHighEvent (v H T : ℝ) : Set CostState :=
  {y | T < stateRatio y.1 ∧ y.2 ∈ Icc (crossingCenter v H) (crossingCenter v H+crossingWidth)}

theorem crossingHighEvent_measurable (v H T : ℝ) : MeasurableSet (crossingHighEvent v H T) :=
  (measurableSet_lt measurable_const (stateRatio_measurable.comp measurable_fst)).inter
    (measurable_snd measurableSet_Icc)

theorem good_crossing_visit {w top xi ell S theta T B v mesh : ℝ} {N : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hell : 1 ≤ ell)
    (htheta : 0 < theta) (hT : 1 ≤ T) (hB : 0 < B) (hm : mesh ≤ 1)
    (he : Real.exp (4*(N:ℝ)*mesh) ≤ 11/10)
    (z : Node) (hs : Valid z.side z.ratio) (hcap : w^z.cutoff=top)
    (p : History w ell S z) (hne : p.primes ≠ []) (y : CostState)
    (hg : liveGood v mesh N p y)
    (hlo : theta*B/3 < p.node.gap) (hhi : p.node.gap ≤ theta*B)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta (T+1)*B)
    (hno : ¬isolatedBin w top xi B (isolatedAlpha theta (T+1)) (4*theta)
      (label (zero_lt_one.trans hw) htop hxi (p.primes.getLastD 0))) :
    y ∈ crossingHighEvent v (theta*B) T := by
  have hratio : T < stateRatio y.1 := by
    by_contra! hr
    have hpT : p.node.ratio ≤ T+1 := by linarith [(abs_le.mp hg.2.2.1).2]
    exact hno (actual_crossing_bin hw htop hxi hell htheta (by linarith) hB z hs hcap p hne hlo hhi hpT hwidth)
  have hp0 : 0 < p.node.gap := by nlinarith
  have hband := matched_gap_crossing (mul_pos htheta hB) hp0 (Real.exp_pos _) hlo hhi hg.2.2.2 he
  exact ⟨hratio,crossing_cost_band (mul_pos htheta hB) v y hband⟩
end NumberTheoryLean.GoodCrossingVisit



namespace NumberTheoryLean.NonisolatedWordOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain FiniteHistoryTransport
open ActualSuccessfulHistories ActualCoupledHistories PrimePrefixRecovery ActualFlagInvariant RepeatedPairEvents
open SourceFirstCrossing GoodCrossingVisit CrossingPrimeBin IsolatedBinGeometry
open CompletedArrivalOccurrence LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open PersistentFailureFlag

noncomputable def noIsolatedWord {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (B alpha beta : ℝ) (ps : List ℕ) : Prop :=
    ∀ p ∈ ps,¬isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p)

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem nonisolated_word_occurs {top xi B theta T mesh : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hB : 0 < B) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (hT : 1 ≤ T)
    (h199 : 199/100 ≤ start.ratio) (hc : PrimeBinMembership.Consistent start) (hcut : start.cutoff=B)
    (hcap : w^start.cutoff=top) (hm : 0 < mesh) (hmesh : mesh ≤ 1) (N : ℕ)
    (hexp : Real.exp (4*(N:ℝ)*mesh) ≤ 11/10)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta (T+1)*B) :
    ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      (last N h).2=false → ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p →
        p.node.gap ≤ theta*B → noIsolatedWord hw htop hxi B (isolatedAlpha theta (T+1)) (4*theta) p.primes →
        completedOccurrence (crossingHighEvent (Real.log start.gap) (theta*B) T) N
          (mapHist (fun q => q.1.2) N h) := by
  filter_upwards [sourceHistory_success_good hwn hell hS0 hS hr hs hsS hm N,
    sourceHistory_recovers_prefix hwn hell hS0 hS hr hs hsS mesh N] with h hgood hprefix
  intro hf j p hp hend hno
  obtain ⟨pre,a,tail,hpre,he,_hbefore,hhi,hlo⟩ :=
    source_gap_crossing (by linarith) hB htheta1 start hs h199 hc hcut p.primes p.admissible hend
  have hword : p.primes=(pre++[a])++tail := by simpa only [List.append_assoc,List.singleton_append] using he
  obtain ⟨hk,q,hq,hqword⟩ := hprefix j p hp (pre++[a]) tail hword
  have hn : (pre++[a]).length ≠ 0 := by simp
  let i : Finset.Iic N := ⟨(pre++[a]).length,Finset.mem_Iic.mpr hk⟩
  let k : Fin N := ⟨(pre++[a]).length-1,by omega⟩
  have hkval : k.1+1=(pre++[a]).length := by dsimp [k]; omega
  have hg := goodAt_enlarge hm.le hk _ (hgood hf i)
  change GoodAt (Real.log start.gap) mesh N ((h i).1.1,(h i).1.2) at hg
  rw [hq] at hg
  cases hy : (h i).1.2 with
  | inr u => rw [hy] at hg; exact False.elim hg
  | inl y =>
    rw [hy] at hg
    have hqne : q.primes ≠ [] := by rw [hqword]; simp
    have hqhi : q.node.gap ≤ theta*B := by change (terminal w start q.primes).gap ≤ _; rwa [hqword]
    have hqlo : theta*B/3 < q.node.gap := by change _ < (terminal w start q.primes).gap; rwa [hqword]
    have ha : a ∈ p.primes := by rw [he]; simp
    have hlast : q.primes.getLastD 0=a := by rw [hqword]; exact List.getLastD_concat
    have hno' : ¬isolatedBin w top xi B (isolatedAlpha theta (T+1)) (4*theta)
        (label (zero_lt_one.trans hw) htop hxi (q.primes.getLastD 0)) := by rw [hlast]; exact hno a ha
    have hv := good_crossing_visit hw htop hxi hell htheta hT hB hmesh hexp start hs hcap q hqne y hg hqlo hqhi hwidth hno'
    refine ⟨k,?_⟩
    change liveMember _ ((h ⟨k.1+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.2)
    have hy' : (h ⟨k.1+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.2=Sum.inl y := by
      simpa only [hkval] using hy
    rw [hy']
    exact hv
end NumberTheoryLean.NonisolatedWordOccurrence



namespace NumberTheoryLean.GeometricRegularWords
open FinitePathGeometry PrimeHistories ActualRegularBoxes RepeatedWordEvents NonisolatedWordOccurrence
open SourceCompactSingletons IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

noncomputable def geometricWords {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Clen B R L alpha beta : ℝ) (z : Node) : Finset (List ℕ) :=
  (regularWords hw htop hxi Clen B R z).filter (fun ps =>
    ¬compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L z ps ∧
    ¬noIsolatedWord hw htop hxi B alpha beta ps)

theorem geometric_isolated_prime {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z) :
    ∃ p ∈ ps,isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p) := by
  have h := (Finset.mem_filter.mp hp).2.2
  simpa only [noIsolatedWord,not_forall,not_not,exists_prop] using h

theorem geometric_compact_singleton {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z)
    (pre tail : List ℕ) (p : ℕ) (he : ps=pre++p::tail) (hgap : (terminal w z pre).gap ≤ L) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).count (label (zero_lt_one.trans hw) htop hxi p)=1 := by
  have hr := Finset.mem_filter.mp hp
  have hd := ErdosPrimeInputs.PrimePrefixMass.mem_decreasingPrefixes.mp (Finset.mem_filter.mp hr.1).1
  exact source_compact_singleton hw htop hxi L z ps hd.1 hd.2 hr.2.1 pre tail p he hgap
end NumberTheoryLean.GeometricRegularWords


end Erdos970

end OAI
