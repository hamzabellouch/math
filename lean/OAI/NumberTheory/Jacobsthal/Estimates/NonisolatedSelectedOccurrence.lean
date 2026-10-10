import OAI.NumberTheory.Jacobsthal.Paths.GeometricRegularWords

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.NonisolatedSelectedOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain FiniteHistoryTransport
open ActualSuccessfulHistories ActualCoupledHistories CompactPrefixOccurrence SourceSelectedCompactOccupation
open NonisolatedWordOccurrence GoodCrossingVisit CrossingPrimeBin
open CompletedArrivalOccurrence PersistentFailureFlag CanonicalCoupledHistories

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hwn hell hS0 hS hr hsS in
theorem selected_nonisolated_probability {top xi B theta T mesh : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hB : 0 < B) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (hT : 1 ≤ T)
    (h199 : 199/100 ≤ start.ratio) (hc : PrimeBinMembership.Consistent start) (hcut : start.cutoff=B)
    (hcap : w^start.cutoff=top) (hm : 0 < mesh) (hmesh : mesh ≤ 1) (N : ℕ)
    (hexp : Real.exp (4*(N:ℝ)*mesh) ≤ 11/10)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta (T+1)*B) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E → p.node.gap ≤ theta*B ∧
      noIsolatedWord hw htop hxi B (isolatedAlpha theta (T+1)) (4*theta) p.primes) :
    fullSourceLaw w ell S start hs mesh N {h | occurs E N h} ≤
      FlaggedSourceStart.sourceLaw hwn hell hS0 hS hr hs hsS mesh N failed +
      finitePathMeasure (FlaggedSourceStart.typedState start.side start.ratio hs) N
        (FiniteHistoryOccurrence.arrivalOccurrence (crossingHighEvent (Real.log start.gap) (theta*B) T) N) := by
  rw [fullSourceLaw_eq hwn hell hS0 hS hr hs hsS]
  have hsub : ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      occurs E N h → h ∈ {h | (last N h).2=true} ∪
        ((mapHist (fun q => q.1.2) N) ⁻¹' {h | completedOccurrence (crossingHighEvent (Real.log start.gap) (theta*B) T) N h}) := by
    filter_upwards [nonisolated_word_occurs hwn hell hS0 hS hr hs hsS hw htop hxi hB htheta htheta1 hT
      h199 hc hcut hcap hm hmesh N hexp hwidth] with h hh
    intro ho
    cases hf : (last N h).2 with
    | true => exact Or.inl hf
    | false =>
      apply Or.inr
      obtain ⟨j,hj⟩ := ho
      let k : Finset.Iic N := ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩
      change selectedNode E ((h k).1.1) at hj
      cases hp : (h k).1.1 with
      | none => rw [hp] at hj; exact False.elim hj
      | some p =>
        rw [hp] at hj
        exact hh hf k p hp (hE p hj).1 (hE p hj).2
  have hu := (measure_mono_ae hsub).trans (measure_union_le _ _)
  rw [sourceHistory_failure_probability hwn hell hS0 hS hr hs hsS mesh N] at hu
  exact hu.trans (add_le_add le_rfl (source_completed_occurrence_le hwn hell hS0 hS hr hs hsS mesh N
    (crossingHighEvent_measurable _ _ _)))
end NumberTheoryLean.NonisolatedSelectedOccurrence


end Erdos970

end OAI
