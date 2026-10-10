import OAI.NumberTheory.Jacobsthal.Analysis.CanonicalBadCompact
import OAI.NumberTheory.Jacobsthal.Analysis.SourceBadCompactOccurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedOccurrenceProbability

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories ActualSuccessfulHistories ActualProcessCoupling FlaggedSourceStart
open FiniteHistoryTransport PriorPrimeWindow CompactPrefixOccurrence CompletedMarkEvents
open SourceBadCompactOccurrence CanonicalBadCompact ContinuousKilledBins PersistentFailureFlag
open Erdos970Dependency.MarkedVisits

variable {w ell S R b₀ b₁ : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem missing_occurrence_probability (hc : Consistent start)
    (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : (11/10)*R < 6*b₀)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E →
      p.node.gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start p.primes) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | occurs E N h} ≤
      sourceLaw hw hell hS0 hS hr hs hsS mesh N failed +
      finitePathMeasure (typedState start.side start.ratio hs) N
        (closedNoHitEvent 1 N start.gap b₀ b₁ 1) := by
  let μ := sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N
  let F : Set (Hist (FlagState (JointState w ell S start)) N) := {h | (last N h).2 = true}
  let C : Set (Hist (FlagState (JointState w ell S start)) N) :=
    mapHist (fun q => q.1.2) N ⁻¹' badCompactPath (Real.log start.gap) ((11/10)*R) b₀ b₁ N
  have hF : μ F = sourceLaw hw hell hS0 hS hr hs hsS mesh N failed :=
    sourceHistory_failure_probability hw hell hS0 hS hr hs hsS mesh N
  have hC : μ C ≤ finitePathMeasure (typedState start.side start.ratio hs) N
      (closedNoHitEvent 1 N start.gap b₀ b₁ 1) := by
    dsimp [μ,C]
    rw [← Measure.map_apply
      (by exact mapHist_measurable (by exact measurable_snd.comp measurable_fst) N)
      (badCompactPath_measurable _ _ _ _ _),sourceHistoryLaw_continuous]
    exact completed_bad_compact_mass hr hb₀ hb₁ hR ell S (typedState start.side start.ratio hs) N
  calc
    _ ≤ μ (F ∪ C) := measure_mono_ae
      (missing_occurrence_inclusion hw hell hS0 hS hr hs hsS hc hb₀ hm hmesh N herror E hE)
    _ ≤ μ F + μ C := measure_union_le F C
    _ ≤ _ := by rw [hF]; exact add_le_add le_rfl hC

end NumberTheoryLean.MarkedOccurrenceProbability

end

end Erdos970

end OAI
