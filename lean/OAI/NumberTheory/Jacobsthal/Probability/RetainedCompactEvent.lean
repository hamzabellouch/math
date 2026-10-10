import OAI.NumberTheory.Jacobsthal.Paths.NearPrefixOccurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RetainedCompactEvent

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open PrimeBinMembership
open ActualCoupledHistories SourceSelectedCompactOccupation FullHistoryPrimeOccupation
open FullPathCompactSelection CompactPrefixOccurrence PrimeFamilyOccupation
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem retained_compact_event (R : ℝ) (hR : 3 ≤ R) (d : ℝ) (hd : 0 < d) :
    ∃ C w₀ : ℝ, 0 < C ∧ 1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,
      ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B →
      let S := (Real.log B)^2
      let N := LowStateHorizon.sourceHorizon S B
      ∀ mesh : ℝ, ∀ E : Set (List ℕ),
        (∀ ps ∈ retainedPrefixes w ell S start, ps ∈ E → (terminal w start ps).gap ≤ R) →
        ENNReal.ofReal (B^2*(∑ ps ∈ (retainedPrefixes w ell S start).filter (· ∈ E),prefixWeight ps)) ≤
          ENNReal.ofReal C * fullSourceLaw w ell S start hs mesh N {h | occurs E N h} := by
  obtain ⟨C,W,hC,hW,hsel⟩ := source_selected_compact R hR d hd
  obtain ⟨W₁,hW₁⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  refine ⟨C,max W (max normalizationThreshold W₁),hC,hW.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
  dsimp only
  intro mesh E hcompact
  have hwW : W ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hlogw : d^2 ≤ Real.log w := hW₁ w
    ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := UniformBudgetRate.source_scale_bound hlogw hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; exact mul_pos hB (valid_pos hs)
  have hsize : start.gap ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  have hnode : ∀ h : History w ell ((Real.log B)^2) start,h.primes ∈ E → h.node.gap ≤ R := by
    intro h hh
    exact hcompact h.primes ((mem_retainedPrefixes hw1 start h.primes).mpr h.admissible) hh
  have hsum : (∑ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,prefixWeight ps*listSelection E ps) =
      ∑ ps ∈ (retainedPrefixes w ell ((Real.log B)^2) start).filter (· ∈ E),prefixWeight ps := by
    simp [Finset.sum_filter,listSelection,mul_ite]
  rw [← hsum,← finite_family_full_history hnorm hell hS0 hscale.1 hr hs hsS hB hsize
    mesh (listSelection E) (fun ps _ => listSelection_nonneg E ps)]
  calc
    _ ≤ ∫⁻ h,{h | occurs E (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) h}.indicator
        (fullCompactReward R w B start (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)) h
        ∂sourceHistoryLaw hnorm hell hS0 hscale.1 hr hs hsS mesh
          (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) :=
      lintegral_mono (full_selected_le_occurrence E hnode _)
    _ ≤ _ := by
      have hh := hsel w hwW ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
        mesh (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) _ (occurs_measurable E _)
      exact hh

end NumberTheoryLean.RetainedCompactEvent

end

end Erdos970

end OAI
