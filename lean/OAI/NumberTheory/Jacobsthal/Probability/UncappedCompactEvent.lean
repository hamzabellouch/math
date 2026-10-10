import OAI.NumberTheory.Jacobsthal.Partitions.CompactSelectedPartition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UncappedCompactEvent

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open PrimeBinMembership
open ActualCoupledHistories SourceSelectedCompactOccupation FullHistoryPrimeOccupation
open CompactPrefixOccurrence PrimeFamilyOccupation ActualPrimeHigh CompactSelectedPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail RetainedCompactEvent

attribute [local instance] Classical.propDecidable

theorem uncapped_compact_event (R : ℝ) (hR : 3 ≤ R) (d : ℝ) (hd : 0 < d) :
    ∃ C w₀ : ℝ, 0 < C ∧ 1 < w₀ ∧ ∀ A : ℝ, ∃ B₀ : ℝ, 0 < B₀ ∧
      ∀ B w : ℝ, B₀ ≤ B → w₀ ≤ w → ∀ ell : ℝ, ∀ start : Node,
      ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B →
      let S := (Real.log B)^2
      let N := LowStateHorizon.sourceHorizon S B
      ∀ mesh : ℝ, ∀ E : Set (List ℕ),
        (∀ ps ∈ uncappedPrefixes w ell start, ps ∈ E → (terminal w start ps).gap ≤ R) →
        (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
          (C/B^2) * (fullSourceLaw w ell S start hs mesh N {h | occurs E N h}).toReal + B^(-A) := by
  obtain ⟨C,W,hC,hW,hret⟩ := retained_compact_event R hR d hd
  obtain ⟨WH,hWH,hhigh⟩ := uncapped_low_gap_high_removal
  let w₀ := max W (max WH (max normalizationThreshold (Real.exp (d^2))))
  refine ⟨C,w₀,hC,hW.trans_le (le_max_left _ _),?_⟩
  intro A
  obtain ⟨BH,hBH⟩ := eventually_atTop.mp (hhigh R (by linarith) A)
  refine ⟨max (Real.exp 2) BH,(Real.exp_pos 2).trans_le (le_max_left _ _),?_⟩
  intro B w hB₀ hw ell start hs hell hellB hcomp hi h199 h23 hc hcut
  dsimp only
  intro mesh E hcompact
  have heB : Real.exp 2 ≤ B := (le_max_left _ _).trans hB₀
  have hB : 0 < B := (Real.exp_pos 2).trans_le heB
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr heB
  have hwW : W ≤ w := (le_max_left _ _).trans hw
  have hwH : WH ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw
  have hexp : Real.exp (d^2) ≤ w :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  have hlogw : d^2 ≤ Real.log w := (Real.le_log_iff_exp_le (by linarith : 0 < w)).mpr hexp
  have hscale := UniformBudgetRate.source_scale_bound hlogw hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; exact mul_pos hB (valid_pos hs)
  have hcompactRet : ∀ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,
      ps ∈ E → (terminal w start ps).gap ≤ R := by
    intro ps hp hE
    rw [retained_eq_nonhigh hw1 hsS] at hp
    exact hcompact ps (Finset.mem_filter.mp hp).1 hE
  have hretain := hret w hwW ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
    mesh E hcompactRet
  let μ := fullSourceLaw w ell ((Real.log B)^2) start hs mesh
    (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)
  let U : Set (FiniteHistoryTransport.Hist
      (FlagState (JointState w ell ((Real.log B)^2) start))
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)) :=
    {h | occurs E (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) h}
  have : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [fullSourceLaw_eq hnorm hell hS0 hscale.1 hr hs hsS]
    infer_instance
  have hm : 0 ≤ ∑ ps ∈ (retainedPrefixes w ell ((Real.log B)^2) start).filter (· ∈ E),prefixWeight ps :=
    Finset.sum_nonneg (fun ps _ => prefixWeight_nonneg ps)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ U)) hretain
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg B) hm),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC.le] at hreal
  have hretReal : (∑ ps ∈ (retainedPrefixes w ell ((Real.log B)^2) start).filter (· ∈ E),prefixWeight ps) ≤
      (C/B^2)*(μ U).toReal := by
    calc
      _ ≤ (C*(μ U).toReal)/B^2 := (le_div_iff₀ (sq_pos_of_pos hB)).mpr (by nlinarith only [hreal])
      _ = _ := by ring
  have hhighB := hBH B ((le_max_right _ _).trans hB₀) w hwH ell hell hellB start hcut hr hs hc
  exact (selected_uncapped_le hw1 hsS E hcompact).trans (add_le_add hretReal hhighB)

end NumberTheoryLean.UncappedCompactEvent

end

end Erdos970

end OAI
