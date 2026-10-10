import OAI.NumberTheory.Jacobsthal.Estimates.RepeatedSelectedOccurrence
import OAI.NumberTheory.Jacobsthal.Estimates.SourceRepeatedRates
import OAI.NumberTheory.Jacobsthal.Probability.UncappedCompactEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WeightedRepeatedWords
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership ActualPrimeHigh
open SourceSelectedCompactOccupation CompactPrefixOccurrence RepeatedSelectedOccurrence RepeatedWordEvents
open SourceRepeatedRates UncappedCompactEvent ExponentialMesh
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem weighted_repeated_word_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D)
    (L : ℝ) (hL : 0 ≤ L) (eps : ℝ) (heps : 0 < eps) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
    ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ top : ℝ,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → ∃ hw : 1 < w,
      ∀ ell : ℝ,∀ start : Node,∀ _hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ D*Real.log w →
      start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 → Consistent start → start.cutoff=B →
      w^start.cutoff=top → ∀ E : Set (List ℕ),
      (∀ ps ∈ uncappedPrefixes w ell start,ps ∈ E →
        (terminal w start ps).gap ≤ R ∧ (searchRepeatedWord hw htop hxi ps ∨
          compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L start ps)) →
      B^2*(∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤ eps := by
  obtain ⟨cR,WC,hcR,hWC,hCompact⟩ := uncapped_compact_event R hR D hD
  obtain ⟨κ,hκ,hProb⟩ := source_repeated_pair_probabilities
  let eta := eps/(4*cR)
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨WP,hWP,hP⟩ := hProb κ hκ le_rfl D L eta hD hL heta
  obtain ⟨BC,hBC,hCbound⟩ := hCompact (3:ℝ)
  let w₀ := max WC (max WP (max normalizationThreshold (Real.exp (D^2))))
  refine ⟨max BC (max (Real.exp 2) (2/eps)),w₀,hBC.trans_le (le_max_left _ _),
    hWC.trans_le (le_max_left _ _),?_⟩
  intro B w hBB hw₀ top htop xi hxi hxi1
  have hB : 0 < B := hBC.trans_le ((le_max_left _ _).trans hBB)
  have hExpB : Real.exp 2 ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hBB
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr hExpB
  have hwC : WC ≤ w := (le_max_left _ _).trans hw₀
  have hwP : WP ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw₀
  have hw : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  refine ⟨hw,?_⟩
  intro ell start hs hell hellB hcomp hi h199 h23 hc hcut hcap E hE
  have hExpW : Real.exp (D^2) ≤ w :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hw₀
  have hlogw : D^2 ≤ Real.log w := (Real.le_log_iff_exp_le (zero_lt_one.trans hw)).mpr hExpW
  have hscale := UniformBudgetRate.source_scale_bound hlogw hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hrnode := SourceNodeCoordinates.source_node_bounds hB start hi h199 h23 hc hcut
  have hHist : ∀ p : History w ell ((Real.log B)^2) start,p.primes ∈ E →
      searchRepeatedWord hw htop hxi p.primes ∨ compactAdjacentWord w (label (zero_lt_one.trans hw) htop hxi) L start p.primes := by
    intro p hp
    have hu : p.primes ∈ uncappedPrefixes w ell start :=
      (mem_uncappedPrefixes hw start p.primes).mpr
        ((uncapped_iff_exists_ceiling w ell start p.primes).mpr ⟨(Real.log B)^2,hsS,p.admissible⟩)
    exact (hE p.primes hu hp).2
  have hOcc := selected_repetition_probability hnorm hell hS0 hscale.1 hrnode.2.1 hs hsS
    hw htop hxi hcap L (mesh κ w) (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) E hHist
  obtain ⟨hw',hProbs⟩ := hP w hwP
  have hp := hProbs top htop ell B start hs hell hB hlogB hcomp hrnode.2.1 h23 hc hrnode.2.2.2 hcap xi hxi hxi1
  have hProbability : fullSourceLaw w ell ((Real.log B)^2) start hs (mesh κ w)
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) {h | occurs E _ h} ≤ ENNReal.ofReal (2*eta) := by
    have hh := hOcc.trans (add_le_add hp.1 hp.2)
    rw [← ENNReal.ofReal_add heta.le heta.le] at hh
    simpa only [two_mul] using hh
  have hpr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hProbability
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*eta)] at hpr
  have hMass := hCbound B w ((le_max_left _ _).trans hBB) hwC ell start hs hell hellB hcomp
    hi h199 h23 hc hcut (mesh κ w) E (fun ps hp hsel => (hE ps hp hsel).1)
  have hMass' : (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
      (cR/B^2)*(2*eta)+B^(-(3:ℝ)) :=
    hMass.trans (add_le_add (mul_le_mul_of_nonneg_left hpr (show 0 ≤ cR/B^2 by positivity)) le_rfl)
  have hlarge : 2/eps ≤ B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hBB
  have hinv : 1/B ≤ eps/2 := by
    have hh := (div_le_iff₀ heps).mp hlarge
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hcEta : cR*(2*eta)=eps/2 := by dsimp [eta]; field_simp [hcR.ne']; ring
  have hpow : B^(-(3:ℝ))=(B^3)⁻¹ := by rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
  calc
    _ ≤ B^2*((cR/B^2)*(2*eta)+B^(-(3:ℝ))) := mul_le_mul_of_nonneg_left hMass' (sq_nonneg B)
    _ = cR*(2*eta)+1/B := by rw [hpow]; field_simp [hB.ne']
    _ ≤ eps := by rw [hcEta]; linarith
end NumberTheoryLean.WeightedRepeatedWords


end Erdos970

end OAI
