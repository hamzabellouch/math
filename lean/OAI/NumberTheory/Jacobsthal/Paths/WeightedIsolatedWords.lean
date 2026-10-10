import OAI.NumberTheory.Jacobsthal.Probability.SourceIsolatedProbability
import OAI.NumberTheory.Jacobsthal.Probability.UncappedCompactEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WeightedIsolatedWords
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership ActualPrimeHigh
open SourceSelectedCompactOccupation CompactPrefixOccurrence NonisolatedWordOccurrence
open SourceIsolatedProbability UncappedCompactEvent ExponentialMesh
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem weighted_nonisolated_mass (R : ℝ) (hR : 3 ≤ R) (D : ℝ) (hD : 0 < D)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (eps : ℝ) (heps : 0 < eps) :
    ∃ alpha B₀ w₀ : ℝ,0 < alpha ∧ alpha ≤ theta ∧ 0 < B₀ ∧ 1 < w₀ ∧
    ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → ∀ ell : ℝ,∀ start : Node,
      ∀ _hs : Valid start.side start.ratio,1 ≤ ell → ell ≤ B → Real.log B ≤ D*Real.log w →
      start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 → Consistent start → start.cutoff=B →
      w^start.cutoff=top → ∀ E : Set (List ℕ),
      (∀ ps ∈ uncappedPrefixes w ell start,ps ∈ E → (terminal w start ps).gap ≤ R ∧
        noIsolatedWord hw htop hxi B alpha (4*theta) ps) →
      B^2*(∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤ eps := by
  obtain ⟨cR,WC,hcR,hWC,hCompact⟩ := uncapped_compact_event R hR D hD
  let eta := eps/(2*cR)
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨κ,alpha,BP,WP,_hκ,ha,hath,hBP,hWP,hP⟩ := source_nonisolated_probability D theta eta hD htheta htheta1 heta
  obtain ⟨BC,hBC,hC⟩ := hCompact (3:ℝ)
  refine ⟨alpha,max BC (max BP (max (Real.exp 2) (max (R/theta) (2/eps)))),max WC WP,
    ha,hath,hBC.trans_le (le_max_left _ _),hWC.trans_le (le_max_left _ _),?_⟩
  intro B w hBB hw₀ hw top htop xi hxi hxi1 ell start hs hell hellB hcomp hi h199 h23 hc hcut hcap E hE
  have hB : 0 < B := hBC.trans_le ((le_max_left _ _).trans hBB)
  have hBC' : BC ≤ B := (le_max_left _ _).trans hBB
  have hBP' : BP ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hBB
  have hExpB : Real.exp 2 ≤ B := (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hBB
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr hExpB
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hRB : R/theta ≤ B := (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))).trans hBB
  have hRtheta : R ≤ theta*B := by have hh := (div_le_iff₀ htheta).mp hRB; nlinarith
  have hHist : ∀ p : History w ell ((Real.log B)^2) start,p.primes ∈ E → p.node.gap ≤ theta*B ∧
      noIsolatedWord hw htop hxi B alpha (4*theta) p.primes := by
    intro p hp
    have hu : p.primes ∈ uncappedPrefixes w ell start :=
      (mem_uncappedPrefixes hw start p.primes).mpr
        ((uncapped_iff_exists_ceiling w ell start p.primes).mpr ⟨(Real.log B)^2,hsS,p.admissible⟩)
    exact ⟨(hE p.primes hu hp).1.trans hRtheta,(hE p.primes hu hp).2⟩
  have hProb := hP B w hBP' ((le_max_right _ _).trans hw₀) hw top htop xi hxi hxi1 ell start hs
    hell hcomp hi h199 h23 hc hcut hcap E hHist
  have hpr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hProb
  rw [ENNReal.toReal_ofReal heta.le] at hpr
  have hMass := hC B w hBC' ((le_max_left _ _).trans hw₀) ell start hs hell hellB hcomp
    hi h199 h23 hc hcut (mesh κ w) E (fun ps hp hsel => (hE ps hp hsel).1)
  have hMass' : (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
      (cR/B^2)*eta+B^(-(3:ℝ)) :=
    hMass.trans (add_le_add (mul_le_mul_of_nonneg_left hpr (show 0 ≤ cR/B^2 by positivity)) le_rfl)
  have hlarge : 2/eps ≤ B := (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))).trans hBB
  have hinv : 1/B ≤ eps/2 := by
    have hh := (div_le_iff₀ heps).mp hlarge
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hcEta : cR*eta=eps/2 := by dsimp [eta]; field_simp [hcR.ne']
  have hpow : B^(-(3:ℝ))=(B^3)⁻¹ := by rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
  calc
    _ ≤ B^2*((cR/B^2)*eta+B^(-(3:ℝ))) := mul_le_mul_of_nonneg_left hMass' (sq_nonneg B)
    _ = cR*eta+1/B := by rw [hpow]; field_simp [hB.ne']
    _ ≤ eps := by rw [hcEta]; linarith
end NumberTheoryLean.WeightedIsolatedWords


end Erdos970

end OAI
