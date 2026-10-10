import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalSourceScale
import OAI.NumberTheory.Jacobsthal.Probability.MarkedOccurrenceProbability
import OAI.NumberTheory.Jacobsthal.Probability.UncappedCompactEvent

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MovingPrimeWindowProbability

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories FlaggedSourceStart FiniteHistoryTransport PriorPrimeWindow
open CompactPrefixOccurrence MarkedOccurrenceProbability MarkedSourceSmallness ExponentialMesh
open SourceSelectedCompactOccupation SourceCouplingRate
open Erdos970Dependency.MarkedVisits

theorem source_missing_window_probability : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ R d eps : ℝ, 0 < d → 0 < eps →
      ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ w₀ : ℝ, 1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ, ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B → w ≤ start.gap →
      let S := (Real.log B)^2
      let N := LowStateHorizon.sourceHorizon S B
      ∀ E : Set (List ℕ),
        (∀ p : History w ell S start,p.primes ∈ E → p.node.gap ≤ R ∧
          ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start p.primes) →
        fullSourceLaw w ell S start hs (mesh κ w) N {h | occurs E N h} ≤ ENNReal.ofReal eps := by
  obtain ⟨κ₀,hκ₀,hCouple⟩ := source_coupling_rate
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle R d eps hd heps
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ hκle d hd
  obtain ⟨rho,hrho,hMoving⟩ := moving_canonical_missing_visit (show 0 < eps/2 by positivity)
  refine ⟨rho,hrho,?_⟩
  intro K hK
  have hA : 0 ≤ 5*d^3 := by positivity
  have hEvents := (hMoving K hK).and ((mark_mesh_smallness hA hκ).and
    ((moving_compact_gap_small ((11/10)*R) hK).and
      (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
        (eventually_le_nhds (show 0 < eps/2 by positivity))).and
          (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2))))))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨max WC (max normalizationThreshold W),hWC.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hi h199 h23 hc hcut hgap
  dsimp only
  intro E hE
  have hwC : WC ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hw3 : 3 ≤ w := hwe.1.1
  have hr : 0 < start.gap := (by linarith : 0 < w).trans_le hgap
  have hscale := UniformBudgetRate.source_scale_bound hwe.2.2.2.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hsize : start.gap ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hf := (hC w hwC ell B start hs hell hB hlogB hcomp hr h23 hc hsize).1
    (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) le_rfl |>.1
  have hfailSmall : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using hwe.2.2.2.1
  have hf' : sourceLaw hnorm hell hS0 hscale.1 hr hs hsS (mesh κ w)
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) PersistentFailureFlag.failed ≤ ENNReal.ofReal (eps/2) :=
    hf.trans (ENNReal.ofReal_le_ofReal hfailSmall)
  let s : TransitionKernels.EvenState := ⟨start.ratio,by simpa only [hi,Valid] using hs⟩
  have htyped : typedState start.side start.ratio hs = Sum.inl s := by
    have aux : ∀ (i : Side) (t : ℝ) (ht : Valid i t) (hi : i = .even),
        typedState i t ht = Sum.inl (⟨t,by simpa only [hi,Valid] using ht⟩ : TransitionKernels.EvenState) := by
      intro i t ht hi
      subst i
      rfl
    exact aux start.side start.ratio hs hi
  have hcanon := hwe.1.2 start.gap hgap s h199 h23
    (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)
  have hb₀ : 0 < K*(Real.log w)^2 := by
    have hL : 0 < Real.log w := Real.log_pos (by linarith)
    positivity
  have hb₁ : 0 < rho*K*(Real.log w)^2 := by
    have : 0 < rho := by linarith
    have hL : 0 < Real.log w := Real.log_pos (by linarith)
    positivity
  have hProb := missing_occurrence_probability hnorm hell hS0 hscale.1 hr hs hsS hc
    hb₀ hb₁ hwe.2.2.1 (mesh_pos κ w) hwe.2.1.1 _ (hwe.2.1.2 _ hscale.2) E hE
  rw [htyped] at hProb
  calc
    _ ≤ _ := hProb
    _ ≤ ENNReal.ofReal (eps/2)+ENNReal.ofReal (eps/2) := add_le_add hf' hcanon
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2) (by positivity : 0 ≤ eps/2)]; congr 1; ring

end NumberTheoryLean.MovingPrimeWindowProbability

end

section

namespace NumberTheoryLean.WeightedMissingPrimeWindow

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership ActualPrimeHigh
open PriorPrimeWindow MovingPrimeWindowProbability UncappedCompactEvent
open SourceSelectedCompactOccupation CompactPrefixOccurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

attribute [local instance] Classical.propDecidable

theorem weighted_missing_prime_window : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ R d eps : ℝ, 3 ≤ R → 0 < d → 0 < eps →
      ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ B₀ w₀ : ℝ, 0 < B₀ ∧ 1 < w₀ ∧
      ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ ell : ℝ, ∀ start : Node,
      ∀ _hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B → w ≤ start.gap →
      ∀ E : Set (List ℕ),
        (∀ ps ∈ uncappedPrefixes w ell start, ps ∈ E → (terminal w start ps).gap ≤ R ∧
          ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start ps) →
        B^2*(∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤ eps := by
  obtain ⟨κ₀,hκ₀,hProb⟩ := source_missing_window_probability
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle R d eps hR hd heps
  obtain ⟨C,WC,hC,hWC,hCompact⟩ := uncapped_compact_event R hR d hd
  let delta := eps/(2*C)
  have hdelt : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨rho,hrho,hMoving⟩ := hProb κ hκ hκle R d delta hd hdelt
  refine ⟨rho,hrho,?_⟩
  intro K hK
  obtain ⟨WP,hWP,hP⟩ := hMoving K hK
  obtain ⟨BC,hBC,hCbound⟩ := hCompact (3:ℝ)
  refine ⟨max BC (max (Real.exp 2) (2/eps)),max WC WP,
    hBC.trans_le (le_max_left _ _),hWC.trans_le (le_max_left _ _),?_⟩
  intro B w hBB hw ell start hs hell hellB hcomp hi h199 h23 hc hcut hgap E hE
  have hB : 0 < B := hBC.trans_le ((le_max_left _ _).trans hBB)
  have heB : Real.exp 2 ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hBB
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr heB
  have hwC : WC ≤ w := (le_max_left _ _).trans hw
  have hwP : WP ≤ w := (le_max_right _ _).trans hw
  have hw1 : 1 < w := hWC.trans_le hwC
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hHist : ∀ p : History w ell ((Real.log B)^2) start,p.primes ∈ E → p.node.gap ≤ R ∧
      ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start p.primes := by
    intro p hp
    have hUn : p.primes ∈ uncappedPrefixes w ell start :=
      (mem_uncappedPrefixes hw1 start p.primes).mpr
        ((uncapped_iff_exists_ceiling w ell start p.primes).mpr ⟨(Real.log B)^2,hsS,p.admissible⟩)
    exact hE p.primes hUn hp
  have hProbability := hP w hwP ell B start hs hell hB hlogB hcomp hi h199 h23 hc hcut hgap E hHist
  have hpReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hProbability
  rw [ENNReal.toReal_ofReal hdelt.le] at hpReal
  have hMass := hCbound B w ((le_max_left _ _).trans hBB) hwC ell start hs hell hellB hcomp
    hi h199 h23 hc hcut (ExponentialMesh.mesh κ w) E (fun ps hp hsel => (hE ps hp hsel).1)
  have hMass' : (∑ ps ∈ (uncappedPrefixes w ell start).filter (· ∈ E),prefixWeight ps) ≤
      (C/B^2)*delta+B^(-(3:ℝ)) :=
    hMass.trans (add_le_add (mul_le_mul_of_nonneg_left hpReal (by positivity)) le_rfl)
  have hlarge : 2/eps ≤ B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hBB
  have hinv : 1/B ≤ eps/2 := by
    have hh := (div_le_iff₀ heps).mp hlarge
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hCD : C*delta = eps/2 := by dsimp [delta]; field_simp [hC.ne']
  have hpow : B^(-(3:ℝ)) = (B^3)⁻¹ := by rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
  calc
    _ ≤ B^2*((C/B^2)*delta+B^(-(3:ℝ))) := mul_le_mul_of_nonneg_left hMass' (sq_nonneg B)
    _ = C*delta+1/B := by rw [hpow]; field_simp [hB.ne']
    _ ≤ eps := by rw [hCD]; linarith

end NumberTheoryLean.WeightedMissingPrimeWindow

end

section

namespace NumberTheoryLean.MissingWindowPrimeMass

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh PriorPrimeWindow
open ErdosPrimeInputs.PrimePrefixMass WeightedMissingPrimeWindow

noncomputable def missingWindowPrefixes (w ell R b₀ b₁ : ℝ) (start : Node) : Finset (List ℕ) := by
  classical
  exact (uncappedPrefixes w ell start).filter fun ps =>
    (terminal w start ps).gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start ps

theorem moving_missing_prefix_mass (R d eps : ℝ) (hR : 3 ≤ R) (hd : 0 < d) (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ B₀ w₀ : ℝ, 0 < B₀ ∧ 1 < w₀ ∧
      ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ ell : ℝ, ∀ start : Node,
      ∀ _hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B → w ≤ start.gap →
      B^2*(∑ ps ∈ missingWindowPrefixes w ell R (K*(Real.log w)^2)
        (rho*K*(Real.log w)^2) start,prefixWeight ps) ≤ eps := by
  classical
  obtain ⟨κ₀,hκ₀,hbound⟩ := weighted_missing_prime_window
  obtain ⟨rho,hrho,hK⟩ := hbound κ₀ hκ₀ le_rfl R d eps hR hd heps
  refine ⟨rho,hrho,?_⟩
  intro K hKpos
  obtain ⟨B₀,w₀,hB₀,hw₀,h⟩ := hK K hKpos
  refine ⟨B₀,w₀,hB₀,hw₀,?_⟩
  intro B w hB hw ell start hs hell hellB hcomp hi h199 h23 hc hcut hgap
  let E : Set (List ℕ) := {ps | (terminal w start ps).gap ≤ R ∧
    ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start ps}
  have hh := h B w hB hw ell start hs hell hellB hcomp hi h199 h23 hc hcut hgap E
    (fun _ _ hmem => hmem)
  have hset : missingWindowPrefixes w ell R (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start =
      (uncappedPrefixes w ell start).filter (fun ps => ps ∈ E) := by
    ext ps
    simp only [missingWindowPrefixes,Finset.mem_filter,E,Set.mem_ofPred_eq]
  rw [hset]
  convert! hh using 1
  congr 1
  apply Finset.sum_congr
  · ext ps
    simp only [Finset.mem_filter]
  · intro ps _
    rfl

end NumberTheoryLean.MissingWindowPrimeMass

end

section

namespace NumberTheoryLean.PaperMissingPrimeWindow

open _root_.Set _root_.Filter _root_.Finset
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open JacobsthalSourceScale MissingWindowPrimeMass ErdosPrimeInputs.PrimePrefixMass

theorem sourceW_le_sourceB_eventually : ∀ᶠ L : ℝ in atTop,sourceW L ≤ sourceB L := by
  filter_upwards [sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hW hL hlog
  have hLp : 0 < L := by linarith
  have hlogW : 0 < Real.log (sourceW L) := Real.log_pos hW.1
  have hd : Real.log (sourceW L) ≤ (Real.log L)^2 := by
    have hh := Real.log_le_log (by linarith [hW.1] : 0 < sourceW L) hW.2.2
    nlinarith
  exact div_le_div_of_nonneg_left hLp.le hlogW hd

theorem paper_missing_prime_window_mass (R eps : ℝ) (hR : 3 ≤ R) (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ,L₀ ≤ L → ∀ ell : ℝ,1 ≤ ell → ell ≤ 2 → ∀ start : Node,
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = sourceB L →
      (sourceB L)^2*(∑ ps ∈ missingWindowPrefixes (sourceW L) ell R
        (K*(Real.log (sourceW L))^2) (rho*K*(Real.log (sourceW L))^2) start,prefixWeight ps) ≤ eps := by
  obtain ⟨rho,hrho,hK⟩ := moving_missing_prefix_mass R 2 eps hR (by norm_num) heps
  refine ⟨rho,hrho,?_⟩
  intro K hKpos
  obtain ⟨B₀,w₀,_hB₀,_hw₀,h⟩ := hK K hKpos
  have he : ∀ᶠ L : ℝ in atTop,∀ ell : ℝ,1 ≤ ell → ell ≤ 2 → ∀ start : Node,
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = sourceB L →
      (sourceB L)^2*(∑ ps ∈ missingWindowPrefixes (sourceW L) ell R
        (K*(Real.log (sourceW L))^2) (rho*K*(Real.log (sourceW L))^2) start,prefixWeight ps) ≤ eps := by
    filter_upwards [source_scale_eventually,sourceW_le_sourceB_eventually,
      sourceB_tendsto.eventually (eventually_ge_atTop (max B₀ 2)),
      sourceW_tendsto.eventually (eventually_ge_atTop w₀)] with L hscale hWB hB hw
    intro ell hell hell2 start hi h199 h23 hc hcut
    have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
    have heq : start.gap = sourceB L*start.ratio := by
      have hh : start.cutoff = start.gap/start.ratio := hc
      rw [hcut] at hh
      exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
    have hgap : sourceW L ≤ start.gap := by
      have hBg : sourceB L ≤ start.gap := by rw [heq]; nlinarith [hscale.2.1]
      exact hWB.trans hBg
    exact h (sourceB L) (sourceW L) ((le_max_left _ _).trans hB) hw ell start hs hell
      (hell2.trans ((le_max_right _ _).trans hB)) hscale.2.2.2.2 hi h199 h23 hc hcut hgap
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp he
  refine ⟨max 1 L₁,by have hh := le_max_left (1:ℝ) L₁; linarith,?_⟩
  intro L hL
  exact hL₁ L ((le_max_right _ _).trans hL)

end NumberTheoryLean.PaperMissingPrimeWindow

end

end Erdos970

end OAI
