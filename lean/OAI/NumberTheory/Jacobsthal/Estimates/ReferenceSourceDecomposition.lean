import OAI.NumberTheory.Jacobsthal.Paths.ReferenceHistoryAdmission
import OAI.NumberTheory.Jacobsthal.Sieve.UniformExponentialOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualBoundaryDomain

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ActualPrimeHigh SourceNodeCoordinates
open ErdosPrimeInputs.HarmonicPrimeMeasure

def BoundaryDomain : Side → ℝ → Prop
  | .even, r => 4 ≤ r
  | .odd, r => 2 ≤ r

theorem child_boundary_domain {w ell : ℝ} {z : Node} {p : ℕ} (hell : 2 ≤ ell)
    (heven : z.side=.even → 2 ≤ z.ratio) (hp : p ∈ uncappedChildren w ell z) :
    BoundaryDomain (step w z p).side (step w z p).gap ∧
      ((step w z p).side=.even → 2 ≤ (step w z p).ratio) := by
  obtain ⟨_hprime,hlo,_hcap,hmin⟩ := Finset.mem_filter.mp hp
  have hx : 2 < primeExponent w p := hell.trans_lt hlo
  have he : (step w z p).ratio*primeExponent w p=(step w z p).gap := by
    dsimp only [step,childRatio]
    field_simp [show primeExponent w p ≠ 0 by linarith]
  cases hi : z.side with
  | even =>
    have hs := heven hi
    have hm : 1 ≤ (step w z p).ratio := by
      change minRatio z.side z.ratio ≤ childRatio w z.gap p at hmin
      rw [hi] at hmin
      change z.ratio-1 ≤ (step w z p).ratio at hmin
      linarith
    have hside : (step w z p).side=.odd := by simp [step,hi,Side.flip]
    rw [hside]
    refine ⟨?_,by intro h; cases h⟩
    change 2 ≤ (step w z p).gap
    nlinarith
  | odd =>
    have hm : 2 ≤ (step w z p).ratio := by
      change minRatio z.side z.ratio ≤ childRatio w z.gap p at hmin
      rw [hi] at hmin
      exact (le_max_left _ _).trans hmin
    have hside : (step w z p).side=.even := by simp [step,hi,Side.flip]
    rw [hside]
    exact ⟨by change 4 ≤ (step w z p).gap; nlinarith,fun _ => hm⟩

theorem boundary_domain_preserved {w ell : ℝ} {z : Node} {ps : List ℕ} (hell : 2 ≤ ell)
    (hdom : BoundaryDomain z.side z.gap) (heven : z.side=.even → 2 ≤ z.ratio)
    (hp : uncappedAllowed w ell z ps) :
    BoundaryDomain (terminal w z ps).side (terminal w z ps).gap := by
  induction ps generalizing z with
  | nil => exact hdom
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    obtain ⟨hd,he⟩ := child_boundary_domain hell heven hc
    exact ih hd he ht

theorem source_boundary_domain {B w ell : ℝ} (hB : 4 ≤ B) (hell : 2 ≤ ell)
    (start : Node) (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hc : Consistent start) (hcut : start.cutoff=B) {ps : List ℕ}
    (hp : uncappedAllowed w ell start ps) :
    BoundaryDomain (terminal w start ps).side (terminal w start ps).gap := by
  obtain ⟨hs,_hr,hBgap,_hsize⟩ := source_node_bounds (by linarith : 0 < B) start hi h199 h23 hc hcut
  have hgap := node_gap_eq hs hc hcut
  cases ps with
  | nil => simpa only [terminal_nil,hi,BoundaryDomain] using hB.trans hBgap
  | cons p ps =>
    obtain ⟨hchild,htail⟩ := hp
    obtain ⟨_hprime,_hlo,hcap,_hmin⟩ := Finset.mem_filter.mp hchild
    have hxp : primeExponent w p ≤ B := by
      change capGuard start.closed start.cutoff (primeExponent w p) at hcap
      rw [hcut] at hcap
      cases hcl : start.closed with
      | false =>
        have h : primeExponent w p < B := by simpa [capGuard,hcl] using hcap
        exact h.le
      | true => simpa only [capGuard,hcl,ite_true] using hcap
    have hside : (step w start p).side=.odd := by simp [step,hi,Side.flip]
    have hdom : BoundaryDomain (step w start p).side (step w start p).gap := by
      rw [hside]
      change 2 ≤ start.gap-primeExponent w p
      nlinarith
    simpa only [terminal_cons] using boundary_domain_preserved (z := step w start p) hell hdom (by rw [hside]; intro h; cases h) htail

theorem boundary_gap_ge_two {i : Side} {r : ℝ} (h : BoundaryDomain i r) : 2 ≤ r := by
  cases i <;> simp only [BoundaryDomain] at h <;> linarith

end NumberTheoryLean.ActualBoundaryDomain

end

section

namespace NumberTheoryLean.UniformBoundaryCorrection

attribute [local instance] Classical.propDecidable

open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open BoundaryAnomaly UniformExponentialOccupation ActualBoundaryDomain
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def boundaryCorrection (w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*((-1:ℝ)^ps.length*
    anomaly w (terminal w start ps).side (terminal w start ps).gap)

theorem uniform_boundary_correction (ell d : ℝ) (hell : 2 ≤ ell) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*|boundaryCorrection w ell start| ≤ C := by
  obtain ⟨A,c,wA,hA,hc,hwA,hAnomaly⟩ := actual_boundary_anomaly_exponential
  obtain ⟨CP,BP,wP,hCP,hBP,hwP,hOccupation⟩ :=
    uniform_signed_exponential_rewards ell c d (by linarith) hc hd
  refine ⟨A*CP,max BP 4,max wP wA,mul_pos hA hCP,hBP.trans_le (le_max_left _ _),
    hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBP' : BP ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hwP' : wP ≤ w := (le_max_left _ _).trans hw
  have hwA' : wA ≤ w := (le_max_right _ _).trans hw
  apply hOccupation B w hBP' hwP' hcomp start hi h199 h23 hcons hcut A hA.le
    (fun ps => (-1:ℝ)^ps.length*anomaly w (terminal w start ps).side (terminal w start ps).gap)
  intro ps hp
  have hpA : uncappedAllowed w ell start ps := (Finset.mem_filter.mp hp).2
  have hdom := source_boundary_domain hB4 hell start hi h199 h23 hcons hcut hpA
  have hr2 := boundary_gap_ge_two hdom
  rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,positiveGapEnvelope,ite_eq_left hr2]
  exact hAnomaly w hwA' _ hr2 _

theorem uniform_boundary_correction_div (ell d : ℝ) (hell : 2 ≤ ell) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → |boundaryCorrection w ell start| ≤ C/B^2 := by
  obtain ⟨C,B₀,w₀,hC,hB₀,hw₀,h⟩ := uniform_boundary_correction ell d hell hd
  refine ⟨C,B₀,w₀,hC,hB₀,hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  apply (le_div_iff₀ (sq_pos_of_pos (hB₀.trans_le hB))).mpr
  simpa only [mul_comm] using h B w hB hw hcomp start hi h199 h23 hcons hcut

end NumberTheoryLean.UniformBoundaryCorrection

end

section

namespace NumberTheoryLean.ReferenceSourceDecomposition

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh
open ReferenceAdmission ReferencePruning ReferenceWeightedRecurrence ReferenceForestTelescoping ReferenceCutoffRecurrence
open ReferenceSourcePrimeSets ReferenceEulerRecurrence ReferenceHistoryAdmission ReferenceLocalResidual
open BoundaryAnomaly UniformBoundaryCorrection
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def sourceReference (w : ℝ) (z : Node) : ℝ :=
  referencePolynomial w (sourcePrimes w z.cutoff z.closed) z.side z.gap

noncomputable def residualCorrection (w : ℝ) (z : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w 2 z,prefixWeight ps*((-1:ℝ)^ps.length*sourceResidual w (terminal w z ps))

theorem suffix_highPrimes {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) {ps : List ℕ} (hp : uncappedAllowed w 2 z ps) :
    suffixPrimes (highPrimes w z.cutoff z.closed) ps=
      highPrimes w (terminal w z ps).cutoff (terminal w z ps).closed := by
  induction ps generalizing z with
  | nil => simp only [suffixPrimes_nil,terminal_nil]
  | cons p ps ih =>
    obtain ⟨hchild,htail⟩ := hp
    have hpH := ((uncapped_child_iff hw hs hz p).mp hchild).1
    have hpS : p ∈ sourcePrimes w z.cutoff z.closed := (Finset.mem_filter.mp hpH).1
    obtain ⟨hvs,hrs,hzs⟩ := uncapped_child_invariants hs hr hchild
    rw [suffixPrimes_cons,terminal_cons,← highPrimes_at_selected hw z.closed hpS]
    exact ih (z := step w z p) hvs hrs hzs htail

theorem uncapped_cutoff_gt_two {w : ℝ} {z : Node} (hb : 2 < z.cutoff) {ps : List ℕ}
    (hp : uncappedAllowed w 2 z ps) : 2 < (terminal w z ps).cutoff := by
  induction ps generalizing z with
  | nil => exact hb
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hx : 2 < primeExponent w p := (Finset.mem_filter.mp hc).2.1
    exact ih hx ht

theorem forest_insertion_eq_corrections {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (hb : 2 < z.cutoff) :
    forestSum w (highPrimes w z.cutoff z.closed) z
      (cutoffInsertion w (boundaryPrimes w) (fun _ y => nodeBenchmark w y))=
      boundaryCorrection w 2 z+residualCorrection w z := by
  unfold forestSum weightedValue boundaryCorrection residualCorrection
  rw [reference_family_eq_uncapped hw hs hr hz,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps hp
  have hpA : uncappedAllowed w 2 z ps := (Finset.mem_filter.mp hp).2
  have hsuf := suffix_highPrimes hw hs hr hz hpA
  have hcap := uncapped_cutoff_gt_two hb hpA
  dsimp only
  rw [hsuf]
  change signedWeight ps*sourceInsertion w (terminal w z ps)=_
  rw [source_insertion_identity hw _ hcap]
  unfold signedWeight
  ring

theorem actual_reference_decomposition {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (hb : 2 < z.cutoff) :
    sourceReference w z-nodeBenchmark w z=boundaryCorrection w 2 z+residualCorrection w z := by
  have h := finite_cutoff_decomposition w (highPrimes_above_boundary (b:=z.cutoff) hw z.closed)
    (fun _ y => nodeBenchmark w y) z
  rw [← sourcePrimes_partition hw hb z.closed] at h
  exact h.trans (forest_insertion_eq_corrections hw hs hr hz hb)

theorem actual_reference_value {w : ℝ} (hw : 1 < w) {z : Node} (hs : Valid z.side z.ratio)
    (hr : 0 < z.gap) (hz : Consistent z) (hb : 2 < z.cutoff) :
    sourceReference w z=nodeBenchmark w z+boundaryCorrection w 2 z+residualCorrection w z := by
  have h := actual_reference_decomposition hw hs hr hz hb
  linarith

end NumberTheoryLean.ReferenceSourceDecomposition

end

end Erdos970

end OAI
