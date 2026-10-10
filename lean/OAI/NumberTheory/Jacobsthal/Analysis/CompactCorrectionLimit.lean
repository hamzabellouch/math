import OAI.NumberTheory.Jacobsthal.Harmonic.CompactAnomalyTest

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Finset
namespace ErdosCorrectionOccupation
attribute [local instance] Classical.propDecidable
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.UncappedCompactMass NumberTheoryLean.SourceNodeCoordinates
open NumberTheoryLean.ActualBoundaryDomain NumberTheoryLean.LiteralUniformPrimeTail
open NumberTheoryLean.LiteralPrimeOccupation
open ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.PrimePrefixTail

noncomputable def compactCorrection (K w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*
    compactAnomalyTest K (terminal w start ps).side ((terminal w start ps).gap,(terminal w start ps).ratio)

theorem compact_correction_error {C c K B w ell : ℝ}
    (hA : ∀ r : ℝ,2 ≤ r → ∀ i : Side,|continuousAnomaly i r| ≤ C*Real.exp (-c*r))
    (hB : 4 ≤ B) (hell : 2 ≤ ell) (hellB : ell ≤ B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) :
    |continuousBoundaryCorrection w ell start-compactCorrection K w ell start| ≤
      C*(∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*tailListReward c K w start ps) := by
  obtain ⟨hs,hr,_hBgap,_hsize⟩ := source_node_bounds (by linarith : 0 < B) start hi h199 h23 hcons hcut
  rw [continuousBoundaryCorrection_eq_state_reward w ell start hi,compactCorrection,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ps hp
  have hpA : uncappedAllowed w ell start ps := (Finset.mem_filter.mp hp).2
  have hr2 := boundary_gap_ge_two (source_boundary_domain hB hell start hi h199 h23 hcons hcut hpA)
  have hratio := uncapped_terminal_ratio_le_gap (by linarith : 1 ≤ ell) hr hs hcons (by rwa [hcut]) hpA
  have he := compactAnomalyTest_error K (terminal w start ps).side hr2 hratio.1.le hratio.2
  have henv : (if K < (terminal w start ps).gap then |continuousAnomaly (terminal w start ps).side (terminal w start ps).gap| else 0) ≤
      C*tailListReward c K w start ps := by
    unfold tailListReward
    split_ifs
    · exact hA _ hr2 _
    · simp
  rw [← mul_sub,abs_mul,abs_of_nonneg (prefixWeight_nonneg ps)]
  have hh := mul_le_mul_of_nonneg_left (he.trans henv) (prefixWeight_nonneg ps)
  convert hh using 1
  ring

theorem uniform_compact_correction (ell d eps : ℝ) (hell : 2 ≤ ell)
    (hd : 0 < d) (heps : 0 < eps) :
    ∃ K B₀ w₀ : ℝ,3 ≤ K ∧ 0 < B₀ ∧ 1 < w₀ ∧
      ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        B^2*|continuousBoundaryCorrection w ell start-compactCorrection K w ell start| ≤ eps := by
  obtain ⟨C,c,_wA,hC,hc,_hwA,_hD,hA⟩ := common_anomaly_exponential
  obtain ⟨M₀,BT,wT,hBT,hwT,hT⟩ := actual_uniform_original_prime_tail d c (eps/C) hd hc (div_pos heps hC)
  let K : ℝ := 3*((M₀:ℝ)+1)
  have hK : 3 ≤ K := by dsimp [K]; have hn := Nat.cast_nonneg (α := ℝ) M₀; linarith
  refine ⟨K,max BT (max 4 ell),wT,hK,hBT.trans_le (le_max_left _ _),hwT,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBT' : BT ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hellB : ell ≤ B := ((le_max_right _ _).trans (le_max_right _ _)).trans hB
  have ht := hT M₀ le_rfl B w hBT' hw ell (by linarith) hellB hcomp start hi h199 h23 hcons hcut
  have he := compact_correction_error (K := K) (w := w) hA hB4 hell hellB start hi h199 h23 hcons hcut
  have heB := mul_le_mul_of_nonneg_left he (sq_nonneg B)
  have htC := mul_le_mul_of_nonneg_left ht hC.le
  have hcanc : C*(eps/C)=eps := mul_div_cancel₀ eps (ne_of_gt hC)
  rw [hcanc] at htC
  nlinarith

end ErdosCorrectionOccupation

end

section

namespace ErdosCorrectionOccupation
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeBinMembership NumberTheoryLean.ActualPrimeHigh
open NumberTheoryLean.OriginalPrimeOccupationLimit
open NumberTheoryLean.CompactLogOccupationTest NumberTheoryLean.NormalizedOccupationLimit

theorem fixed_compact_correction_limit (K ell d eps : ℝ) (hK : 3 ≤ K) (hell : 2 ≤ ell)
    (hd : 0 < d) (heps : 0 < eps) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |(start.gap^2/weight start.side start.ratio)*compactCorrection K w ell start-
          invariantAverage (arrivalTest ell (compactAnomalyTest K))| ≤ eps := by
  simpa only [compactCorrection] using
    literal_original_prime_occupation
      (fun i => compactAnomalyTest_continuous K i)
      (fun i => compactAnomalyTest_compact K i)
      (by norm_num : (0:ℝ)<1) (by linarith : 0<K+1) (by linarith : 1≤ell)
      (fun i r s hr => compactAnomalyTest_support K i r s hr) d eps hd heps

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
