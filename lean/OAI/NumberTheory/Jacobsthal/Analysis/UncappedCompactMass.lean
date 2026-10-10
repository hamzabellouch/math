import OAI.NumberTheory.Jacobsthal.Estimates.PositiveGapMajorant

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UncappedCompactMass

attribute [local instance] Classical.propDecidable
open _root_.Set _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeCompactWeights
open ActualPrimeHigh SourceNodeCoordinates LiteralCompactRemoval LiteralPrimeOccupation
open PositiveGapMajorant OriginalPrimeOccupationLimit CompactLogOccupationTest NormalizedOccupationLimit
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def compactPrefixMass (K w ell : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*
    (if 2 ≤ (terminal w start ps).gap ∧ (terminal w start ps).gap ≤ K then 1 else 0)

theorem uncapped_terminal_ratio_le_gap {w ell : ℝ} {start : Node} {ps : List ℕ}
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hc : Consistent start) (hcut : ell ≤ start.cutoff) (hp : uncappedAllowed w ell start ps) :
    0 < (terminal w start ps).ratio ∧ (terminal w start ps).ratio ≤ (terminal w start ps).gap := by
  obtain ⟨U,_hU,hpU⟩ := (uncapped_iff_exists_ceiling w ell start ps).mp hp
  exact ⟨valid_pos (terminal_valid hs hpU),history_ratio_le_gap hell hr hs hc hcut ⟨ps,hpU⟩⟩

theorem uniform_uncapped_compact_mass (K ell d : ℝ) (hK : 3 ≤ K) (hell : 1 ≤ ell) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B → B^2*compactPrefixMass K w ell start ≤ C := by
  obtain ⟨H,hcompact,hbounds,hOne,hzero⟩ := exists_positive_gap_majorant K
  let HH : Side → ℝ×ℝ → ℝ := fun _ => H
  have hH : ∀ i,Continuous (HH i) := fun _ => H.continuous
  have hCpt : ∀ i,HasCompactSupport (HH i) := fun _ => hcompact
  have hsupport : ∀ i : Side,∀ r s : ℝ,r<1 ∨ K+1<r → HH i (r,s)=0 := fun _ => hzero
  obtain ⟨BL,w₀,hBL,hw₀,hlim⟩ := original_prime_continuous_occupation_limit hH hCpt
    (by norm_num : 0 < (1:ℝ)) (by linarith : 0 < K+1) hell hsupport d 1 hd (by norm_num)
  let L : ℝ := |invariantAverage (arrivalTest ell HH)|+1
  let W : ℝ := weight .even (199/100)
  have hL : 0 < L := by dsimp [L]; positivity
  have hW : 0 < W := weight_pos (by norm_num [Valid])
  refine ⟨W*L,max BL ell,w₀,mul_pos hW hL,hBL.trans_le (le_max_left _ _),hw₀,?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBL' : BL ≤ B := (le_max_left _ _).trans hB
  have hellB : ell ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := hBL.trans_le hBL'
  obtain ⟨hs,hr,hBgap,_hsize⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have hlimit := hlim B w hBL' hw hcomp start hi h199 h23 hcons hcut
  have hnorm : uncappedFamilyValue HH w ell start ≤ L := by
    have hu := (abs_le.mp hlimit).2
    have hab := le_abs_self (invariantAverage (arrivalTest ell HH))
    dsimp only [L]
    linarith
  let Z : ℝ := ∑ ps ∈ uncappedPrefixes w ell start,prefixWeight ps*nodeReward HH w start ps
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun ps _ => mul_nonneg (prefixWeight_nonneg ps) (hbounds _).1)
  have hdom : compactPrefixMass K w ell start ≤ Z := by
    apply Finset.sum_le_sum
    intro ps hp
    apply mul_le_mul_of_nonneg_left _ (prefixWeight_nonneg ps)
    change (if 2 ≤ (terminal w start ps).gap ∧ (terminal w start ps).gap ≤ K then 1 else 0) ≤
      H ((terminal w start ps).gap,(terminal w start ps).ratio)
    split_ifs with hgap
    · have hpA : uncappedAllowed w ell start ps := (Finset.mem_filter.mp hp).2
      have hratio := uncapped_terminal_ratio_le_gap hell hr hs hcons (by rwa [hcut]) hpA
      rw [hOne _ _ hgap.1 hgap.2 hratio.1.le (hratio.2.trans hgap.2)]
    · exact (hbounds _).1
  have hwpos := weight_pos hs
  have hwupper : weight start.side start.ratio ≤ W := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (by rwa [hi] at hs) h199
  have hsq : B^2 ≤ start.gap^2 := by nlinarith
  calc
    B^2*compactPrefixMass K w ell start ≤ B^2*Z := mul_le_mul_of_nonneg_left hdom (sq_nonneg B)
    _ ≤ start.gap^2*Z := mul_le_mul_of_nonneg_right hsq hZ
    _ = weight start.side start.ratio*uncappedFamilyValue HH w ell start := by
      unfold uncappedFamilyValue
      dsimp only [Z]
      field_simp
    _ ≤ weight start.side start.ratio*L := mul_le_mul_of_nonneg_left hnorm hwpos.le
    _ ≤ W*L := mul_le_mul_of_nonneg_right hwupper hL.le

end NumberTheoryLean.UncappedCompactMass

end

end Erdos970

end OAI
