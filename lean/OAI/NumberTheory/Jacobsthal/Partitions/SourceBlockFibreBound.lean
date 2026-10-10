import OAI.NumberTheory.Jacobsthal.Estimates.SourceLargePairBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosHyperbolaError
  ErdosLargeHeightBlocks ErdosInversePrimeBin ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def blockPatternPrimes (R theta w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ primeBin R theta,p.Prime)
    (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern w H) :
    Finset (goodPrimes (primeBin R theta) H) :=
  Finset.univ.filter (fun p => p.val ∈ blockPrimes C0 R theta H i ∧
    actualFullPattern (primeBin R theta) w H C0 hw hP hlarge p = v)

theorem blockPatternPrimes_le_pairs (R theta w : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 1 < R) (htheta : 0 < theta) (hH : 0 < H) (hw : 0 ≤ w)
    (hP : ∀ p ∈ primeBin R theta,p.Prime) (hlarge : ∀ p ∈ primeBin R theta,w < (p : ℝ))
    (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern w H) :
    (blockPatternPrimes R theta w H C0 hw hP hlarge i v).card ≤
      (siftedSourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
        (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ)
        (blockLeft C0 R theta H i) (blockRight C0 R theta H i)
        (coordinateLower C0 R theta H i) (coordinateUpper C0 R theta H i) false true true false
          (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*coprimeModulus w H))).card := by
  apply original_prime_fibre_le_pairs (primeBin R theta) w H C0 hw hP hlarge _ v R hR
  intro p hp
  obtain ⟨hb,hv⟩ := (Finset.mem_filter.mp hp).2
  have hpP := (Finset.mem_filter.mp p.property).1
  have hprime := hP p hpP
  let : NeZero p.val := ⟨hprime.ne_zero⟩
  have hRp : 0 < R := by linarith
  have hbig := (mem_primeBin hRp.le htheta.le p).mp hpP
  have hbin := (mem_blockPrimes C0 R theta H i p hRp htheta).mp hb
  have hcoord := actual_m0_block_interval C0 R theta H i p hRp htheta hH
    (Finset.mem_filter.mp p.property).2 hb
  refine ⟨hv,hbig.2.1,hbin.2,?_⟩
  exact hcoord.1

theorem actual_block_rectangle_bounds (R theta : ℝ) (H : ℕ) (C0 : ℤ)
    (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hH : 0 < H)
    (i : Fin (blockCount C0 R theta H)) :
    blockLeft C0 R theta H i ≤ blockRight C0 R theta H i ∧
    blockRight C0 R theta H i-blockLeft C0 R theta H i ≤ R ∧
    coordinateLower C0 R theta H i ≤ coordinateUpper C0 R theta H i ∧
    coordinateUpper C0 R theta H i-coordinateLower C0 R theta H i ≤ 2*(H : ℝ) := by
  have hn := blockCount_pos C0 R theta H
  have hright : blockLeft C0 R theta H i < blockRight C0 R theta H i :=
    ErdosTagSubbins.left_lt_right hR htheta hn
  refine ⟨hright.le,?_,?_,block_coordinate_width C0 R theta H i hR htheta hH⟩
  · change ErdosTagSubbins.right R theta (blockCount C0 R theta H) i-
      ErdosTagSubbins.left R theta (blockCount C0 R theta H) i ≤ R
    rw [ErdosTagSubbins.right_sub_left]
    unfold ErdosTagSubbins.step
    have hden : (1 : ℝ) ≤ blockCount C0 R theta H := by exact_mod_cast hn
    have hh := div_le_self (mul_nonneg htheta.le hR.le) hden
    have hnum : theta*R ≤ R := by nlinarith
    simpa only [mul_comm] using hh.trans hnum
  · unfold coordinateLower coordinateUpper
    exact (min_le_max).trans (le_add_of_nonneg_right (Nat.cast_nonneg H))

end ErdosVarianceLargeMap

end

section

open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosVarianceLargeScale
  ErdosLargeHeightBlocks ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_block_fibre_bound (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R theta : ℝ),z^alpha ≤ R → 0 < theta → theta ≤ 1 →
      ∀ (H : ℕ) (C0 : ℤ),2 ≤ H → Int.gcd C0 (H : ℤ) = 1 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 →
      ∀ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
        (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ))
        (i : Fin (blockCount C0 R theta H)) (v : ErdosLargePatternLaw.FullPattern (sourceW z) H),
        ((blockPatternPrimes R theta (sourceW z) H C0 hw hP hlarge i v).card : ℝ) ≤
          C*(blockRight C0 R theta H i-blockLeft C0 R theta H i)/
            ((patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ)*Real.log R)+
              R^((9 : ℝ)/10) := by
  obtain ⟨C,hC,hbound⟩ := source_large_pair_bound alpha halpha
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with z hz
  refine ⟨hz.1,?_⟩
  intro R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge i v
  have hR1 : 1 < R := (Real.one_lt_rpow hz.1 halpha).trans_le hRlo
  have hR : 0 < R := by linarith
  have hH0 : 0 < H := by omega
  let T0 := divisorModulus (sourceW z) H
  let T1 := coprimeModulus (sourceW z) H
  have hT0 : 0 < T0 := divisorModulus_pos _ _
  have hT1 : 0 < T1 := coprimeModulus_pos _ _
  have hT0M : T0 ≤ smallModulus (sourceW z) := by
    have hh : T0 ≤ T0*T1 := by nlinarith
    exact hh.trans_eq (pattern_moduli_product _ _)
  have hSF : Squarefree T0 := IntervalBoundingSieve.squarefree_primeSet_product _
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)
  have hsupport : ∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H :=
    fun t _ ht => ht.trans (divisorModulus_dvd_H (sourceW z) H)
  have hcop : T1.Coprime (H*T0) := (effective_pattern_coprime _ _).symm
  have hunit := full_pattern_units (sourceW z) H v
  have hrectangle := actual_block_rectangle_bounds R theta H C0 hR htheta htheta1 hH0 i
  have hpairs := hz.2 R hRlo H T0 T1 hH hT0 hT1 hSF hsupport hcop hHlo hHhi hT0M
    C0 (v.2.1.val : ℤ) (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ)
    hC0 hunit.1 hunit.2
    (blockLeft C0 R theta H i) (blockRight C0 R theta H i)
    (coordinateLower C0 R theta H i) (coordinateUpper C0 R theta H i)
    hrectangle.1 hrectangle.2.1 hrectangle.2.2.1 hrectangle.2.2.2 false true true false
  have hactual := blockPatternPrimes_le_pairs R theta (sourceW z) H C0 hR1 htheta hH0 hw hP hlarge i v
  exact (show ((blockPatternPrimes R theta (sourceW z) H C0 hw hP hlarge i v).card : ℝ) ≤ _ by
    exact_mod_cast hactual).trans hpairs

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
