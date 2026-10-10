import OAI.NumberTheory.Jacobsthal.Partitions.BoundedEdgeBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.BoundedEdgePrimeRange
open ErdosCofactorChoices ErdosSubsetWord BoundedEdgeBins
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints PrimeBinRepresentatives
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem bounded_edge_lower_exponent {w top xi M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (j : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) : leftExponent w (lower w top xi j) ≤ X := by
  obtain ⟨f,hf,u,hfu,_hm,hx⟩ := hj
  have hu : u ∈ globalBins w top xi j := ((mem_selections _ _ _).mp hf j).1 (by rw [hfu]; simp)
  have hh := bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) j.1)
    (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hu
  exact hh.1.le.trans hx

theorem bounded_edge_prime_range {w top xi M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (j : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) :
    w ≤ lower w top xi j ∧ lower w top xi j ≤ w^X := by
  refine ⟨(bin_source_bounds (zero_lt_one.trans hw) htop hxi j).1,?_⟩
  have hx := bounded_edge_lower_exponent hw htop hxi m j hj
  have hh : Real.log (lower w top xi j) ≤ X*Real.log w := (div_le_iff₀ (Real.log_pos hw)).mp hx
  apply (Real.log_le_log_iff (endpoint_pos (zero_lt_one.trans hw) j.1) (Real.rpow_pos_of_pos (zero_lt_one.trans hw) X)).mp
  rwa [Real.log_rpow (zero_lt_one.trans hw)]
end NumberTheoryLean.BoundedEdgePrimeRange



namespace NumberTheoryLean.BoundedEdgeHighPrimes
open ErdosSubsetWord ErdosCofactorChoices BoundedEdgeBins BoundedEdgePrimeRange
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints
open PrimeBinRepresentatives SourceLabelStrictOrder ErdosPrimeInputs.HarmonicPrimeMeasure


theorem bounded_edge_all_exponents {w top xi M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (j : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) {p : ℕ}
    (hp : p ∈ globalBins w top xi j) : primeExponent w p ≤ X+xi/Real.log w := by
  have hR : 0 < lower w top xi j := endpoint_pos (zero_lt_one.trans hw) j.1
  have he := (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have hb := (bin_exponent_bounds hw hR he hp).2
  have hl := bounded_edge_lower_exponent hw htop hxi m j hj
  have hwidth := bin_exponent_width (w:=w) hR he
  have hlog : Real.log (1+effectiveWidth w top xi) ≤ xi :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by
      have hh := effectiveWidth_le (zero_lt_one.trans hw) htop hxi
      linarith)
  have hdiv := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le
  change primeExponent w p ≤ rightExponent w (lower w top xi j) (effectiveWidth w top xi) at hb
  linarith

theorem bounded_edge_descendant_exponent {w top xi M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (j k : Fin (binCount w top xi))
    (hj : boundedEdgeBin w top xi Y m M X j) (hkj : k ≤ j) {p : ℕ}
    (hp : p ∈ globalBins w top xi k) : primeExponent w p ≤ X+xi/Real.log w := by
  rcases hkj.eq_or_lt with heq | hlt
  · subst k
    exact bounded_edge_all_exponents hw htop hxi m j hj hp
  · obtain ⟨f,hf,u,hfu,_hM,huX⟩ := hj
    have hu : u ∈ globalBins w top xi j := ((mem_selections _ _ _).mp hf j).1 (by rw [hfu]; simp)
    have hpS := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr
      (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp)
    have huS := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop u).mpr
      (bin_prime_in_source (zero_lt_one.trans hw) htop hxi j hu)
    have hpl := ((bin_mem_iff_label (zero_lt_one.trans hw) htop hxi k p).mp hp).2.2.2
    have hul := ((bin_mem_iff_label (zero_lt_one.trans hw) htop hxi j u).mp hu).2.2.2
    have hpu := prime_lt_of_label_lt hw htop hxi hpS huS (by rwa [hpl,hul])
    have hp0 : (0:ℝ)<p := by exact_mod_cast (bin_prime_in_source (zero_lt_one.trans hw) htop hxi k hp).1.pos
    have hpuR : (p:ℝ)≤u := by exact_mod_cast hpu.le
    have hx : primeExponent w p ≤ primeExponent w u :=
      div_le_div_of_nonneg_right (Real.log_le_log hp0 hpuR) (Real.log_pos hw).le
    have hnonneg := div_nonneg hxi.le (Real.log_pos hw).le
    linarith
end NumberTheoryLean.BoundedEdgeHighPrimes


end Erdos970

end OAI
