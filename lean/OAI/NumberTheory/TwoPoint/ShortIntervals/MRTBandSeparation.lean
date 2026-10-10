import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalRamare

namespace OAI

/-! The actual MRT bands are disjoint, as required by the corrected
Ramaré decomposition; no disjointness hypothesis on those bands remains. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_adjacent_band_gap (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q j < mrtBandLower P Q (j + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hpow : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  apply Real.exp_lt_exp.mpr
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hlogQ.le j)
  have hp : 0 < (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by positivity
  nlinarith

lemma mrt_band_lower_monotone (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandLower P Q i ≤ mrtBandLower P Q j := by
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  refine Nat.le_induction le_rfl (fun k hk ih => ?_) j hij
  exact ih.trans (((mrt_band_endpoints P Q k (hi.trans hk) hP hPQ hlogQ).2).trans
    (mrt_adjacent_band_gap P Q k (hi.trans hk) hP hPQ hlogP).le)

lemma mrt_band_gap (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q i < mrtBandLower P Q j :=
  (mrt_adjacent_band_gap P Q i hi hP hPQ hlogP).trans_le
    (mrt_band_lower_monotone P Q (i + 1) j (by omega) (by omega) hP hPQ hlogP)

theorem mrt_actual_bands_pairwise_disjoint (P Q : ℝ) (J : ℕ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Set.univ : Set {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)})
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := mem_Icc.mp i.property
  have hj := mem_Icc.mp j.property
  have hn : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  have hip := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q i hi.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpi
  have hjp := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q j hj.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpj
  change mrtBandLower P Q i < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q i at hip
  change mrtBandLower P Q j < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q j at hjp
  rcases lt_or_gt_of_ne hn with hij' | hji'
  · have hgap := mrt_band_gap P Q i j hi.1 hij' hP hPQ hlogP
    linarith
  · have hgap := mrt_band_gap P Q j i hj.1 hji' hP hPQ hlogP
    linarith

end TwoPointCorrelations

end OAI
