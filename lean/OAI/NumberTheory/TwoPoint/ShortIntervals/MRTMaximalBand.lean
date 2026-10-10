import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandLogGrowth

namespace OAI

/-! A maximal actual MRT band below a prescribed logarithmic cutoff.
The cubic next-band comparison supplies a large final lower endpoint. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_band_upper_log_mono {Q : ℝ} (hQ : 1 ≤ Real.log Q)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Real.log (mrtBandUpper Q i) ≤ Real.log (mrtBandUpper Q j) := by
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hi.trans hij
  have hbase : (i:ℝ)^(4*i+2) ≤ (j:ℝ)^(4*j+2) :=
    (pow_le_pow_left₀ hi0 (Nat.cast_le.mpr hij) _).trans
      (pow_le_pow_right₀ hj1 (by omega))
  simp only [mrtBandUpper,Real.log_exp]
  exact mul_le_mul hbase (pow_le_pow_right₀ hQ hij)
    (by positivity) (by positivity)

theorem mrt_maximal_band_exists {Q B : ℝ} (hQ : 1 ≤ Real.log Q)
    (hB : Real.log Q ≤ B) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.log (mrtBandUpper Q J) ≤ B ∧
      B < Real.log (mrtBandUpper Q (J+1)) ∧
      ∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ B := by
  have hB0 : 0 ≤ B := by linarith
  let S := (Icc 1 ⌊B⌋₊).filter (fun j => Real.log (mrtBandUpper Q j) ≤ B)
  have h1 : 1 ∈ S := by
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨le_rfl,?_⟩,?_⟩
    · exact Nat.le_floor (by simpa using (show (1:ℝ) ≤ B by linarith))
    · simpa [mrtBandUpper] using hB
  let J := S.max' ⟨1,h1⟩
  have hJmem : J ∈ S := max'_mem S ⟨1,h1⟩
  have hJ : 1 ≤ J := (mem_Icc.mp (mem_filter.mp hJmem).1).1
  have hJB : Real.log (mrtBandUpper Q J) ≤ B := (mem_filter.mp hJmem).2
  refine ⟨J,hJ,hJB,?_,fun j hj =>
    (mrt_band_upper_log_mono hQ (mem_Icc.mp hj).1 (mem_Icc.mp hj).2).trans hJB⟩
  by_contra hh
  have hnext : Real.log (mrtBandUpper Q (J+1)) ≤ B := le_of_not_gt hh
  have hnextB : J+1 ≤ ⌊B⌋₊ := Nat.le_floor
    ((mrt_band_index_le_log_upper Q (J+1) (by omega) hQ).trans hnext)
  have hnextmem : J+1 ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hnextB⟩,hnext⟩
  have hh' : J+1 ≤ J := le_max' S (J+1) hnextmem
  omega

/-- Cubing the last lower endpoint dominates the next upper endpoint;
the small exceptional index is handled by direct integer arithmetic. -/
lemma mrt_next_band_log_le_lower_cube {P Q : ℝ}
    (hP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) {j : ℕ} (hj : 2 ≤ j) :
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.log (mrtBandLower P Q j)^3 := by
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hindex : ((j+1:ℕ):ℝ)^(4*(j+1)+2) ≤ (j:ℝ)^(12*j) := by
    by_cases htwo : j=2
    · subst j
      norm_num
    have hj3 : 3 ≤ j := by omega
    have hj3R : (3:ℝ) ≤ j := by exact_mod_cast hj3
    have hsq : ((j+1:ℕ):ℝ) ≤ (j:ℝ)^2 := by push_cast; nlinarith
    calc
      _ ≤ ((j:ℝ)^2)^(4*(j+1)+2) := pow_le_pow_left₀ (by positivity) hsq _
      _ = (j:ℝ)^(2*(4*(j+1)+2)) := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_right₀ hj1 (by omega)
  have hq : Real.log Q^(j+1) ≤ Real.log Q^(3*(j-1)) :=
    pow_le_pow_right₀ hQ (by omega)
  have hp : (1:ℝ) ≤ Real.log P^3 := one_le_pow₀ hP
  have he1 : 4*j*3=12*j := by omega
  have he2 : (j-1)*3=3*(j-1) := by omega
  simp only [mrtBandUpper,mrtBandLower,Real.log_exp,mul_pow,← pow_mul,he1,he2]
  exact (mul_le_mul hindex hq (by positivity) (by positivity)).trans
    (le_mul_of_one_le_right (by positivity) hp)

/-- The first-band alternative covers J=1. Otherwise maximality and the
cubic comparison force the final lower endpoint above the desired target. -/
theorem mrt_maximal_band_lower {P Q B K : ℝ}
    (hP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hB : Real.log Q ≤ B) (hK : K^3 ≤ B)
    (hfirst : K ≤ Real.log P ∨ Real.log (mrtBandUpper Q 2) ≤ B) :
    ∃ J : ℕ, 1 ≤ J ∧ K ≤ Real.log (mrtBandLower P Q J) ∧
      B < Real.log (mrtBandUpper Q (J+1)) ∧
      ∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ B := by
  obtain ⟨J,hJ,_,hnext,hall⟩ := mrt_maximal_band_exists hQ hB
  refine ⟨J,hJ,?_,hnext,hall⟩
  by_cases hJ1 : J=1
  · subst J
    rcases hfirst with hp | hu
    · simpa [mrtBandLower] using hp
    · norm_num only at hnext
      linarith
  · have hJ2 : 2 ≤ J := by omega
    apply le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0)
      (show 0 ≤ Real.log (mrtBandLower P Q J) by
        simp only [mrtBandLower,Real.log_exp]
        positivity)
    exact hK.trans (hnext.le.trans (mrt_next_band_log_le_lower_cube hP hQ hJ2))

end TwoPointCorrelations

end OAI
