import OAI.NumberTheory.TotientAsymptotic.SimplexVolume

namespace OAI

/-! Diagonal changes of variables bounding a linear cap of the standard simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def simplexDiagonal (N : ℕ) (w : Fin N → ℝ) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' (Matrix.diagonal w)

lemma simplexDiagonal_apply (N : ℕ) (w v : Fin N → ℝ) (i : Fin N) :
    simplexDiagonal N w v i = w i*v i := by
  simp [simplexDiagonal, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma simplexDiagonal_det (N : ℕ) (w : Fin N → ℝ) :
    LinearMap.det (simplexDiagonal N w) = ∏ i, w i := by
  rw [simplexDiagonal, LinearMap.det_toLin', Matrix.det_diagonal]

def positiveSimplex (N : ℕ) (w : Fin N → ℝ) (T : ℝ) : Set (Fin N → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, w i*v i) ≤ T}

lemma positiveSimplex_eq_preimage (N : ℕ) (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) (T : ℝ) :
    positiveSimplex N w T = simplexDiagonal N w ⁻¹' standardSimplex N T := by
  ext v
  simp only [positiveSimplex, standardSimplex, Set.mem_preimage, Set.mem_ofPred_eq,
    simplexDiagonal_apply]
  exact and_congr (forall_congr' fun i => (mul_nonneg_iff_of_pos_left (hw i)).symm) Iff.rfl

lemma volume_positiveSimplex (N : ℕ) (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) {T : ℝ} (hT : 0 ≤ T) :
    volume (positiveSimplex N w T) =
      ENNReal.ofReal (T^N / ((N.factorial : ℝ)*∏ i, w i)) := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  rw [positiveSimplex_eq_preimage N w hw,
    ← Measure.map_apply (simplexDiagonal N w).continuous_of_finiteDimensional.measurable
      (measurableSet_standardSimplex N T),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [simplexDiagonal_det]; exact hp.ne'),
    simplexDiagonal_det, Measure.smul_apply, smul_eq_mul, volume_standardSimplex N hT,
    abs_inv, abs_of_pos hp, ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma simplex_lower_cap_subset (N : ℕ) (B t s : ℝ) (w : Fin N → ℝ)
    (hs : 0 ≤ s) :
    standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t} ⊆
      positiveSimplex N (fun i => 1+s*w i) (B+s*t) := by
  rintro v ⟨⟨hv,hB⟩,ht⟩
  refine ⟨hv,?_⟩
  calc
    _ = (∑ i, v i)+s*(∑ i, w i*v i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ B+s*t := add_le_add hB (mul_le_mul_of_nonneg_left ht hs)

/-- A finite-dimensional Chernoff bound, before logarithmic estimation. -/
theorem volume_simplex_lower_cap_le (N : ℕ) (B t s : ℝ) (w : Fin N → ℝ)
    (hs : 0 ≤ s) (hw : ∀ i, 0 < 1+s*w i) (hT : 0 ≤ B+s*t) :
    (volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t})).toReal ≤
      (B+s*t)^N / ((N.factorial : ℝ)*∏ i, (1+s*w i)) := by
  have hb : volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t}) ≤
      volume (positiveSimplex N (fun i => 1+s*w i) (B+s*t)) :=
    measure_mono (simplex_lower_cap_subset N B t s w hs)
  rw [volume_positiveSimplex N _ hw hT] at hb
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hT _)
    (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (hw i).le))))] at hh
  exact hh

lemma simplex_upper_cap_eq_lower (N : ℕ) (w : Fin N → ℝ) (t : ℝ) :
    {v : Fin N → ℝ | t ≤ ∑ i, w i*v i} =
      {v | (∑ i, (-w i)*v i) ≤ -t} := by
  ext v
  simp only [Set.mem_ofPred_eq, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]

/-- The corresponding upper-tail volume bound. -/
theorem volume_simplex_upper_cap_le (N : ℕ) (B t s : ℝ) (w : Fin N → ℝ)
    (hs : 0 ≤ s) (hw : ∀ i, 0 < 1-s*w i) (hT : 0 ≤ B-s*t) :
    (volume (standardSimplex N B ∩ {v | t ≤ ∑ i, w i*v i})).toReal ≤
      (B-s*t)^N / ((N.factorial : ℝ)*∏ i, (1-s*w i)) := by
  rw [simplex_upper_cap_eq_lower]
  convert volume_simplex_lower_cap_le N B (-t) s (fun i => -w i) hs
    (by simpa only [mul_neg, ← sub_eq_add_neg] using hw)
    (by simpa only [mul_neg, ← sub_eq_add_neg] using hT) using 1
  simp only [mul_neg, ← sub_eq_add_neg]

end TotientAsymptotic

end

end OAI
