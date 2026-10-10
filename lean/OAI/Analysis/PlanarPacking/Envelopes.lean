import OAI.Analysis.PlanarPacking.DirectBounds

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma pieceL_antitone (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    pieceL j t ≤ pieceL j s := by
  have he : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*(t-s)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hh := mul_nonneg (mul_nonneg Real.pi_pos.le (dampingCap_pos ⟨j.val+1,by omega⟩).le) (sub_nonneg.mpr hst)
    nlinarith
  have hh:=pieceL_shift_bound j hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at hh
  exact hh.trans (by nlinarith [pieceL_nonneg j hs])
lemma atomL_antitone (j : Fin 7) {s t : ℝ} (hst : s ≤ t) : atomL j t ≤ atomL j s := by
  unfold atomL
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_pos Real.pi_pos (dampingCap_pos j)]
  · exact mul_nonneg (by fin_cases j <;> norm_num [atomMass]) (lambdaCap_nonneg _)
noncomputable def directEnvelope (ell : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j/6*(Real.pi*((j.val:ℝ)+1)/6)^ell
noncomputable def transformEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  ∑ j : Fin 6,densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell
noncomputable def atomicEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  ∑ j : Fin 7,atomL j s*(Real.pi*zCap j)^ell
lemma directEnvelope_nonneg (ell : ℕ) : 0 ≤ directEnvelope ell := by
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (div_nonneg (densityCap_nonneg j) (by norm_num)) (by positivity)
lemma transformEnvelope_nonneg (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ transformEnvelope ell s := by
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (mul_nonneg (densityCap_nonneg _) (pieceL_nonneg _ hs))
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)
lemma atomicEnvelope_nonneg (ell : ℕ) (s : ℝ) : 0 ≤ atomicEnvelope ell s := by
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (atomL_nonneg _ _) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)
lemma transformEnvelope_antitone (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    transformEnvelope ell t ≤ transformEnvelope ell s := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pieceL_antitone j hs hst)
    (densityCap_nonneg _)) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)
lemma atomicEnvelope_antitone (ell : ℕ) {s t : ℝ} (hst : s ≤ t) :
    atomicEnvelope ell t ≤ atomicEnvelope ell s := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_right (atomL_antitone j hst)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)
lemma Pmoment_norm_bound (ell : ℕ) (s : ℝ) : |Pmoment ell s| ≤ 25*Real.pi^ell := by
  have he : Pmoment ell s=(∑ j : Fin 7,atomicCoefficient j*directKernel ell s ((j.val:ℝ)/6)).re := by
    norm_num [Pmoment,atomicCoefficient,directKernel,Fin.sum_univ_succ,Finset.sum_Icc_succ_top]
    ring
  rw [he]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 7,atomMass j*Real.pi^ell := by
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul,atomicCoefficient_norm,directKernel_norm,abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left
      · apply pow_le_pow_left₀ (by positivity)
        have hj : (j.val:ℝ) ≤ 6 := by exact_mod_cast (by omega : j.val ≤ 6)
        nlinarith [Real.pi_pos]
      · fin_cases j <;> norm_num [atomMass]
    _=25*Real.pi^ell := by rw [← Finset.sum_mul]; norm_num [atomMass,Fin.sum_univ_succ]
lemma direct_spectral_bound (p : CardinalData) (ell : ℕ) (s : ℝ) :
    |cardinalSeries p ell s| ≤ 
      |p.C| *25*Real.pi^ell+(|p.c₀|+|p.d₀|+‖p.x‖)*directEnvelope ell := by
  have he:=directDensity_series p ell s
  have he' : cardinalSeries p ell s=p.C*Pmoment ell s+
    (∑ j ∈ Finset.range 6,∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t*directKernel ell s t).re := by
    rw [he]; unfold cardinalSeries; ring
  rw [he']
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (Pmoment_norm_bound ell s) (abs_nonneg _)
  · apply (Complex.abs_re_le_norm _).trans
    rw [← Fin.sum_univ_eq_sum_range]
    apply (norm_sum_le _ _).trans
    unfold directEnvelope
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    simpa only [mul_div_assoc,mul_assoc] using direct_piece_bound p j ell s
lemma direct_envelope_coarse (ell : ℕ) : directEnvelope ell ≤ 
    (∑ j : Fin 6,densityCap j/6)*Real.pi^ell := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀ (by positivity)
    have hj : (j.val:ℝ)+1 ≤ 6 := by exact_mod_cast (by omega : j.val+1 ≤ 6)
    nlinarith [Real.pi_pos]
  · exact div_nonneg (densityCap_nonneg _) (by norm_num)
end SharpPlanar

end OAI
