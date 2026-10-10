import OAI.NumberTheory.CubicMoment.Transform.MetaplecticMellinGrowth
import OAI.NumberTheory.CubicMoment.Estimates.MellinPositiveTest
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticContinuationProof
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticMellinShift

namespace OAI

/-! Polynomial growth of the canonical Gauss continuation, derived
directly from the published Voronoi identity. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticFullContinuation_weighted
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hWp : tsupport W ⊆ Ioi 0)
    (hWs : ContDiff ℝ ∞ W) {s : ℂ} (hs : 0 < s.re)
    (hMW : mellin W s ≠ 0) (hsp : s ≠ 5/6) :
    mellin W s*metaplecticFullContinuation r s = metaplecticWeightedRegular r W s+
      metaplecticCompletedResidue r*mellin W (5/6)/(s-5/6) := by
  unfold metaplecticFullContinuation
  rw [metaplecticRegularContinuation_eq_test hV hr hsr W hW hWp hWs hs hMW]
  unfold metaplecticRegularNumerator
  rw [dslope_of_ne _ hsp,slope,smul_eq_mul]
  simp only [vsub_eq_sub]
  field_simp
  ring

lemma metaplecticHeightTest_cancel (σ t : ℝ) :
    mellin (metaplecticHeightTest (-t)) ((σ:ℂ)+(t:ℂ)*Complex.I) =
      mellin normPartitionWeight (σ:ℂ) := by
  rw [metaplecticHeightTest_mellin]
  congr 1
  push_cast
  ring

theorem metaplectic_strip_polynomial_of_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    {ε : ℝ} (hε : 0 < ε) :
    MetaplecticStripPolynomial (metaplecticCanonicalGauss r) (1/2+ε) 2 := by
  by_cases hεlarge : 2 < 1/2+ε
  · refine ⟨0,le_rfl,0,?_⟩
    intro σ hσ t _
    linarith [hσ.1,hσ.2]
  obtain ⟨C,N,hC,hJ⟩ := metaplecticWeightedRegular_height_bound hV hr hsr
    (show 0 < 1/2+ε by linarith) (le_of_not_gt hεlarge)
  obtain ⟨M,hM,hMW⟩ := smooth_mellin_vertical_decay normPartitionWeight
    normPartitionWeight_compact normPartitionWeight_positive_support normPartitionWeight_smooth
    (5/6) 0
  obtain ⟨D,hD,hDinv⟩ := normPartitionWeight_mellin_inverse_bound (1/2+ε) 2
  obtain ⟨E,hE,hEinv⟩ := metaplecticCompletionEuler_inverse_uniform hε
  let B : ℝ := ‖metaplecticCompletedResidue r‖*M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(C+B)*D*E,by positivity,N,?_⟩
  intro σ hσ t ht
  let s : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
  let W : ℝ → ℂ := metaplecticHeightTest (-t)
  have hsre : 0 < s.re := by dsimp [s]; simp; linarith [hσ.1]
  have him : (s-5/6).im = t := by simp [s]
  have hnorm : 1 ≤ ‖s-5/6‖ := ht.trans (by rw [←him]; exact Complex.abs_im_le_norm _)
  have hsp : s ≠ (5/6:ℂ) := by
    intro h
    have hz : s-5/6 = 0 := sub_eq_zero.mpr h
    rw [hz,norm_zero] at hnorm
    norm_num at hnorm
  have hW : mellin W s = mellin normPartitionWeight (σ:ℂ) :=
    metaplecticHeightTest_cancel σ t
  have hWn : mellin W s ≠ 0 := by
    rw [hW]
    intro hz
    have hp := normPartitionWeight_mellin_real_positive σ
    rw [hz,Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hden : ‖(s-5/6)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hnorm
  have hMWt : ‖mellin W (5/6)‖ ≤ M := by
    rw [metaplecticHeightTest_mellin]
    simpa only [pow_zero,one_mul,Complex.ofReal_div,Complex.ofReal_ofNat] using hMW (-t)
  have hJt : ‖metaplecticWeightedRegular r W s‖ ≤ C*(1+|t|)^N := by
    simpa only [abs_neg] using hJ σ hσ (-t) t
  have hpole : ‖metaplecticCompletedResidue r*mellin W (5/6)/(s-5/6)‖ ≤ B := by
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    simpa only [mul_one,B] using
      mul_le_mul (mul_le_mul_of_nonneg_left hMWt (_root_.norm_nonneg _)) hden
        (_root_.norm_nonneg _) (by positivity : 0 ≤ ‖metaplecticCompletedResidue r‖*M)
  have heq : metaplecticCanonicalGauss r s =
      (metaplecticWeightedRegular r W s+
        metaplecticCompletedResidue r*mellin W (5/6)/(s-5/6))*
          (mellin W s)⁻¹*(metaplecticCompletionEuler r s)⁻¹ := by
    rw [←metaplecticFullContinuation_weighted hV hr hsr W
      (metaplecticHeightTest_compact _) (metaplecticHeightTest_positive _)
      (metaplecticHeightTest_smooth _) hsre hWn hsp]
    unfold metaplecticCanonicalGauss
    rw [mul_right_comm (mellin W s) (metaplecticFullContinuation r s) ((mellin W s)⁻¹),
      mul_inv_cancel₀ hWn,one_mul,div_eq_mul_inv]
  change ‖metaplecticCanonicalGauss r s‖ ≤ _
  rw [heq,norm_mul,norm_mul]
  have hsum : ‖metaplecticWeightedRegular r W s+
      metaplecticCompletedResidue r*mellin W (5/6)/(s-5/6)‖ ≤ (C+B)*(1+|t|)^N := by
    apply (norm_add_le _ _).trans
    have hpow : 1 ≤ (1+|t|)^N := one_le_pow₀ (by linarith [abs_nonneg t])
    calc
      _ ≤ C*(1+|t|)^N+B := add_le_add hJt hpole
      _ ≤ C*(1+|t|)^N+B*(1+|t|)^N :=
        add_le_add le_rfl (le_mul_of_one_le_right hB hpow)
      _ = _ := by ring
  have hDi : ‖(mellin W s)⁻¹‖ ≤ D := by rw [hW]; exact hDinv σ hσ
  have hEi : ‖(metaplecticCompletionEuler r s)⁻¹‖ ≤ E :=
    hEinv r (primary_ne_zero hr) s (by simpa [s] using hσ.1)
  calc
    _ ≤ ((C+B)*(1+|t|)^N)*D*E := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
