import OAI.Geometry.Immersion.ClosedSurface.PhaseCoordinates
import OAI.Geometry.Immersion.ClosedSurface.DirectionStability
import OAI.Geometry.Immersion.ClosedSurface.LengthMargins

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma relative_margin_covector_sq {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    {ε : ℝ} (hB : B ≠ 0)
    (hmargin : ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖) :
    ε ≤ 4*‖ξ‖^2 := by
  have hlen := norm_secondQuadratic_le B (-ξ.2,ξ.1)
  rw [norm_rotated_covector] at hlen
  have hh : ε*‖B‖ ≤ (4*‖ξ‖^2)*‖B‖ := hmargin.trans (by nlinarith [hlen])
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hB)).mp hh

lemma covector_norm_sq_le (ξ : Base) : ‖ξ‖^2 ≤ ξ.1^2 + ξ.2^2 := by
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  rcases le_total |ξ.1| |ξ.2| with h | h
  · rw [max_eq_right h, sq_abs]
    linarith [sq_nonneg ξ.1]
  · rw [max_eq_left h, sq_abs]
    linarith [sq_nonneg ξ.2]



theorem reciprocal_second_length_bound {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (hB : b ≤ ‖B‖)
    (hmargin : ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖) :
    ‖secondQuadratic B (-ξ.2,ξ.1)‖⁻¹ ≤ (ε*b)⁻¹ := by
  have hp := (mul_pos hε hb).trans_le ((mul_le_mul_of_nonneg_left hB hε.le).trans hmargin)
  simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hε hb)
    ((mul_le_mul_of_nonneg_left hB hε.le).trans hmargin)



theorem phase_inverse_norm_bound {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    {ε C : ℝ} (hε : 0 < ε) (hB : B ≠ 0) (hC : ‖ξ‖ ≤ C)
    (hmargin : ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖) :
    ∃ hξ : ξ ≠ 0, ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ 8*C/ε := by
  have hsq := relative_margin_covector_sq B ξ hB hmargin
  have hn : ξ ≠ 0 := by
    intro h
    simp only [h,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hsq
    linarith
  refine ⟨hn,?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg ξ).trans hC
  have hd : ε/4 ≤ ξ.1^2+ξ.2^2 := by
    have hh := covector_norm_sq_le ξ
    linarith
  have hd0 := covector_length_sq_pos hn
  have h1 : |ξ.1| ≤ C := by
    exact (show |ξ.1| ≤ ‖ξ‖ by simpa only [Real.norm_eq_abs] using norm_fst_le ξ).trans hC
  have h2 : |ξ.2| ≤ C := by
    exact (show |ξ.2| ≤ ‖ξ‖ by simpa only [Real.norm_eq_abs] using norm_snd_le ξ).trans hC
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(phaseEquiv ξ hn).symm v‖ ≤ (8*C/ε)*‖v‖
  rw [phaseEquiv_symm_apply,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff]
  have hv1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  have hnum1 : |ξ.1*v.1-ξ.2*v.2| ≤ 2*C*‖v‖ := by
    calc
      _ ≤ |ξ.1*v.1|+|ξ.2*v.2| := abs_sub _ _
      _ ≤ C*‖v‖+C*‖v‖ := by rw [abs_mul,abs_mul]; gcongr
      _ = _ := by ring
  have hnum2 : |ξ.2*v.1+ξ.1*v.2| ≤ 2*C*‖v‖ := by
    calc
      _ ≤ |ξ.2*v.1|+|ξ.1*v.2| := abs_add_le _ _
      _ ≤ C*‖v‖+C*‖v‖ := by rw [abs_mul,abs_mul]; gcongr
      _ = _ := by ring
  have hbnd : 2*C*‖v‖/(ξ.1^2+ξ.2^2) ≤ (8*C/ε)*‖v‖ := by
    calc
      _ ≤ 2*C*‖v‖/(ε/4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = _ := by field_simp; ring
  constructor
  · rw [abs_div,abs_of_pos hd0]
    exact (div_le_div_of_nonneg_right hnum1 hd0.le).trans hbnd
  · rw [abs_div,abs_of_pos hd0]
    exact (div_le_div_of_nonneg_right hnum2 hd0.le).trans hbnd



theorem weighted_selected_denominators {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    {ε b C W w : ℝ} (hε : 0 < ε) (hb : 0 < b) (hC : 0 ≤ C)
    (hB : b/2 ≤ ‖B‖) (hξ : ‖ξ‖ ≤ C) (hw : 1 ≤ w) (hwW : w ≤ W)
    (hm : (ε/4)*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖) :
    ‖secondQuadratic B (-(w • ξ).2,(w • ξ).1)‖⁻¹ ≤ 8/(ε*b) ∧
    ∃ hn : w • ξ ≠ 0,
      ‖(phaseEquiv (w • ξ) hn).symm.toContinuousLinearMap‖ ≤ 32*W*C/ε := by
  have hw0 : 0 ≤ w := by linarith
  have hw2 : 1 ≤ w^2 := by nlinarith
  have hm' : (ε/4)*‖B‖ ≤ ‖secondQuadratic B (-(w • ξ).2,(w • ξ).1)‖ := by
    rw [norm_secondQuadratic_rotated_smul]
    exact hm.trans (by nlinarith [norm_nonneg (secondQuadratic B (-ξ.2,ξ.1))])
  have hB0 : B ≠ 0 := norm_pos_iff.mp ((half_pos hb).trans_le hB)
  have hξ' : ‖w • ξ‖ ≤ W*C := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hw0]
    exact (mul_le_mul_of_nonneg_left hξ hw0).trans (mul_le_mul_of_nonneg_right hwW hC)
  constructor
  · convert reciprocal_second_length_bound B (w • ξ)
      (div_pos hε (by norm_num : (0:ℝ)<4)) (half_pos hb) hB hm' using 1
    field_simp
    ring
  · obtain ⟨hn,hbound⟩ := phase_inverse_norm_bound B (w • ξ)
      (div_pos hε (by norm_num : (0:ℝ)<4)) hB0 hξ' hm'
    refine ⟨hn,hbound.trans_eq ?_⟩
    field_simp
    ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
