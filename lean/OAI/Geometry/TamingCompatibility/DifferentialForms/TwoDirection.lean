import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiDdcBound

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma two_direction_inner_sq_le (z u v : E) (huv : ⟪u,v⟫ = 0) (hv : ‖v‖ = ‖u‖) :
    ⟪z,u⟫^2 + ⟪z,v⟫^2 ≤ ‖z‖^2*‖u‖^2 := by
  by_cases hu : u = 0
  · have hv0 : v = 0 := norm_eq_zero.mp (by simpa [hu] using hv)
    simp [hu,hv0]
  have hu2 : 0 < ‖u‖^2 := pow_pos (norm_pos_iff.mpr hu) 2
  have hvu : ⟪v,u⟫ = 0 := by rw [real_inner_comm,huv]
  have hzu : ⟪u,z⟫ = ⟪z,u⟫ := real_inner_comm _ _
  have hzv : ⟪v,z⟫ = ⟪z,v⟫ := real_inner_comm _ _
  have h : 0 ≤ ⟪‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v,
    ‖u‖^2 • z - ⟪z,u⟫ • u - ⟪z,v⟫ • v⟫ := real_inner_self_nonneg
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    huv,hvu,hzu,hzv] at h
  simp only [real_inner_self_eq_norm_sq,hv] at h
  nlinarith
end TamingCompatibility.RadialPotential

end

noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma logPotential_trace_lower {s : ℝ} (hs : 0 < s) (z u v : E)
    (huv : ⟪u,v⟫ = 0) (hv : ‖v‖ = ‖u‖) :
    2*s^2*‖u‖^2/(s^2+‖z‖^2)^2 ≤
      fderiv ℝ (fderiv ℝ (logPotential s)) z u u +
      fderiv ℝ (fderiv ℝ (logPotential s)) z v v := by
  have hA := radial_sq_pos hs z
  have hS := two_direction_inner_sq_le z u v huv hv
  rw [logPotential_hessian hs,logPotential_hessian hs,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hv]
  calc
    _ ≤ (2*(s^2+‖z‖^2)*‖u‖^2 - 2*(⟪z,u⟫^2+⟪z,v⟫^2))/(s^2+‖z‖^2)^2 := by
      apply (div_le_div_iff_of_pos_right (pow_pos hA 2)).mpr
      nlinarith
    _ = _ := by field_simp; ring

lemma sqrtPotential_trace_lower {s : ℝ} (hs : 0 < s) (z u v : E)
    (huv : ⟪u,v⟫ = 0) (hv : ‖v‖ = ‖u‖) :
    ‖u‖^2/Real.sqrt (s^2+‖z‖^2) ≤
      fderiv ℝ (fderiv ℝ (sqrtPotential s)) z u u +
      fderiv ℝ (fderiv ℝ (sqrtPotential s)) z v v := by
  have hA := radial_sq_pos hs z
  have hq := Real.sqrt_pos.mpr hA
  have hq2 := Real.sq_sqrt (le_of_lt hA)
  have hS := two_direction_inner_sq_le z u v huv hv
  rw [sqrtPotential_hessian hs,sqrtPotential_hessian hs,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hv]
  calc
    _ = ((Real.sqrt (s^2+‖z‖^2))^2 * ‖u‖^2)/(Real.sqrt (s^2+‖z‖^2))^3 := by
      field_simp
    _ ≤ (2*(Real.sqrt (s^2+‖z‖^2))^2*‖u‖^2 -
      (⟪z,u⟫^2+⟪z,v⟫^2))/(Real.sqrt (s^2+‖z‖^2))^3 := by
      apply (div_le_div_iff_of_pos_right (pow_pos hq 3)).mpr
      rw [hq2]
      nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg ‖u‖)]
    _ = _ := by field_simp; ring
end TamingCompatibility.RadialPotential

end

noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma logPotential_smooth {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (logPotential (E := E) s) := by
  have h : ContDiff ℝ ∞ (fun z : E => Real.log (s^2+‖z‖^2)) :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).log (fun z => ne_of_gt (radial_sq_pos hs z))
  exact contDiff_const.mul h

lemma sqrtPotential_smooth {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (sqrtPotential (E := E) s) := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun z => ne_of_gt (radial_sq_pos hs z))

lemma constant_ddc_trace (J : E →L[ℝ] E) (hJJ : ∀ v, J (J v) = -v)
    {f : E → ℝ} {z : E} (hdf : DifferentiableAt ℝ (fderiv ℝ f) z) (v : E) :
    extDeriv (ExteriorForms.dc (fun _ => J) f) z ![v,J v] =
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ f) z (J v) (J v) := by
  rw [ExteriorForms.extDeriv_dc_apply hdf (differentiableAt_const J)]
  have hzero : fderiv ℝ (fun _ : E => J) z = 0 := (hasFDerivAt_const J z).fderiv
  simp [hJJ, hzero]

lemma orthogonal_complex_pair (J : E →L[ℝ] E) (hJJ : ∀ v, J (J v) = -v)
    (hinner : ∀ u v, ⟪J u,J v⟫ = ⟪u,v⟫) (v : E) :
    ⟪v,J v⟫ = 0 ∧ ‖J v‖ = ‖v‖ := by
  constructor
  · have h := hinner v (J v)
    rw [hJJ,inner_neg_right,real_inner_comm] at h
    linarith
  · have h := hinner v v
    simp only [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (J v),norm_nonneg v]

lemma log_ddc_lower (J : E →L[ℝ] E) (hJJ : ∀ v, J (J v) = -v)
    (hinner : ∀ u v, ⟪J u,J v⟫ = ⟪u,v⟫) {s : ℝ} (hs : 0 < s) (z v : E) :
    2*s^2*‖v‖^2/(s^2+‖z‖^2)^2 ≤
      extDeriv (ExteriorForms.dc (fun _ => J) (logPotential s)) z ![v,J v] := by
  have hc : ContDiffAt ℝ 2 (logPotential s) z :=
    contDiffAt_infty.mp (logPotential_smooth hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (logPotential s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [constant_ddc_trace J hJJ hdf]
  obtain ⟨ho,hn⟩ := orthogonal_complex_pair J hJJ hinner v
  exact logPotential_trace_lower hs z v (J v) ho hn

lemma sqrt_ddc_lower (J : E →L[ℝ] E) (hJJ : ∀ v, J (J v) = -v)
    (hinner : ∀ u v, ⟪J u,J v⟫ = ⟪u,v⟫) {s : ℝ} (hs : 0 < s) (z v : E) :
    ‖v‖^2/Real.sqrt (s^2+‖z‖^2) ≤
      extDeriv (ExteriorForms.dc (fun _ => J) (sqrtPotential s)) z ![v,J v] := by
  have hc : ContDiffAt ℝ 2 (sqrtPotential s) z :=
    contDiffAt_infty.mp (sqrtPotential_smooth hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (sqrtPotential s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [constant_ddc_trace J hJJ hdf]
  obtain ⟨ho,hn⟩ := orthogonal_complex_pair J hJJ hinner v
  exact sqrtPotential_trace_lower hs z v (J v) ho hn
end TamingCompatibility.RadialPotential

end

noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma bilinear_diagonal_difference (H : E →L[ℝ] E →L[ℝ] ℝ)
    (J K : E →L[ℝ] E) (v : E) :
    ‖H (J v) (J v) - H (K v) (K v)‖ ≤
      ‖H‖ * ‖J-K‖ * (‖J‖+‖K‖) * ‖v‖^2 := by
  have heq : H (J v) (J v) - H (K v) (K v) =
      H ((J-K) v) (J v) + H (K v) ((J-K) v) := by
    simp only [_root_.sub_apply,map_sub]
    ring
  rw [heq]
  calc
    _ ≤ ‖H ((J-K) v) (J v)‖ + ‖H (K v) ((J-K) v)‖ := norm_add_le _ _
    _ ≤ ‖H‖*‖(J-K) v‖*‖J v‖ + ‖H‖*‖K v‖*‖(J-K) v‖ :=
      add_le_add (H.le_opNorm₂ _ _) (H.le_opNorm₂ _ _)
    _ ≤ ‖H‖*(‖J-K‖*‖v‖)*(‖J‖*‖v‖) + ‖H‖*(‖K‖*‖v‖)*(‖J-K‖*‖v‖) := by
      gcongr
      · exact (J-K).le_opNorm v
      · exact J.le_opNorm v
      · exact K.le_opNorm v
      · exact (J-K).le_opNorm v
    _ = _ := by ring

lemma ddc_gradient_bound (p : E →L[ℝ] ℝ) (D : E →L[ℝ] E →L[ℝ] E)
    (J : E →L[ℝ] E) (v : E) :
    ‖p (D (J v) v - D v (J v))‖ ≤ 2*‖p‖*‖D‖*‖J‖*‖v‖^2 := by
  calc
    _ ≤ ‖p‖ * ‖D (J v) v - D v (J v)‖ := p.le_opNorm _
    _ ≤ ‖p‖ * (‖D (J v) v‖ + ‖D v (J v)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖p‖ * (‖D‖*‖J v‖*‖v‖ + ‖D‖*‖v‖*‖J v‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (D.le_opNorm₂ _ _) (D.le_opNorm₂ _ _)) (norm_nonneg _)
    _ ≤ ‖p‖ * (‖D‖*(‖J‖*‖v‖)*‖v‖ + ‖D‖*‖v‖*(‖J‖*‖v‖)) := by
      gcongr <;> exact J.le_opNorm v
    _ = _ := by ring

lemma ddc_perturbation_bound {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {f : E → ℝ} {z : E} (hdf : DifferentiableAt ℝ (fderiv ℝ f) z)
    (hJ : DifferentiableAt ℝ J z) (hJJ : ∀ v, J z (J z v) = -v)
    (hKK : ∀ v, K (K v) = -v) (v : E) :
    ‖extDeriv (ExteriorForms.dc J f) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) f) z ![v,K v]‖ ≤
      (‖fderiv ℝ (fderiv ℝ f) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ f z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 := by
  rw [ExteriorForms.extDeriv_dc_apply hdf hJ,constant_ddc_trace K hKK hdf,hJJ]
  simp only [map_neg,neg_neg]
  have heq :
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ f) z (J z v) (J z v) +
        fderiv ℝ f z ((fderiv ℝ J z (J z v)) v - (fderiv ℝ J z v) (J z v)) -
        (fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ f) z (K v) (K v)) =
      (fderiv ℝ (fderiv ℝ f) z (J z v) (J z v) - fderiv ℝ (fderiv ℝ f) z (K v) (K v)) +
        fderiv ℝ f z ((fderiv ℝ J z (J z v)) v - (fderiv ℝ J z v) (J z v)) := by ring
  rw [heq]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) z‖*‖J z-K‖*(‖J z‖+‖K‖)*‖v‖^2 +
      2*‖fderiv ℝ f z‖*‖fderiv ℝ J z‖*‖J z‖*‖v‖^2 :=
        add_le_add (bilinear_diagonal_difference _ _ _ _) (ddc_gradient_bound _ _ _ _)
    _ = _ := by ring
end TamingCompatibility.RadialPotential

end

end OAI
