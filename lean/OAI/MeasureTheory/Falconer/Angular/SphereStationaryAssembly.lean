import OAI.MeasureTheory.Falconer.Estimates.OffPoleAmbient

namespace OAI

/-! # Algebra and integration for the two stationary poles

These identities retain the original sphere measure and the original
ambient amplitude. The antipodal contribution uses the same smooth pole
patch as the outgoing contribution.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def antipodalConjugate {d : ℕ} (B : Space d → ℂ) (x : Space d) : ℂ :=
  star (B (-x))

theorem antipodalConjugate_contDiff {d : ℕ} {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (antipodalConjugate B) :=
  Complex.conjCLE.contDiff.comp (hB.comp contDiff_id.neg)

theorem antipodalConjugate_derivative_norm {d : ℕ} (B : Space d → ℂ)
    (k : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ k (antipodalConjugate B) x‖ = ‖iteratedFDeriv ℝ k B (-x)‖ := by
  change ‖iteratedFDeriv ℝ k (Complex.conjLIE ∘
    (B ∘ LinearIsometryEquiv.neg ℝ (E := Space d))) x‖ = _
  rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left,
    (LinearIsometryEquiv.neg ℝ (E := Space d)).norm_iteratedFDeriv_comp_right]
  rfl

theorem sphere_phase_norm {d : ℕ} (Λ : ℝ) (e w : Sphere d) :
    ‖Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ))‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
    sub_zero,Real.exp_zero]

theorem sphereOscillation_integrable {d : ℕ} (Λ : ℝ) (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    Integrable (fun w : Sphere d =>
      Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ))*B w)
        (sphereMeasure d) := by
  obtain ⟨C,hC⟩ := (isCompact_sphere (0 : Space d) 1).exists_bound_of_continuousOn
    hB.continuous.continuousOn
  apply Integrable.of_bound (by fun_prop) C
  filter_upwards with w
  simpa only [norm_mul,sphere_phase_norm,one_mul] using hC w w.property

theorem sphereOscillation_pole_partition {d : ℕ} (Λ : ℝ) (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    sphereOscillation Λ e (fun w => B w) =
      (sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w)+
        sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w))+
      sphereOscillation Λ e (fun w => offPoleLocalizedAmbient e B w) := by
  let F : Sphere d → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ))
  have hfun : (fun w : Sphere d => F w*B w) = fun w =>
      (F w*poleLocalizedAmbient e B w+F w*poleLocalizedAmbient (oppositePole e) B w)+
        F w*offPoleLocalizedAmbient e B w := by
    funext w
    simp only [poleLocalizedAmbient,offPoleLocalizedAmbient,offPoleCutoff,
      Complex.ofReal_sub,Complex.ofReal_one]
    ring
  have hp := sphereOscillation_integrable Λ e (poleLocalizedAmbient_contDiff e hB)
  have hm := sphereOscillation_integrable Λ e (poleLocalizedAmbient_contDiff (oppositePole e) hB)
  have ho := sphereOscillation_integrable Λ e (offPoleLocalizedAmbient_contDiff e hB)
  change (∫ w, F w*B w ∂sphereMeasure d) = _
  rw [hfun]
  calc
    _ = (∫ w, F w*poleLocalizedAmbient e B w+F w*poleLocalizedAmbient (oppositePole e) B w
          ∂sphereMeasure d)+(∫ w, F w*offPoleLocalizedAmbient e B w ∂sphereMeasure d) :=
      integral_add (hp.add hm) ho
    _ = _ := congrArg (fun z => z+(∫ w, F w*offPoleLocalizedAmbient e B w ∂sphereMeasure d))
      (integral_add hp hm)

theorem sphere_stationary_phase_norm (Λ : ℝ) : ‖Complex.exp (Complex.I*(Λ : ℂ))‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,Real.exp_zero]

theorem remove_outgoing_phase (Λ : ℝ) (p I S : ℂ) :
    ‖p*I-Complex.exp (Complex.I*(Λ : ℂ))*S‖ =
      ‖p*Complex.exp (-(Complex.I*(Λ : ℂ)))*I-S‖ := by
  let z := Complex.exp (Complex.I*(Λ : ℂ))
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have he : z*(p*z⁻¹*I-S) = p*I-z*S := by field_simp
  rw [Complex.exp_neg]
  change ‖p*I-z*S‖ = ‖p*z⁻¹*I-S‖
  rw [← he,norm_mul,sphere_stationary_phase_norm,one_mul]

theorem stationary_offPole_scale (m J : ℕ) {D Λ : ℝ} (hD : 1 ≤ D) (hΛ : 1 ≤ Λ) :
    Λ^(((m+2 : ℕ) : ℝ)/2)*(D/Λ)^(J+(m+2)+1) ≤
      Λ^(-(J : ℝ))*D^(2*J+(m+2)+1) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hpow : Λ^(((m+2 : ℕ) : ℝ)/2)*(D/Λ)^(J+(m+2)+1) =
      Λ^(((m+2 : ℕ) : ℝ)/2-((J+(m+2)+1 : ℕ) : ℝ))*D^(J+(m+2)+1) := by
    rw [div_pow,div_eq_mul_inv (D^(J+(m+2)+1)) (Λ^(J+(m+2)+1)),
      ← Real.rpow_natCast Λ (J+(m+2)+1),
      ← Real.rpow_neg hΛp.le]
    rw [show Λ^(((m+2 : ℕ) : ℝ)/2)*
        (D^(J+(m+2)+1)*Λ^(-((J+(m+2)+1 : ℕ) : ℝ))) =
      (Λ^(((m+2 : ℕ) : ℝ)/2)*Λ^(-((J+(m+2)+1 : ℕ) : ℝ)))*D^(J+(m+2)+1) by ring,
      ← Real.rpow_add hΛp]
    congr 1
  rw [hpow]
  apply mul_le_mul
  · apply Real.rpow_le_rpow_of_exponent_le hΛ
    push_cast
    linarith
  · exact pow_le_pow_right₀ hD (by omega)
  · exact pow_nonneg hD0 _
  · exact (Real.rpow_pos_of_pos hΛp _).le

end Falconer

end OAI
