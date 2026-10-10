import OAI.Analysis.LiebThirring.MomentBound

namespace OAI


noncomputable section
namespace SharpLiebThirring.ExtremizerProof
open ConstantProof SpectralProof MeasureTheory Set

/-- Exact substitution `z = tanh (r*x)`; no integrability convention is used to
    guess the integral, since the Jacobian theorem applies to the full line. -/
lemma potential_power_integral {r σ : ℝ} (hr : 0 < r) :
    (∫ x, (potential r x)^(1+σ)) = (r+1)^(1+σ)/r * betaAction σ := by
  let f : ℝ → ℝ := fun x ↦ Real.tanh (r*x)
  have hf' (x : ℝ) : HasDerivAt f ((Real.cosh (r*x))⁻¹^2*r) x := by
    convert! (tanh_hasDerivAt (r*x)).comp x ((hasDerivAt_id x).const_mul r) using 1
    simp
  have hinj : Function.Injective f := by
    intro x y h
    exact mul_left_cancel₀ hr.ne' (Real.tanh_injective h)
  have himg : f '' univ = Ioo (-1 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
    · intro hz
      obtain ⟨x,_,hx⟩ := Real.tanh_surjOn hz
      refine ⟨x/r,mem_univ _,?_⟩
      dsimp [f]
      rw [mul_div_cancel₀ _ hr.ne',hx]
  have hj := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hf' x).hasDerivWithinAt) hinj.injOn (fun z : ℝ ↦ (1-z^2)^σ)
  rw [himg,setIntegral_univ] at hj
  have halg (x : ℝ) : |(Real.cosh (r*x))⁻¹^2*r| * (1-f x^2)^σ =
      r*((Real.cosh (r*x))⁻¹^2)^(1+σ) := by
    have hs : 0 < (Real.cosh (r*x))⁻¹^2 := by positivity
    have ht : 1-f x^2 = (Real.cosh (r*x))⁻¹^2 := by
      dsimp [f]
      linarith [tanh_sq_add_sech_sq (r*x)]
    rw [abs_of_pos (mul_pos hs hr),ht,Real.rpow_add hs,Real.rpow_one]
    ring
  have hj' : betaAction σ = r*∫ x, ((Real.cosh (r*x))⁻¹^2)^(1+σ) := by
    rw [betaAction,intervalIntegral.integral_of_le (by norm_num),integral_Ioc_eq_integral_Ioo,hj]
    simp only [smul_eq_mul,halg]
    exact integral_const_mul _ _
  have hi : (∫ x, (potential r x)^(1+σ)) =
      (r+1)^(1+σ)*∫ x, ((Real.cosh (r*x))⁻¹^2)^(1+σ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      dsimp only [potential]
      rw [Real.mul_rpow (by linarith : 0 ≤ r+1) (sq_nonneg _)])
  rw [hi,hj']
  field_simp

lemma young_times_extremizer_factor {σ : ℝ} (hσ : 0 < σ) :
    actionYoungConstant σ * ((σ⁻¹+1)^(1+σ)/σ⁻¹) = 1 := by
  have hp : 0 < 1+σ := by linarith
  have he : σ⁻¹+1 = (1+σ)/σ := by field_simp
  rw [actionYoungConstant,he,Real.div_rpow hp.le hσ.le]
  rw [Real.rpow_add hσ,Real.rpow_one]
  have hn : (1+σ)^(1+σ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have hn' : σ^σ ≠ 0 := (Real.rpow_pos_of_pos hσ _).ne'
  field_simp

lemma sharp_times_extremizer_integral {γ : ℝ} (hγ : 1/2 < γ) :
    sharpConstant γ * (∫ x, (equalityPotential γ x)^(γ+1/2)) = 1 := by
  have hσ : 0 < γ-1/2 := by linarith
  have hr : 0 < (γ-1/2)⁻¹ := inv_pos.mpr hσ
  have hpow : γ+1/2 = 1+(γ-1/2) := by ring
  change sharpConstant γ * (∫ x, (potential ((γ-1/2)⁻¹) x)^(γ+1/2)) = 1
  rw [hpow,potential_power_integral hr]
  have hc := action_constant_eq_sharp hσ
  rw [sub_add_cancel] at hc
  rw [← hc]
  calc
    _ = actionYoungConstant (γ-1/2)*(((γ-1/2)⁻¹+1)^(1+(γ-1/2))/(γ-1/2)⁻¹) := by
      rw [mul_comm _ (betaAction (γ-1/2)),← mul_assoc,div_mul_cancel₀ _ (betaAction_pos hσ).ne']
    _ = 1 := young_times_extremizer_factor hσ

end SharpLiebThirring.ExtremizerProof

end

end OAI
