import OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma control_mono {S T:Finset (ℕ×ℕ)}(h:S⊆T)(W:𝓢(ℝ,ℂ)):
    sourceControl S W≤sourceControl T W:=Seminorm.le_def.mp (Finset.sup_mono h) W

theorem reference_envelopes (a b:ℝ)(ha:0<a)
    (S T Slong:Finset (ℕ×ℕ))(degree n nlong:ℕ)(Cref Dchild Dref:ℝ)
    (hCr:0<Cref)(hDc:0<Dchild)(hDr:0<Dref):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t height:ℝ,0≤height →
      let E:=C*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J;
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*(1+|t|+height)^degree≤E ∧
      Cref*Dchild*(sourceControl Slong W₂)^2*(sourceControl T W₁)^2*
        (1+‖t‖)^(2*nlong)*(1+|t|+height)^(degree+2*n)≤E ∧
      Dref*(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
        (1+‖t‖)^(2*nlong)≤E:=by
  obtain ⟨na,Ta,Ca,hCa,hprof⟩:=independent_profile_control a b ha S
  let U:=((Ta∪T)∪Slong)∪{(0,0)}
  let J:=degree+4*na+2*n+2*nlong
  let C:=1+Ca^2*2^(4*na)+Cref*Dchild+Dref
  have hC:0<C:=by dsimp only [C];positivity
  refine ⟨J,U,C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only
  let H:=1+|t|+height
  let A:=sourceControl U W₁*sourceControl U W₂
  have hH:1≤H:=by dsimp only [H];linarith [abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hA:0≤A:=mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have haU:Ta⊆U:=by intro x hx;simp [U,hx]
  have hTU:T⊆U:=by intro x hx;simp [U,hx]
  have hlU:Slong⊆U:=by intro x hx;simp [U,hx]
  have hzU:(0,0)∈U:=by simp [U]
  have hz:(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁≤sourceControl U W₁:=
    Seminorm.le_def.mp (Finset.le_sup hzU) W₁
  have hp:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S≤Ca*A*(2*H)^(2*na):=by
    apply (hprof W₁ W₂ hs₁ hs₂ t t).trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hCa.le
      exact mul_le_mul (control_mono haU W₁) (control_mono haU W₂)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    · apply pow_le_pow_left₀ (by positivity)
      dsimp only [H]
      simp only [Real.norm_eq_abs]
      linarith [abs_nonneg t]
    · positivity
    · positivity
  have hd:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S^2*H^degree≤
      (Ca^2*2^(4*na))*A^2*H^J:=by
    have hsq:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
    have hmul:=mul_le_mul_of_nonneg_right hsq (pow_nonneg hH0 degree)
    have hid:(Ca*A*(2*H)^(2*na))^2*H^degree=
        (Ca^2*2^(4*na))*A^2*H^(degree+4*na):=by
      rw [mul_pow,mul_pow,←pow_mul,show (2*na)*2=4*na by omega,mul_pow,pow_add]
      ring_nf
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (by positivity))
  have hm:(sourceControl Slong W₂)^2*(sourceControl T W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul (control_mono hTU W₁) (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have he:(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (apply_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul hz (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hheightpow:(1+‖t‖)^(2*nlong)≤H^(2*nlong):=by
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [H]
    simp only [Real.norm_eq_abs]
    linarith
  have hcm: Cref*Dchild≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hce:Dref≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hcd:Ca^2*2^(4*na)≤C:=by dsimp only [C];nlinarith
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg A)) (pow_nonneg hH0 J)),?_,?_⟩
  · calc
      _=(Cref*Dchild)*((sourceControl Slong W₂)^2*(sourceControl T W₁)^2)*
          ((1+‖t‖)^(2*nlong)*H^(degree+2*n)):=by ring
      _≤C*A^2*(H^(2*nlong)*H^(degree+2*n)):=by gcongr
      _≤C*A^2*H^J:=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (sq_nonneg A))
        rw [←pow_add]
        exact pow_le_pow_right₀ hH (by dsimp only [J];omega)
  · calc
      _=Dref*((sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2)*(1+‖t‖)^(2*nlong):=by ring
      _≤C*A^2*H^(2*nlong):=by gcongr
      _≤C*A^2*H^J:=mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (mul_nonneg hC.le (sq_nonneg A))

end SevenEighths.CenteredMomentEnergyReferenceProfileBudget

end

end OAI
