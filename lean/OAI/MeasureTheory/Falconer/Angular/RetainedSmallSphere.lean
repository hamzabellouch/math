import OAI.MeasureTheory.Falconer.Radial.SingleSphereRadial

namespace OAI

/-! # The smaller sphere remains an exact integral

No derivatives of the smaller amplitude are used. Its original value is
retained through Fubini, and only its absolute bound is used afterward.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem single_profile_sum {Ψ : ℝ → ℝ}
    (hsupp : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (s : ℝ) :
    (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e =
      ∑ ε : Bool, ∑ j ∈ Finset.range J,
        stationaryPhase ((R*(stationarySign ε*d))*s)*
          singleSignedRadialCoefficient m j Ψ B e (R*d) ε s := by
  by_cases hs : 0 < s
  · rw [stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ε _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h := singleStationaryPole_radial m j Ψ B e hR hd hs 0 ε
    simpa only [mul_zero,add_zero,stationaryPhase,Complex.ofReal_zero,mul_zero,
      Complex.exp_zero,mul_one] using h
  · have hz : Ψ s = 0 := by
      by_contra hn
      have hp := (hsupp s hn).1
      linarith
    simp only [hz,Complex.ofReal_zero,zero_mul,singleSignedRadialCoefficient,
      PlanarFalconer.radialStationaryProfile,mul_zero,Finset.sum_const_zero]

theorem stationary_profile_regular {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) :
    Measurable (fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e) ∧
      Integrable (fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e) := by
  have he : (fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e) =
      fun s => ∑ ε : Bool, ∑ j ∈ Finset.range J,
        stationaryPhase ((R*(stationarySign ε*d))*s)*
          singleSignedRadialCoefficient m j Ψ B e (R*d) ε s :=
    funext (single_profile_sum hs m J B e hR hd)
  rw [he]
  constructor
  · apply Finset.measurable_sum _
    intro ε _
    apply Finset.measurable_sum _
    intro j _
    apply Continuous.measurable
    apply Continuous.mul
    · unfold stationaryPhase
      fun_prop
    · exact continuous_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _).continuous
  · exact integrable_finsetSum _ (fun ε _ => integrable_finsetSum _ (fun j _ =>
      singleSignedRadial_integrable hΨ hs m j B e (R*d) _ ε))

private theorem radial_sphere_swap {d : ℕ} (F : ℝ → ℂ)
    (hFm : Measurable F) (hFi : Integrable F) (G : Sphere d → ℂ)
    (hG : Measurable G) {C : ℝ} (hGC : ∀ w, ‖G w‖ ≤ C)
    (T : ℝ) (e : Sphere d) :
    (∫ s : ℝ, F s*sphereOscillation (T*s) e G) =
      ∫ w : Sphere d, G w*(∫ s : ℝ,
        F s*stationaryPhase (s*(T*inner ℝ (w : Space d) (e : Space d)))) ∂sphereMeasure d := by
  let H := fun p : ℝ × Sphere d => F p.1*
    (Complex.exp (Complex.I*((T*p.1 : ℝ):ℂ)*(inner ℝ (p.2 : Space d) (e : Space d):ℂ))*G p.2)
  have hm : Measurable H := by
    apply Measurable.mul
    · exact hFm.comp measurable_fst
    · apply Measurable.mul
      · fun_prop
      · exact hG.comp measurable_snd
  have hi : Integrable H (volume.prod (sphereMeasure d)) := by
    apply ((hFi.norm.comp_fst (sphereMeasure d)).mul_const C).mono' hm.aestronglyMeasurable
    filter_upwards with p
    have hphase : ‖Complex.exp
        (Complex.I*((T*p.1 : ℝ):ℂ)*(inner ℝ (p.2 : Space d) (e : Space d):ℂ))‖ = 1 :=
      sphere_phase_norm (T*p.1) e p.2
    dsimp only [H]
    rw [norm_mul,norm_mul,hphase,one_mul]
    exact mul_le_mul_of_nonneg_left (hGC p.2) (norm_nonneg _)
  calc
    _ = ∫ s : ℝ, ∫ w : Sphere d, H (s,w) ∂sphereMeasure d := by
      simp only [sphereOscillation,H,integral_const_mul]
    _ = ∫ w : Sphere d, (∫ s : ℝ, H (s,w)) ∂sphereMeasure d :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      have he : Complex.exp (Complex.I*((T*s : ℝ):ℂ)*
          (inner ℝ (w : Space d) (e : Space d):ℂ)) =
          stationaryPhase (s*(T*inner ℝ (w : Space d) (e : Space d))) := by
        unfold stationaryPhase
        congr 1
        push_cast
        ring
      dsimp only [H]
      rw [he]
      ring

theorem single_sphere_retained_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D R large small E : ℝ, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
      0 ≤ small → 2*small ≤ large → D^2 ≤ R*large →
      (∀ k ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ (e f : Sphere (m+3)) (G : Sphere (m+3) → ℂ), Measurable G →
      (∀ w, ‖G w‖ ≤ E) →
      ‖∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J (R*s*large) B e*
        sphereOscillation (R*s*small) f G‖ ≤
      H*C*E*(sphereMeasure (m+3)).real univ*
        (R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
  obtain ⟨H,hH,hbound⟩ := single_sphere_radial_bound hΨ hs m J q
  refine ⟨H,hH,?_⟩
  intro B hB C D R large small E hC hD hR hl hsmall hsep hscale hb e f G hG hGE
  let F := fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*large) B e
  have hF := stationary_profile_regular hΨ hs m J B e hR hl
  have heq : (fun s => F s*sphereOscillation (R*s*small) f G) =
      fun s => F s*sphereOscillation ((R*small)*s) f G := by
    funext s
    rw [show R*s*small = (R*small)*s by ring]
  change ‖∫ s, F s*sphereOscillation (R*s*small) f G‖ ≤ _
  rw [heq,radial_sphere_swap F hF.1 hF.2 G hG hGE (R*small) f]
  have hbphase (w : Sphere (m+3)) :
      ‖∫ s, F s*stationaryPhase (s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3))))‖ ≤
        H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
    let t := small*inner ℝ (w : Space (m+3)) (f : Space (m+3))
    have ht : |t| ≤ small := by
      dsimp only [t]
      rw [abs_mul,abs_of_nonneg hsmall]
      calc
        _ ≤ small*1 := mul_le_mul_of_nonneg_left
          (by simpa only [sphere_norm,mul_one] using abs_real_inner_le_norm (w : Space (m+3)) (f : Space (m+3))) hsmall
        _ = small := mul_one _
    have h := hbound B hB C D R large small t hC hD hR hl hsep ht hscale hb e
    have hchange := Measure.integral_comp_mul_left
      (fun r : ℝ => (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*large) B e*stationaryPhase (r*t)) R
    have hid : (R⁻¹ • ∫ r, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*large) B e*stationaryPhase (r*t)) =
        ∫ s, F s*stationaryPhase (s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3)))) := by
      have hp : (fun s => (Ψ ((R*s)/R):ℂ)*stationarySphereApprox m J (R*s*large) B e*
          stationaryPhase ((R*s)*t)) =
          fun s => F s*stationaryPhase (s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3)))) := by
        funext s
        rw [mul_div_cancel_left₀ _ hR.ne']
        dsimp only [F,t]
        rw [show R*s*(small*inner ℝ (w : Space (m+3)) (f : Space (m+3))) =
          s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3))) by ring]
      simpa only [abs_of_pos hR,abs_of_pos (inv_pos.mpr hR),hp] using hchange.symm
    rwa [hid] at h
  have hfinal := norm_integral_le_of_norm_le_const (μ := sphereMeasure (m+3))
    (Filter.Eventually.of_forall fun w => (norm_mul (G w) _).le.trans
      (mul_le_mul (hGE w) (hbphase w) (norm_nonneg _)
        ((norm_nonneg (G w)).trans (hGE w))))
  apply hfinal.trans_eq
  ring

end Falconer

end OAI
