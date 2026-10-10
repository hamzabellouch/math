import OAI.MeasureTheory.Falconer.Angular.AngularIntegrationByParts
import OAI.MeasureTheory.Falconer.Angular.ScaledAngularTransport

namespace OAI

/-!
# Coordinate integration by parts for the angular localization

For an arbitrary smooth real phase in a sphere chart, coordinate integration
by parts gives a scale bound through the reciprocal phase derivative.
The transport derivative identities concern functions on the real line and
are independent of the ambient sphere dimension.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable def phaseOscillator (φ : ℝ → ℝ) (Λ x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (Λ : ℂ) * (φ x : ℂ))

theorem phaseOscillator_norm (φ : ℝ → ℝ) (Λ x : ℝ) :
    ‖phaseOscillator φ Λ x‖ = 1 := by
  simp [phaseOscillator, Complex.norm_exp]

theorem phaseOscillator_hasDerivAt {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ)
    (Λ x : ℝ) : HasDerivAt (phaseOscillator φ Λ)
      (Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) x := by
  have hh := (((hφ x).hasDerivAt.ofReal_comp).const_mul (Complex.I * (Λ : ℂ))).cexp
  convert hh using 1
  · rfl
  · dsimp [phaseOscillator]
    ring

theorem phase_integration_by_parts {φ : ℝ → ℝ} {q f : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f)
    (hrecip : ∀ x ∈ tsupport f, ((deriv φ x : ℝ) : ℂ) * q x = 1) (Λ : ℝ) :
    (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransport q f x) =
      (-Complex.I * (Λ : ℂ)) * ∫ x, phaseOscillator φ Λ x * f x := by
  let v : ℝ → ℂ := fun x => q x * f x
  have hv : ContDiff ℝ ∞ v := hq.mul hf
  have hvc : HasCompactSupport v := hc.mul_left
  have hE : Continuous (phaseOscillator φ Λ) := by
    unfold phaseOscillator
    fun_prop
  have hv' : Continuous (PlanarFalconer.angularTransport q f) :=
    hv.continuous_deriv (by simp)
  have hi₁ : Integrable (fun x => phaseOscillator φ Λ x * PlanarFalconer.angularTransport q f x) :=
    (hE.mul hv').integrable_of_hasCompactSupport hvc.deriv.mul_left
  have hE' : Continuous (fun x =>
      Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (hφ.continuous_deriv (by simp)))).mul hE
  have hi₂ : Integrable (fun x =>
      (Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) * v x) :=
    (hE'.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hi₃ : Integrable (fun x => phaseOscillator φ Λ x * v x) :=
    (hE.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := phaseOscillator φ Λ) (v := v) (v' := PlanarFalconer.angularTransport q f)
    (fun x _ => phaseOscillator_hasDerivAt (hφ.differentiable (by simp)) Λ x)
    (fun x _ => (hv.differentiable (by simp)).differentiableAt.hasDerivAt) hi₁ hi₂ hi₃
  change (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransport q f x) = _ at hh
  rw [hh]
  have he : (fun x =>
      (Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) * v x) =
      fun x => (Complex.I * (Λ : ℂ)) * (phaseOscillator φ Λ x * f x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · dsimp [v]
      calc
        _ = (Complex.I * (Λ : ℂ)) * phaseOscillator φ Λ x *
            (((deriv φ x : ℝ) : ℂ) * q x) * f x := by ring
        _ = _ := by rw [hrecip x hx]; ring
    · simp [v, image_eq_zero_of_notMem_tsupport hx]
  rw [he, integral_const_mul]
  ring

theorem phase_transport_iterate_integral {φ : ℝ → ℝ} {q f : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f)
    (hrecip : ∀ x ∈ tsupport f, ((deriv φ x : ℝ) : ℂ) * q x = 1) (Λ : ℝ) (n : ℕ) :
    (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransportIterate q n f x) =
      (-Complex.I * (Λ : ℂ))^n * ∫ x, phaseOscillator φ Λ x * f x := by
  induction n with
  | zero => simp [PlanarFalconer.angularTransportIterate]
  | succ n ih =>
    have hi := PlanarFalconer.angularTransportIterate_contDiff hq hf n
    have hs := PlanarFalconer.angularTransportIterate_support q f n
    have hc' : HasCompactSupport (PlanarFalconer.angularTransportIterate q n f) :=
      hc.mono' (fun _ hx => hs (subset_closure hx))
    have hh := phase_integration_by_parts hφ hq hi hc'
      (fun x hx => hrecip x (hs hx)) Λ
    change (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransport q
      (PlanarFalconer.angularTransportIterate q n f) x) = _
    rw [hh, ih, pow_succ]
    ring

/-- Uniform coordinate IBP. The reciprocal derivative has size `U` and
derivative scale `D`; the gain per integration is `U*D/Λ`. -/
theorem phase_nonstationary_scale_bound {φ : ℝ → ℝ} {q f : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a ≤ b) (hs : tsupport f ⊆ Icc a b)
    (hrecip : ∀ x ∈ tsupport f, ((deriv φ x : ℝ) : ℂ) * q x = 1)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 ≤ Q k)
    {C U D Λ : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ U) (hD : 0 ≤ D) (hΛ : 0 < Λ)
    (n : ℕ)
    (hbq : ∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k q x‖ ≤ Q k * U * D^k)
    (hbf : ∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k f x‖ ≤ C * D^k) :
    ‖∫ x, phaseOscillator φ Λ x * f x‖ ≤
      (PlanarFalconer.scaledAngularTransportCost Q n 0 * C * (b-a)) * (U*D/Λ)^n := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have ht := PlanarFalconer.angularTransportIterate_contDiff hq hf n
  have hts := (PlanarFalconer.angularTransportIterate_support q f n).trans hs
  let A := PlanarFalconer.scaledAngularTransportCost Q n 0
  have hA : 0 ≤ A := PlanarFalconer.scaledAngularTransportCost_nonneg hQ n 0
  have hbound (x : ℝ) : ‖PlanarFalconer.angularTransportIterate q n f x‖ ≤ A*C*U^n*D^n := by
    by_cases hx : x ∈ tsupport f
    · simpa only [iteratedDeriv_zero, Nat.add_zero] using
        PlanarFalconer.angularTransportIterate_scaled_bound hq hf hQ hC hU hD n 0 x
          (fun k hk => hbq k (by simpa using hk) x hx)
          (fun k hk => hbf k (by simpa using hk) x hx)
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hh => hx (PlanarFalconer.angularTransportIterate_support q f n hh)), norm_zero]
      positivity
  obtain ⟨ψ,hψ⟩ := PlanarFalconer.compact_smooth_to_schwartz hts ht
  have hψs : tsupport (ψ : ℝ → ℂ) ⊆ Icc a b := by simpa [hψ] using hts
  have hψb : ∀ x, ‖iteratedDeriv 0 (ψ : ℝ → ℂ) x‖ ≤ A*C*U^n*D^n := by
    simpa [hψ] using hbound
  have hint := PlanarFalconer.compact_derivative_integral_bound ψ hab hψs 0 hψb
  simp only [iteratedDeriv_zero] at hint
  have hψ' : ∀ x, ψ x = PlanarFalconer.angularTransportIterate q n f x := congrFun hψ
  simp only [hψ'] at hint
  have hi : ‖∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransportIterate q n f x‖ ≤
      (A*C*U^n*D^n)*(b-a) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul, phaseOscillator_norm, one_mul] using hint
  rw [phase_transport_iterate_integral hφ hq hf hc hrecip Λ n, norm_mul,
    norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΛ] at hi
  have hh : ‖∫ x, phaseOscillator φ Λ x * f x‖ ≤ (A*C*U^n*D^n)*(b-a)/Λ^n :=
    (le_div_iff₀ (pow_pos hΛ n)).mpr (by simpa only [mul_comm (Λ^n)] using hi)
  apply hh.trans_eq
  dsimp [A]
  rw [div_pow, mul_pow]
  ring

end Falconer

end OAI
