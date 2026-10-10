import OAI.MeasureTheory.Falconer.Angular.ScaledAngularTransport
import OAI.MeasureTheory.Falconer.Angular.ReciprocalSineBounds
import OAI.MeasureTheory.Falconer.Angular.AngularNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

theorem angular_nonstationary_scale_uniform {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ η, 0 < η → η ≤ 1 →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → tsupport f ⊆ Icc a b →
    (∀ x ∈ tsupport f, η ≤ |Real.sin x|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → η⁻¹ ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ ≤ A*C*(D/(Λ*η))^n := by
  choose Q hQ hbQ using smoothInverseSine_half_derivatives
  let B := scaledAngularTransportCost Q n 0
  have hB : 0 ≤ B := scaledAngularTransportCost_nonneg hQ n 0
  refine ⟨B*(b-a), mul_nonneg hB (sub_nonneg.mpr hab), ?_⟩
  intro η hη hη1 f hf hs haway C D Λ hC hD hΛ hb
  let q : ℝ → ℂ := fun x => (smoothInverseSine (η/2) (half_pos hη) x : ℂ)
  have hq : ContDiff ℝ ∞ q :=
    Complex.ofRealCLM.contDiff.comp (smoothInverseSine_contDiff _ _)
  have hD0 : 0 ≤ D := (le_of_lt (inv_pos.mpr hη)).trans hD
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hqs : ∀ x ∈ tsupport f, (Real.sin x : ℂ)*q x = 1 := by
    intro x hx
    have hh := (smoothInverseSine_half_germ hη (haway x hx)).eq_of_nhds
    dsimp [q]
    exact_mod_cast (show Real.sin x * smoothInverseSine (η/2) (half_pos hη) x = 1 by
      simpa only [mul_comm] using hh)
  have hit := angularTransportIterate_contDiff hq hf n
  have hist : tsupport (angularTransportIterate q n f) ⊆ Icc a b :=
    (angularTransportIterate_support q f n).trans hs
  have hib : ∀ x, ‖angularTransportIterate q n f x‖ ≤ B*C*η⁻¹^n*D^n := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have hbq : ∀ k ≤ n+0, ‖iteratedDeriv k q x‖ ≤ Q k * η⁻¹ * D^k := by
        intro k hk
        calc
          _ ≤ Q k * η⁻¹^(k+1) := hbQ k η hη hη1 x (haway x hx)
          _ = Q k * η⁻¹ * η⁻¹^k := by rw [pow_succ]; ring
          _ ≤ Q k * η⁻¹ * D^k := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hη)) hD k)
            (mul_nonneg (hQ k) (le_of_lt (inv_pos.mpr hη)))
      simpa only [iteratedDeriv_zero, Nat.add_zero] using
        angularTransportIterate_scaled_bound hq hf hQ hC (le_of_lt (inv_pos.mpr hη))
          hD0 n 0 x hbq (fun k hk => hb k (by simpa using hk) x hx)
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hh => hx (angularTransportIterate_support q f n hh)), norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hB hC) (pow_nonneg (le_of_lt (inv_pos.mpr hη)) _))
        (pow_nonneg hD0 _)
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hist hit
  have hsφ : tsupport (φ : ℝ → ℂ) ⊆ Icc a b := by simpa [hφ] using hist
  have hbφ : ∀ x, ‖iteratedDeriv 0 (φ : ℝ → ℂ) x‖ ≤ B*C*η⁻¹^n*D^n := by
    simpa [hφ] using hib
  have hL := compact_derivative_integral_bound φ hab hsφ 0 hbφ
  simp only [iteratedDeriv_zero] at hL
  have hφ' : ∀ x, φ x = angularTransportIterate q n f x := congrFun hφ
  simp only [hφ'] at hL
  have hi : ‖∫ x : ℝ, cosineOscillator Λ x * angularTransportIterate q n f x‖ ≤
      (B*C*η⁻¹^n*D^n)*(b-a) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul, cosineOscillator_norm, one_mul] using hL
  rw [angularTransportIterate_integral hq hf hc hqs Λ n, norm_mul, norm_pow, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΛ] at hi
  have hh := (le_div_iff₀ (pow_pos hΛ n)).mpr (show
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ * Λ^n ≤ (B*C*η⁻¹^n*D^n)*(b-a) by
      simpa only [mul_comm (Λ^n)] using hi)
  apply hh.trans_eq
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow]
  ring

theorem angular_nonstationary_max_scale {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ η, 0 < η → η ≤ 1 →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → tsupport f ⊆ Icc a b →
    (∀ x ∈ tsupport f, η ≤ |Real.sin x|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → 0 < Λ →
    (∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k f x‖ ≤ C*(max D η⁻¹)^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ ≤ A*C*(max D η⁻¹/(Λ*η))^n := by
  obtain ⟨A,hA,hb⟩ := angular_nonstationary_scale_uniform hab n
  exact ⟨A,hA,fun η hη hη1 f hf hs ha C D Λ hC hΛ hfD =>
    hb η hη hη1 hf hs ha hC (le_max_right _ _) hΛ hfD⟩

end PlanarFalconer

end OAI
