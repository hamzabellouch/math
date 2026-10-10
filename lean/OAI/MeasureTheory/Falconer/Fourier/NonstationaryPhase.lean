import OAI.MeasureTheory.Falconer.Fourier.PhaseIntegration
import OAI.MeasureTheory.Falconer.Fourier.SmoothReciprocal
import OAI.MeasureTheory.Falconer.Angular.InheritedCircleRegularity

namespace OAI

/-!
# Uniform nonstationary phase in one angular coordinate

A smooth reciprocal of the phase derivative is constructed from a scalar
bump. A lower bound on the phase derivative and normalized bounds
on its higher derivatives give the required power of `D / (Λ * τ)`.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem phase_nonstationary_from_derivative_bounds
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (φ : ℝ → ℝ) (f : ℝ → ℂ),
      ContDiff ℝ ∞ φ → ContDiff ℝ ∞ f →
      ∀ (a b C D Λ τ : ℝ), a ≤ b → 0 ≤ C → 0 ≤ D → 0 < Λ → 0 < τ →
      tsupport f ⊆ Icc a b →
      (∀ x ∈ tsupport f, τ ≤ |deriv φ x|) →
      (∀ k, 1 ≤ k → k ≤ n → ∀ x ∈ tsupport f,
        |iteratedDeriv k (deriv φ) x| ≤ B k * τ * D^k) →
      (∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
      ‖∫ x, phaseOscillator φ Λ x * f x‖ ≤ A*C*(b-a)*(D/(Λ*τ))^n := by
  choose Q hQ hbound using reciprocal_germ_derivatives B hB
  let A := PlanarFalconer.scaledAngularTransportCost Q n 0
  refine ⟨A,PlanarFalconer.scaledAngularTransportCost_nonneg hQ n 0,?_⟩
  intro φ f hφ hf a b C D Λ τ hab hC hD hΛ hτ hs haway hgb hfb
  have hg : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  let q₀ : ℝ → ℝ := fun x => smoothReciprocal (τ/2) (half_pos hτ) (deriv φ x)
  let q : ℝ → ℂ := fun x => (q₀ x : ℂ)
  have hq₀ : ContDiff ℝ ∞ q₀ := (smoothReciprocal_contDiff _ _).comp hg
  have hq : ContDiff ℝ ∞ q := Complex.ofRealCLM.contDiff.comp hq₀
  have hgerm (x : ℝ) (hx : x ∈ tsupport f) :
      (fun y => q₀ y * deriv φ y) =ᶠ[𝓝 x] (fun _ => 1) :=
    smoothReciprocal_half_germ hg.continuous hτ (haway x hx)
  have hrecip (x : ℝ) (hx : x ∈ tsupport f) : ((deriv φ x : ℝ) : ℂ) * q x = 1 := by
    have hh := (hgerm x hx).eq_of_nhds
    dsimp [q]
    exact_mod_cast (show deriv φ x * q₀ x = 1 by simpa only [mul_comm] using hh)
  have hbq (k : ℕ) (hk : k ≤ n) (x : ℝ) (hx : x ∈ tsupport f) :
      ‖iteratedDeriv k q x‖ ≤ Q k * τ⁻¹ * D^k := by
    change ‖iteratedDeriv k (fun y => (q₀ y : ℂ)) x‖ ≤ _
    rw [PlanarFalconer.iteratedDeriv_ofReal hq₀,Complex.norm_real,Real.norm_eq_abs]
    exact hbound k (deriv φ) q₀ hg hq₀ τ D x hτ hD (haway x hx) (hgerm x hx)
      (fun j hj hjk => hgb j hj (hjk.trans hk) x hx)
  have hh := phase_nonstationary_scale_bound hφ hq hf hab hs hrecip Q hQ hC
    (inv_nonneg.mpr hτ.le) hD hΛ n hbq hfb
  apply hh.trans_eq
  dsimp only [A]
  congr 1
  congr 1
  rw [div_eq_mul_inv,div_eq_mul_inv,mul_inv_rev]
  ring

end Falconer

end OAI
