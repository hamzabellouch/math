import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricTwoCoreUniform

namespace OAI

/-! # Two-core convergence in the physical periodic-copy coordinates -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem copyFreeKernel_eq_rescaled {r : ℝ} (hr : 0 < r)
    (s₀ η K α γ d₀ q : ℝ) (i : Label) (z : Published.KineticPhase) :
    copyFreeKernel r s₀ η K α γ d₀ q i z =
      JetCoreSheet.rescaledCoreMeasure r η K α γ (JetGeometry.jetScale s₀ η i.annulus/r)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) q i.positive z.1.1
        (JetPeriodicDatum.spatialMap (z.1.2-r⁻¹ • latticeVector i.lattice)) z.2 := by
  rw [copyFreeKernel_eq,JetCoreSheet.dilatedFreeKernel_eq_rescaled hr]

theorem axial_flight_translation (x c w : Velocity) (t : ℝ) :
    axial (x-t • w-c) = axial (x-c)-t*axial w := by
  simp only [axial,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  ring

/-- The selected second label can vary with the intermediate velocity. This
statement covers the retained paths based at one periodic origin. -/
theorem copy_two_core_axial_tendsto {K α γ q a s₀ η d₀ M : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r t₁ t₂ : ℕ → ℝ) (N : ℕ → ℕ) (i₁ : ℕ → Label) (i₂ : ℕ → Velocity → Label)
    (x : ℕ → Velocity) (v : ℕ → Velocity)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht₂ : ∀ n, a ≤ t₂ n) (htt : ∀ n, t₂ n ≤ t₁ n)
    (hi₂ : ∀ n w, (i₂ n w).annulus < N n)
    (hscale : ∀ n w, JetGeometry.jetScale s₀ η (i₂ n w).annulus/r n ≤ M)
    (hcopy : ∀ n w, (i₂ n w).lattice = (i₁ n).lattice)
    (hv : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ w,
      copyFreeKernel (r n) s₀ η K α γ d₀ q (i₂ n w)
        ((t₂ n,x n-(t₁ n-t₂ n) • w),w) univ
      ∂copyFreeKernel (r n) s₀ η K α γ d₀ q (i₁ n) ((t₁ n,x n),v n))
      atTop (𝓝 0) := by
  let X n := JetPeriodicDatum.spatialMap (x n-(r n)⁻¹ • latticeVector (i₁ n).lattice)
  let Y n w := transverse (x n-(t₁ n-t₂ n) • w-(r n)⁻¹ • latticeVector (i₁ n).lattice)
  have hl := JetCoreSheet.geometric_two_core_axial_tendsto hK hα hγ hq₁ hq₂
    ha hs₀ hsmax hη hd₀ hdmax r t₁ t₂ N (fun n => (i₁ n).annulus)
    (fun n w => (i₂ n w).annulus) (fun n => (i₁ n).positive)
    (fun n w => (i₂ n w).positive) X v Y hr hrlim ht₂ htt hi₂ hscale hv
  convert hl using 1
  funext n
  rw [copyFreeKernel_eq_rescaled (hr n)]
  apply lintegral_congr
  intro w
  rw [copyFreeKernel_eq_rescaled (hr n)]
  unfold JetCoreSheet.rescaledBallisticSecondCoreMass
  rw [hcopy n w]
  congr 2
  apply Prod.ext
  · rfl
  · exact axial_flight_translation _ _ _ _

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
