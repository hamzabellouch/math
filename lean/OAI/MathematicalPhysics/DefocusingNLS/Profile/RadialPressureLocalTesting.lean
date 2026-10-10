import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureQuotientTesting
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialClampedPhase

namespace OAI

/-! Pressure testing needs positivity only on the physical inner ball. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_pressure_local_test_convergence (R l b : ℝ) (hl : 0 ≤ l) (hlR : l ≤ R)
    (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n) (H : ℕ → ℝ → ℝ) (hH : ∀ n, Continuous (H n))
    (hH0 : ∀ n r, r ∈ Icc 0 R → 0 ≤ H n r)
    (hP : ∀ n r, r ∈ Icc 0 R → (H n r)^(p n-1) ≤ 1)
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAz : ∀ r ∈ Icc 0 R, A r ≠ 0)
    (hAD : ∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r)
    (hcore : EqOn A (fun _ => 1) (Icc 0 l))
    (hTA : TendstoUniformlyOn H A atTop (Icc 0 R))
    (hT : TendstoUniformlyOn (fun n r => ∫ t in (0 : ℝ)..r, (H n t)^(p n)*t^11)
      (fun r => b/12*(min r l)^12) atTop (Icc 0 R))
    (φ φ₁ : ℝ → ℝ) (hφ : Continuous φ) (hφ₁ : Continuous φ₁)
    (hφD : ∀ r ∈ Ioo 0 R, HasDerivAt φ (φ₁ r) r) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..R, (H n t)^(p n-1)*φ t*t^11) atTop
      (𝓝 (b*∫ t in (0 : ℝ)..l, φ t*t^11)) := by
  let B := radialClampedAmplitude R A
  have hB : Continuous B := radialClampedAmplitude_continuous R A hA
  have hBz : ∀ r, B r ≠ 0 := fun r => hAz _ (radialClamp_mem R r (hl.trans hlR))
  have hBA : EqOn A B (Icc 0 R) := fun r hr => (radialClampedAmplitude_eq R A r hr).symm
  have hBD : ∀ r ∈ Ioo 0 R, HasDerivAt B (D r) r := by
    intro r hr
    apply (hAD r hr).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact radialClampedAmplitude_eq R A t ⟨ht.1.le,ht.2.le⟩
  have hBc : EqOn B (fun _ => 1) (Icc 0 l) := fun r hr =>
    (hBA ⟨hr.1,hr.2.trans hlR⟩).symm.trans (hcore hr)
  exact radial_pressure_quotient_test_convergence R l b hl hlR p hp H hH hH0 hP
    B D hB hD hBz hBD hBc (hTA.congr_right hBA) hT φ φ₁ hφ hφ₁ hφD

end DefocusingNLS

end OAI
