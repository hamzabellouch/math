import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerShootingFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStationaryReconstruction

namespace OAI

/-! The selected shooting profile solves the actual stationary equation on the inner ball. -/

open Set
namespace DefocusingNLS

noncomputable def radialShootingA (n : ℕ) : ℝ :=
  1/(2*((n+radialInnerShootingThreshold : ℕ) : ℝ))

theorem radialShootingInner_power_pos (n : ℕ) (w : RadialShootingDisk) :
    0 < n+radialInnerShootingThreshold := by
  have h := (radialShootingInnerData n w).hp
  rw [radialShootingInnerData_p] at h
  omega

theorem radialShootingInner_c_eq (n : ℕ) (w : RadialShootingDisk) :
    (radialShootingInnerData n w).c=6-2*radialShootingA n := by
  rw [radialShootingInnerData_c]
  unfold radialShootingA
  field_simp

theorem radialShootingInnerComplex_eq (n : ℕ) (w : RadialShootingDisk) :
    radialShootingInnerComplex n w=
      radialInnerComplex innerBoundaryRadius (radialShootingA n) (radialShootingInnerAmplitude n w) := by
  unfold radialShootingInnerComplex radialInnerComplex radialInnerPhase
  rw [radialShootingInner_c_eq]

theorem radialShootingInner_positive (n : ℕ) (w : RadialShootingDisk) (r : ℝ)
    (hr : r ∈ Icc 0 innerBoundaryRadius) : 0 < radialShootingInnerAmplitude n w r := by
  have hh := (radialShootingInnerAmplitude_spec n w).2.2.2.2.1 r
    (by simpa only [radialShootingInnerData_R] using hr)
  linarith [(radialShootingInnerData n w).lo_lower,hh.1.1]

theorem radialShootingInner_differentiable (n : ℕ) (w : RadialShootingDisk) :
    Differentiable ℝ (radialShootingInnerComplex n w) := by
  have hH := (radialShootingInnerAmplitude_spec n w).1
  have hφ := radialPhase_differentiable (radialShootingInnerData n w).c
    (radialClampedAmplitude innerBoundaryRadius (radialShootingInnerAmplitude n w))
    (radialClampedAmplitude_continuous _ _ hH.continuous)
    (fun r => (radialShootingInner_positive n w _
      (radialClamp_mem innerBoundaryRadius r (by linarith [innerBoundaryRadius_bounds.1]))).ne')
  exact fun r => (radialPolar_hasDerivAt _ _ hH hφ r).differentiableAt

theorem radialShootingInner_origin (n : ℕ) (w : RadialShootingDisk) :
    0 < (radialShootingInnerComplex n w 0).re ∧
      (radialShootingInnerComplex n w 0).im=0 := by
  rw [radialShootingInnerComplex_eq,radialInnerComplex_origin]
  exact ⟨radialShootingInner_positive n w 0 ⟨le_rfl,by linarith [innerBoundaryRadius_bounds.1]⟩,rfl⟩

theorem radialShootingInner_norm (n : ℕ) (w : RadialShootingDisk) (r : ℝ)
    (hr : r ∈ Icc 0 innerBoundaryRadius) :
    ‖radialShootingInnerComplex n w r‖=radialShootingInnerAmplitude n w r := by
  rw [radialShootingInnerComplex_eq]
  exact radialInnerComplex_norm _ _ _ _ (radialShootingInner_positive n w r hr).le

theorem radialShootingInner_stationary (n : ℕ) (w : RadialShootingDisk) :
    ∀ r ∈ Ioo 0 innerBoundaryRadius,
      deriv (deriv (radialShootingInnerComplex n w)) r+
        (11/r : ℝ)*deriv (radialShootingInnerComplex n w) r+
        Complex.I*((r/2 : ℝ)*deriv (radialShootingInnerComplex n w) r+
          (radialShootingA n : ℂ)*radialShootingInnerComplex n w r)+
        (radialShootingB w : ℂ)*radialShootingInnerComplex n w r=
      (‖radialShootingInnerComplex n w r‖^(2*(n+radialInnerShootingThreshold)) : ℝ)*
        radialShootingInnerComplex n w r := by
  let P := radialShootingInnerData n w
  have hH := radialShootingInnerAmplitude_spec n w
  have hEq := hH.2.2.2.2.2
  simp only [radialShootingInnerData_R,radialShootingInner_c_eq,radialShootingInnerData_b] at hEq
  have hD := hH.2.1
  simp only [radialShootingInnerData_R] at hD
  have hh := radialInnerComplex_stationary P.p (by have := P.hp; omega)
    innerBoundaryRadius (radialShootingA n) (radialShootingB w)
    (by linarith [innerBoundaryRadius_bounds.1]) (radialShootingInnerAmplitude n w) hH.1
    (radialShootingInner_positive n w) hD hEq
  intro r hr
  rw [radialShootingInner_norm n w r ⟨hr.1.le,hr.2.le⟩,radialShootingInnerComplex_eq]
  simpa only [P,radialShootingInnerData_p,Nat.add_sub_cancel] using hh r hr

end DefocusingNLS

end OAI
