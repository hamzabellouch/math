import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerShootingData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledComplexParameter

namespace OAI

/-! The canonical nonlinear inner family and its continuous complex boundary map. -/

open Set Filter
namespace DefocusingNLS

noncomputable def radialInnerShootingThreshold : ℕ := Classical.choose exists_radialInnerShootingData

theorem radialInnerShootingData_exists (n : ℕ) (w : RadialShootingDisk) :
    ∃ P : RadialInnerData, P.p=2*(n+radialInnerShootingThreshold)+1 ∧ P.R=innerBoundaryRadius ∧
      P.lo=‖(radialFreeInnerJet w innerBoundaryRadius).1‖ ∧
      P.c=6-1/((n+radialInnerShootingThreshold : ℕ) : ℝ) ∧ P.b=radialShootingB w :=
  Classical.choose_spec exists_radialInnerShootingData (n+radialInnerShootingThreshold)
    (by unfold radialInnerShootingThreshold; omega) w

noncomputable def radialShootingInnerData (n : ℕ) (w : RadialShootingDisk) : RadialInnerData :=
  Classical.choose (radialInnerShootingData_exists n w)

theorem radialShootingInnerData_p (n : ℕ) (w : RadialShootingDisk) :
    (radialShootingInnerData n w).p=2*(n+radialInnerShootingThreshold)+1 :=
  (Classical.choose_spec (radialInnerShootingData_exists n w)).1

theorem radialShootingInnerData_R (n : ℕ) (w : RadialShootingDisk) :
    (radialShootingInnerData n w).R=innerBoundaryRadius :=
  (Classical.choose_spec (radialInnerShootingData_exists n w)).2.1

theorem radialShootingInnerData_lo (n : ℕ) (w : RadialShootingDisk) :
    (radialShootingInnerData n w).lo=‖(radialFreeInnerJet w innerBoundaryRadius).1‖ :=
  (Classical.choose_spec (radialInnerShootingData_exists n w)).2.2.1

theorem radialShootingInnerData_c (n : ℕ) (w : RadialShootingDisk) :
    (radialShootingInnerData n w).c=6-1/((n+radialInnerShootingThreshold : ℕ) : ℝ) :=
  (Classical.choose_spec (radialInnerShootingData_exists n w)).2.2.2.1

theorem radialShootingInnerData_b (n : ℕ) (w : RadialShootingDisk) :
    (radialShootingInnerData n w).b=radialShootingB w :=
  (Classical.choose_spec (radialInnerShootingData_exists n w)).2.2.2.2

noncomputable def radialShootingInnerAmplitude (n : ℕ) (w : RadialShootingDisk) : ℝ → ℝ :=
  Classical.choose (exists_radial_coupled_profile (radialShootingInnerData n w))

theorem radialShootingInnerAmplitude_spec (n : ℕ) (w : RadialShootingDisk) :
    let P := radialShootingInnerData n w
    let H := radialShootingInnerAmplitude n w
    RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H :=
  Classical.choose_spec (exists_radial_coupled_profile (radialShootingInnerData n w))

noncomputable def radialShootingInnerComplex (n : ℕ) (w : RadialShootingDisk) : ℝ → ℂ :=
  radialPolar (radialShootingInnerAmplitude n w)
    (radialPhase (radialShootingInnerData n w).c
      (radialClampedAmplitude innerBoundaryRadius (radialShootingInnerAmplitude n w)))

noncomputable def radialShootingInnerBoundary (n : ℕ) (w : RadialShootingDisk) : ℂ × ℂ :=
  (radialShootingInnerComplex n w innerBoundaryRadius,
    deriv (radialShootingInnerComplex n w) innerBoundaryRadius)

theorem continuous_radialShootingInnerBoundary (n : ℕ) :
    Continuous (radialShootingInnerBoundary n) := by
  apply SeqContinuous.continuous
  intro w w₀ hw
  have hlo : Tendsto (fun i => (radialShootingInnerData n (w i)).lo) atTop
      (nhds (radialShootingInnerData n w₀).lo) := by
    simpa only [radialShootingInnerData_lo] using!
      continuous_radialFreeInner_boundary.fst.norm.continuousAt.tendsto.comp hw
  have hc : Tendsto (fun i => (radialShootingInnerData n (w i)).c) atTop
      (nhds (radialShootingInnerData n w₀).c) := by
    simp only [radialShootingInnerData_c]
    exact tendsto_const_nhds
  have hbc : Continuous radialShootingB := by unfold radialShootingB; fun_prop
  have hb : Tendsto (fun i => (radialShootingInnerData n (w i)).b) atTop
      (nhds (radialShootingInnerData n w₀).b) := by
    simpa only [radialShootingInnerData_b] using! hbc.continuousAt.tendsto.comp hw
  have hh := radial_coupled_complex_parameter_limit (radialShootingInnerData n w₀)
    (fun i => radialShootingInnerData n (w i))
    (fun i => by rw [radialShootingInnerData_p,radialShootingInnerData_p])
    (fun i => by rw [radialShootingInnerData_R,radialShootingInnerData_R]) hlo hc hb
    (radialShootingInnerAmplitude n w₀) (fun i => radialShootingInnerAmplitude n (w i))
    (radialShootingInnerAmplitude_spec n w₀) (fun i => radialShootingInnerAmplitude_spec n (w i))
  simpa only [radialShootingInnerData_R,radialShootingInnerBoundary,radialShootingInnerComplex] using! hh

end DefocusingNLS

end OAI
