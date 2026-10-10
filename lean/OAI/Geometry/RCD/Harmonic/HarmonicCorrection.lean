import OAI.Geometry.RCD.Sobolev.DirichletPoisson

namespace OAI

/-! # Quantitative harmonic corrections of a small divergence defect -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A bound for the energy-dual defect gives a harmonic correction with
that energy bound and the corresponding Poincare `L²` bound. This is the
functional step in the manuscript's radial harmonic correction. -/
theorem exists_harmonic_correction (Ω : Set X) {P D : ℝ}
    (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (g : SobolevSpace μ hQ)
    (hdefect : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (energyForm μ hQ g φ.val) ^ 2 ≤ D * energyForm μ hQ φ.val φ.val) :
    ∃ h : SobolevSpace μ hQ, g - h ∈ SobolevSpace.dirichlet μ hQ Ω ∧
      IsSobolevHarmonicOn μ hQ Ω h ∧
      energyForm μ hQ (g - h) (g - h) ≤ D ∧
      ‖SobolevSpace.toLp μ hQ (g - h)‖ ^ 2 ≤ P * D := by
  obtain ⟨h, hb, hh⟩ := exists_harmonic_replacement μ hQ Ω hP hbound g
  have hmem : g - h ∈ SobolevSpace.dirichlet μ hQ Ω := by
    simpa only [neg_sub] using (SobolevSpace.dirichlet μ hQ Ω).neg_mem hb
  let v : SobolevSpace.dirichlet μ hQ Ω := ⟨g - h, hmem⟩
  let e := energyForm μ hQ v.val v.val
  have he : 0 ≤ e := by
    dsimp [e]
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ v.val)
  have hid : e = energyForm μ hQ g v.val := by
    change energyForm μ hQ (g - h) v.val = _
    rw [energyForm_sub_left, hh v.val v.property, sub_zero]
  have hs : e ^ 2 ≤ D * e := by
    have hs := hdefect v
    rwa [← hid] at hs
  have henergy : e ≤ D := by
    by_cases hz : e = 0
    · simpa only [hz] using hD
    · have hp : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith only [hs]
  refine ⟨h, hmem, hh, henergy, ?_⟩
  exact (hbound v).trans (mul_le_mul_of_nonneg_left henergy hP)

end RegularPointCoordinates

end

end OAI
