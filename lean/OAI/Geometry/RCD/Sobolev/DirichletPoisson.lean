import OAI.Geometry.RCD.Harmonic.HarmonicGrams
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

namespace OAI

/-!
# Dirichlet solutions from the canonical Cheeger energy

The only quantitative premise is the Poincare estimate on the actual
zero-boundary Sobolev space. Lax--Milgram constructs the solution, including
the harmonic replacement of a given Sobolev function.
-/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def sobolevEnergyForm : SobolevSpace μ hQ →L[ℝ] SobolevSpace μ hQ →L[ℝ] ℝ :=
  innerSL ℝ - (innerSL ℝ).bilinearComp
    (SobolevSpace.toLpCLM μ hQ) (SobolevSpace.toLpCLM μ hQ)

theorem sobolevEnergyForm_apply (f g : SobolevSpace μ hQ) :
    sobolevEnergyForm μ hQ f g = energyForm μ hQ f g := rfl

def dirichletEnergyForm (Ω : Set X) :
    SobolevSpace.dirichlet μ hQ Ω →L[ℝ]
      SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ :=
  (sobolevEnergyForm μ hQ).bilinearComp
    (SobolevSpace.dirichlet μ hQ Ω).subtypeL
    (SobolevSpace.dirichlet μ hQ Ω).subtypeL

theorem dirichletEnergyForm_apply (Ω : Set X)
    (f g : SobolevSpace.dirichlet μ hQ Ω) :
    dirichletEnergyForm μ hQ Ω f g = energyForm μ hQ f.val g.val := rfl

theorem dirichletEnergyForm_isCoercive (Ω : Set X) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val) :
    IsCoercive (dirichletEnergyForm μ hQ Ω) := by
  have hp : 0 < P + 1 := by linarith
  refine ⟨(P + 1)⁻¹, inv_pos.mpr hp, fun f => ?_⟩
  have he : energyForm μ hQ f.val f.val =
      ‖f‖ ^ 2 - ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 := by
    simp only [energyForm, real_inner_self_eq_norm_sq, Submodule.norm_coe]
  change (P + 1)⁻¹ * ‖f‖ * ‖f‖ ≤ energyForm μ hQ f.val f.val
  calc
    _ = ‖f‖ ^ 2 / (P + 1) := by ring
    _ ≤ _ := (div_le_iff₀ hp).mpr (by nlinarith [hbound f])

/-- Existence and uniqueness for every continuous functional on the
zero-boundary Sobolev space. No solution is assumed. -/
theorem existsUnique_dirichlet_solution (Ω : Set X) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (F : SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ) :
    ∃! f : SobolevSpace.dirichlet μ hQ Ω,
      ∀ φ : SobolevSpace.dirichlet μ hQ Ω, energyForm μ hQ f.val φ.val = F φ := by
  let hc := dirichletEnergyForm_isCoercive μ hQ Ω hP hbound
  let e := hc.continuousLinearEquivOfBilin
  let f := e.symm ((InnerProductSpace.toDual ℝ (SobolevSpace.dirichlet μ hQ Ω)).symm F)
  have hf (φ : SobolevSpace.dirichlet μ hQ Ω) : energyForm μ hQ f.val φ.val = F φ := by
    calc
      _ = ⟪e f, φ⟫_ℝ := (hc.continuousLinearEquivOfBilin_apply f φ).symm
      _ = F φ := by simp only [f, ContinuousLinearEquiv.apply_symm_apply,
        InnerProductSpace.toDual_symm_apply]
  refine ⟨f, hf, fun g hg => ?_⟩
  apply e.injective
  apply ext_inner_right ℝ
  intro φ
  rw [hc.continuousLinearEquivOfBilin_apply, hc.continuousLinearEquivOfBilin_apply]
  exact (hg φ).trans (hf φ).symm

/-- The harmonic representative in a given affine Dirichlet class is
constructed from its boundary datum and the Poincare estimate. -/
theorem exists_harmonic_replacement (Ω : Set X) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (u : SobolevSpace μ hQ) :
    ∃ h : SobolevSpace μ hQ, h - u ∈ SobolevSpace.dirichlet μ hQ Ω ∧
      IsSobolevHarmonicOn μ hQ Ω h := by
  let F : SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ :=
    -((sobolevEnergyForm μ hQ u).comp (SobolevSpace.dirichlet μ hQ Ω).subtypeL)
  obtain ⟨v, hv, _⟩ := existsUnique_dirichlet_solution μ hQ Ω hP hbound F
  refine ⟨u + v.val, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using v.property
  · intro φ hφ
    have he := hv ⟨φ, hφ⟩
    change energyForm μ hQ v.val φ = -energyForm μ hQ u φ at he
    rw [energyForm_add_left, he]
    exact add_neg_cancel _

/-- The harmonic representative does not increase Dirichlet energy. -/
theorem harmonic_replacement_energy_le (Ω : Set X) (u h : SobolevSpace μ hQ)
    (hboundary : h - u ∈ SobolevSpace.dirichlet μ hQ Ω)
    (hharm : IsSobolevHarmonicOn μ hQ Ω h) :
    energyForm μ hQ h h ≤ energyForm μ hQ u u := by
  have hz := hharm (h - u) hboundary
  rw [energyForm_sub_right] at hz
  have hs := energyForm_comm μ hQ h u
  have hn : 0 ≤ energyForm μ hQ (h - u) (h - u) := by
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ (h - u))
  simp only [energyForm_sub_left, energyForm_sub_right] at hn
  linarith

end RegularPointCoordinates

end

end OAI
