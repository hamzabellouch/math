import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.BoundedPotentialOperator

namespace OAI

/-! Finite orbital penalties pass from compact tests to the complete weak-H1
domain without asking approximants to preserve exact orthogonality. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def graphOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) (f : H1Coordinates n) : ℝ :=
  ∑ s, ∑ i, ‖inner ℂ (ψ i) (f (Sum.inl s))‖^2

theorem graphOrbitalMass_continuous {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) :
    Continuous (graphOrbitalMass ψ) :=
  continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun _i _ =>
    (continuous_const.inner (continuous_apply (Sum.inl s))).norm.pow 2))

theorem graphOrbitalMass_eq_zero {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) (f : H1Coordinates n)
    (horth : ∀ s i, inner ℂ (ψ i) (f (Sum.inl s)) = 0) :
    graphOrbitalMass ψ f = 0 := by
  simp only [graphOrbitalMass, horth, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero]

/-- The finite projection term is continuous on the same graph as the
kinetic and bounded potential terms. -/
theorem boundedPotential_projection_lower_of_compact
    (hpublished : PublishedSobolevSmoothDensity) {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ x, |V x| ≤ B)
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) (E κ : ℝ)
    (hcompact : ∀ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) →
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) →
      E*Coulomb.mass v - κ*graphOrbitalMass ψ (h1Coordinates v) ≤ boundedPotentialForm V v)
    (u : Coulomb.H1Vector n) :
    E*Coulomb.mass u - κ*graphOrbitalMass ψ (h1Coordinates u) ≤ boundedPotentialForm V u := by
  let A := BoundedPotential.operator V hV B hB
  let F : H1Coordinates n → ℝ := fun f =>
    graphBoundedForm A f - E*graphMass f + κ*graphOrbitalMass ψ f
  have hF : Continuous F :=
    ((graphBoundedForm_continuous A).sub
      (continuous_const.mul (graphMass_continuous n))).add
      (continuous_const.mul (graphOrbitalMass_continuous ψ))
  have h := h1_continuous_nonnegative_of_compact hpublished F hF
    (fun v hv hd => by
      dsimp [F, A]
      rw [← boundedPotentialForm_eq_graph V hV B hB, ← mass_eq_graphMass]
      linarith [hcompact v hv hd]) u
  dsimp [F, A] at h
  rw [← boundedPotentialForm_eq_graph V hV B hB, ← mass_eq_graphMass] at h
  linarith

theorem boundedPotential_complement_lower_of_compact
    (hpublished : PublishedSobolevSmoothDensity) {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ x, |V x| ≤ B)
    (ψ : ι → Lp ℂ 2 (volume : Measure (Configuration n))) (E κ : ℝ)
    (hcompact : ∀ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) →
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) →
      E*Coulomb.mass v - κ*graphOrbitalMass ψ (h1Coordinates v) ≤ boundedPotentialForm V v)
    (u : Coulomb.H1Vector n)
    (horth : ∀ s i, inner ℂ (ψ i) (h1Coordinates u (Sum.inl s)) = 0) :
    E*Coulomb.mass u ≤ boundedPotentialForm V u := by
  have h := boundedPotential_projection_lower_of_compact hpublished V hV B hB ψ E κ hcompact u
  simpa only [graphOrbitalMass_eq_zero ψ _ horth, mul_zero, sub_zero] using h

end ContinuumCoulomb

end

end OAI
