import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1GraphCore

namespace OAI

/-! Continuous kinetic-plus-bounded-operator forms on the full H1 graph. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

abbrev H1Coordinates (n : ℕ) := H1Index n → Lp ℂ 2 (volume : Measure (Configuration n))

def graphMass {n : ℕ} (f : H1Coordinates n) : ℝ :=
  ∑ s, ‖f (Sum.inl s)‖^2

def graphKinetic {n : ℕ} (f : H1Coordinates n) : ℝ :=
  (1/2 : ℝ) * ∑ s, ∑ a, ‖f (Sum.inr (s,a))‖^2

theorem h1Coordinates_norm_sq {n : ℕ} (u : Coulomb.H1Vector n) (a : H1Index n) :
    ‖h1Coordinates u a‖^2 = ∫ x, ‖h1CoordinateFunction u a x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(h1Coordinate_memLp u a).coeFn_toLp] with x hx
  simpa only [real_inner_self_eq_norm_sq, h1Coordinates] using congrArg (fun z : ℂ => ‖z‖^2) hx

theorem mass_eq_graphMass {n : ℕ} (u : Coulomb.H1Vector n) :
    Coulomb.mass u = graphMass (h1Coordinates u) := by
  simp only [Coulomb.mass, graphMass, h1Coordinates_norm_sq, h1CoordinateFunction]

theorem kinetic_eq_graphKinetic {n : ℕ} (u : Coulomb.H1Vector n) :
    Coulomb.kinetic u = graphKinetic (h1Coordinates u) := by
  simp only [Coulomb.kinetic, graphKinetic, h1Coordinates_norm_sq, h1CoordinateFunction]

theorem graphMass_continuous (n : ℕ) : Continuous (@graphMass n) :=
  continuous_finsetSum _ (fun s _ => (continuous_apply (Sum.inl s)).norm.pow 2)

theorem graphKinetic_continuous (n : ℕ) : Continuous (@graphKinetic n) :=
  continuous_const.mul (continuous_finsetSum _ (fun s _ =>
    continuous_finsetSum _ (fun a _ => (continuous_apply (Sum.inr (s,a))).norm.pow 2)))

def graphBoundedForm {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (f : H1Coordinates n) : ℝ :=
  graphKinetic f + ∑ s, inner ℝ (f (Sum.inl s)) (A (f (Sum.inl s)))

theorem graphBoundedForm_continuous {n : ℕ}
    (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) : Continuous (graphBoundedForm A) :=
  (graphKinetic_continuous n).add (continuous_finsetSum _ (fun s _ =>
    (continuous_apply (Sum.inl s)).inner (A.continuous.comp (continuous_apply (Sum.inl s)))))

/-- A compact-test lower bound for an actual bounded L2 operator extends
with the kinetic energy to the entire declared weak-H1 domain. -/
theorem boundedForm_lower_of_compact (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (A : Lp ℂ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Configuration n))) (E : ℝ)
    (hcompact : ∀ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) →
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) →
      E*Coulomb.mass v ≤ graphBoundedForm A (h1Coordinates v))
    (u : Coulomb.H1Vector n) : E*Coulomb.mass u ≤ graphBoundedForm A (h1Coordinates u) := by
  have hc : Continuous (fun f : H1Coordinates n => graphBoundedForm A f - E*graphMass f) :=
    (graphBoundedForm_continuous A).sub (continuous_const.mul (graphMass_continuous n))
  have h := h1_continuous_nonnegative_of_compact hpublished
    (fun f => graphBoundedForm A f - E*graphMass f) hc
    (fun v hv hd => by
      rw [← mass_eq_graphMass]
      exact sub_nonneg.mpr (hcompact v hv hd)) u
  rw [← mass_eq_graphMass] at h
  exact sub_nonneg.mp h

end ContinuumCoulomb

end

end OAI
