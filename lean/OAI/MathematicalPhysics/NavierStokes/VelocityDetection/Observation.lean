import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model

namespace OAI

noncomputable section
namespace VelocityDetection.Observation
open scoped BigOperators Topology ContDiff
open Set Function Filter
open MeasureTheory

def join (X : Coord 2) (z : ℝ) : Coord 3 := ![X 0, X 1, z]

@[simp] theorem horizontal_join (X : Coord 2) (z : ℝ) : horizontal (join X z) = X := by
  ext i
  fin_cases i <;> simp [horizontal, join]

def torusEvent (u : VectorField 3) : Prop :=
  letI := neZeroThree
  ∃ t : ℝ, 0 ≤ t ∧ ∃ x : Coord 3,
    1 / ((32 : ℕ) : ℝ) < x 1 ∧ x 1 < 1 / ((8 : ℕ) : ℝ) ∧ (1 / ((2 : ℕ) : ℝ) : ℝ) < u t x 2

def upperHalfPlane : Set (Coord 2) := {X | 0 < X 1}

def planeMass (u : VectorField 3) (t : ℝ) : ℝ :=
  letI := neZeroThree
  ∫ q in upperHalfPlane ×ˢ Ioc (0 : ℝ) 1,
    u t (join q.1 q.2) 2 ∂(volume.prod volume)

def planeEvent (u : VectorField 3) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ (1 / ((2 : ℕ) : ℝ) : ℝ) < planeMass u t

theorem normalized_vertical_period (ρ : Coord 2 → ℝ) :
    (∫ q in upperHalfPlane ×ˢ Ioc (0 : ℝ) 1, ρ q.1 ∂(volume.prod volume)) =
      ∫ X in upperHalfPlane, ρ X := by
  have h := setIntegral_prod_mul (μ := (volume : Measure (Coord 2)))
    (ν := (volume : Measure ℝ)) ρ (fun _ : ℝ => (1 : ℝ)) upperHalfPlane (Ioc (0 : ℝ) 1)
  simpa using h

@[simp] theorem planeMass_lift (a : VectorField 2) (w : ScalarField 2) (t : ℝ) :
    planeMass (liftVelocity a w) t = ∫ X in upperHalfPlane, w t X := by
  simp only [planeMass, liftVelocity, Matrix.cons_val, horizontal_join]
  exact normalized_vertical_period (w t)

theorem planeEvent_lift (a : VectorField 2) (w : ScalarField 2) :
    planeEvent (liftVelocity a w) ↔
      ∃ t : ℝ, 0 ≤ t ∧ (1 / 2 : ℝ) < ∫ X in upperHalfPlane, w t X := by
  simp only [planeEvent, planeMass_lift, Nat.cast_ofNat]

theorem torusEvent_lift (a : VectorField 2) (w : ScalarField 2) :
    torusEvent (liftVelocity a w) ↔
      ∃ t : ℝ, 0 ≤ t ∧ ∃ X : Coord 2,
        1 / 32 < X 1 ∧ X 1 < 1 / 8 ∧ (1 / 2 : ℝ) < w t X := by
  constructor
  · rintro ⟨t, ht, x, hx1, hx2, hx3⟩
    refine ⟨t, ht, horizontal x, ?_, ?_, ?_⟩
    · simpa [horizontal] using hx1
    · simpa [horizontal] using hx2
    · simpa [liftVelocity] using hx3
  · rintro ⟨t, ht, X, hx1, hx2, hx3⟩
    refine ⟨t, ht, join X 0, ?_, ?_, ?_⟩
    · simpa [join] using hx1
    · simpa [join] using hx2
    · simpa [liftVelocity] using hx3

end VelocityDetection.Observation
end

end OAI
