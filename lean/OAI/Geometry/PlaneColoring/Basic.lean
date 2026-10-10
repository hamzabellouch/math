import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem160

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def circleDir (t : ℝ) : Plane :=
  WithLp.toLp 2 ![Real.cos t, Real.sin t]

def normalizedAngleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ •
    Measure.restrict volume (Set.Ico 0 (2 * Real.pi))

def circleMeasure : Measure Plane :=
  Measure.map circleDir normalizedAngleMeasure

def weakPairMeasure (R : ℝ) : Measure (Plane × Plane) :=
  (Measure.restrict volume (Metric.ball (0 : Plane) R)).prod circleMeasure

def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    ∀ x y : Plane, dist x y = 1 → c x ≠ c y

def WeakMeasurableColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    AEMeasurable c volume ∧
      ∀ R : ℝ, 0 < R →
        (∑ i : Fin k,
          (weakPairMeasure R)
            {p : Plane × Plane |
              c (Prod.fst p) = i ∧
              c (Prod.fst p + Prod.snd p) = i}) = 0

def planeChromaticNumber : ℕ :=
  sInf {k : ℕ | ProperColoring k}

end Problem160

end

end OAI
