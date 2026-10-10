import Mathlib

namespace OAI

open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
local instance namedAtLeastTwoTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable local instance ambientSub (d : ℕ) : Sub (Ambient d) where
  sub vector other := WithLp.toLp (2 : ℝ≥0∞)
    (WithLp.ofLp (p := (2 : ℝ≥0∞)) vector - WithLp.ofLp (p := (2 : ℝ≥0∞)) other)

noncomputable local instance ambientInner (d : ℕ) : Inner ℝ (Ambient d) where
  inner vector other := ∑ coordinate : Fin d,
    inner ℝ (WithLp.ofLp (p := (2 : ℝ≥0∞)) vector coordinate)
      (WithLp.ofLp (p := (2 : ℝ≥0∞)) other coordinate)

noncomputable def gramVolume {d k : ℕ} (u : Ambient d) (z : Fin k → Ambient d) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i => z i-u)).det
noncomputable def inverseVolume {d : ℕ} (u : Ambient d) (z : Fin (d/100) → Ambient d) : ℝ≥0∞ :=
  ((ENNReal.ofReal (gramVolume u z))⁻¹)^(d/100)
def BallBound {d : ℕ} (ν : Measure (Ambient d)) : Prop :=
  ∀ (x : Ambient d) (r : ℝ), 0 < r →
    ν (ball x r) ≤ ENNReal.ofReal (r^(((d:ℝ)-1)/2))
def InverseVolumeStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ ν : Measure (Ambient d), IsProbabilityMeasure ν → BallBound ν →
      ∀ u : Ambient d, (∫⁻ z,inverseVolume u z ∂Measure.pi (fun _ : Fin (d/100) => ν)) ≤
        ENNReal.ofReal (Real.exp (C*d*(d/100:ℕ)))

open Set
open scoped Topology NNReal

end AllScaleInverseVolume

end OAI
