import OAI.Analysis.FiniteFactor.CrossedProduct.AngleRelations
import OAI.Analysis.FiniteFactor.CrossedProduct.Rotation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

def sourceFirstCoordinate : SourceCoordinate :=
  ⟨0, ⟨0, by have := (sourceStage 0).m_ge_100; change 0 < (sourceStage 0).m; omega⟩⟩

theorem SourceRationalIndependent.mul_ne_integer {θ : SourceCoordinate → ℝ}
    (hθ : SourceRationalIndependent θ) (i : SourceCoordinate) (k : ℤ) (hk : k ≠ 0) (c : ℤ) :
    (k : ℝ)*θ i ≠ (c : ℝ) := by
  intro he
  have hh := (hθ (Finsupp.single i k) c (by simpa using he)).1
  have hz := congrArg (fun v : SourceCoordinate →₀ ℤ => v i) hh
  exact hk (by simpa using hz)

/-- Every nonzero integer rotation has no fixed point, using one source
coordinate. This is pointwise freeness, not merely an almost-everywhere claim. -/
theorem SourceRationalIndependent.rotation_free {θ : SourceCoordinate → ℝ}
    (hθ : SourceRationalIndependent θ) (k : ℤ) (hk : k ≠ 0) (x : SourceCoordinate → ℝ) :
    coordinateRotate θ k x ≠ x := by
  intro he
  have hh := congrFun he sourceFirstCoordinate
  change Int.fract (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate) =
    x sourceFirstCoordinate at hh
  rw [Int.fract] at hh
  apply hθ.mul_ne_integer sourceFirstCoordinate k hk
    (Int.floor (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate))
  linarith

theorem exists_source_free_base : ∃ θ : SourceCoordinate → ℝ,
    SourceAngles θ ∧ SourceRationalIndependent θ ∧
    (∀ k : ℤ, MeasurePreserving (coordinateRotate θ k)
      (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))
      (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) ∧
    (∀ k : ℤ, k ≠ 0 → ∀ x, coordinateRotate θ k x ≠ x) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨θ, ha, hr⟩ := (sourceAngleLaw_admissible.and sourceAngleLaw_rationalIndependent).exists
  exact ⟨θ, ha, hr, fun k => coordinateRotate_preserving θ k,
    fun k hk x => hr.rotation_free k hk x, ha, staged_sourceOperator_properties θ ha⟩

end
end FiniteFactor

end OAI
