import OAI.Probability.InvariantIsing.Cavity.CavityHaarSides
import OAI.Probability.InvariantIsing.Pressure.Concentration

namespace OAI

/-! An all-size version of the oriented physical law. The zero-dimensional
case is only a harmless placeholder for sequences indexed by all naturals. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

def cavityOrientedFamily (μ : (N : ℕ) → Measure (Orthogonal N)) (N : ℕ) :
    Measure (SpecialOrthogonal N) :=
  if h : 0 < N then cavityOrientedBaseLaw h (μ N) else Measure.dirac 1

lemma cavityOrientedFamily_pos (μ : (N : ℕ) → Measure (Orthogonal N))
    {N : ℕ} (hN : 0 < N) :
    cavityOrientedFamily μ N=cavityOrientedBaseLaw hN (μ N) := by
  simp only [cavityOrientedFamily, dite_eq_left hN]

instance cavityOrientedFamily_probability (μ : (N : ℕ) → Measure (Orthogonal N))
    [∀ N, IsProbabilityMeasure (μ N)] (N : ℕ) :
    IsProbabilityMeasure (cavityOrientedFamily μ N) := by
  by_cases hN : 0 < N
  · rw [cavityOrientedFamily_pos μ hN]
    infer_instance
  · simp only [cavityOrientedFamily, dite_eq_right hN]
    infer_instance

lemma cavityOrientedFamily_leftInvariant (μ : (N : ℕ) → Measure (Orthogonal N))
    [∀ N, IsProbabilityMeasure (μ N)] [∀ N, (μ N).IsMulRightInvariant] (N : ℕ) :
    (cavityOrientedFamily μ N).IsMulLeftInvariant := by
  by_cases hN : 0 < N
  · rw [cavityOrientedFamily_pos μ hN]
    exact cavityOrientedBaseLaw_leftInvariant hN (μ N)
  · have hzero : N=0 := by omega
    subst N
    constructor
    intro g
    have hg : g=1 := by
      apply Subtype.ext
      ext i
      exact Fin.elim0 i
    rw [hg]
    simp

lemma cavity_oriented_pressure {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) (eig c : Fin N → ℝ) :
    (∫ U, rotatedPressure eig (specialRotation U) c ∂cavityOrientedBaseLaw hN μ) =
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ := by
  calc
    _ = ∫ V, rotatedPressure eig
        (specialRotation (cavityOrientationLift hN V⁻¹)) c ∂μ :=
      ((cavityOrientedBaseLaw_preserving hN μ).hasLaw.integral_comp
        (measurable_rotatedPressure eig c).aestronglyMeasurable).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun V => by
        simp only [rotatedPressure, cavityOrientationLift_energy]

end InvariantIsing

end

end OAI
