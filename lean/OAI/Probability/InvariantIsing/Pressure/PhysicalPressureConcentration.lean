import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily
import OAI.Probability.InvariantIsing.Pressure.PressureMean

namespace OAI

/-! Almost-sure pressure concentration for the actual orthogonal matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

theorem ae_physical_pressure_sub_mean_tendsto_zero (hpub : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (n : ℕ) → Ω → Orthogonal (n+3)) (hU : ∀ n, Measurable (U n))
    (hHaar : ∀ n, (P.map (U n)).IsMulRightInvariant)
    (eig c : (n : ℕ) → Fin (n+3) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ n i, |eig n i| ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      rotatedPressure (eig n) (matrixRotation (U n ω)⁻¹) (c n)-
        ∫ η, rotatedPressure (eig n) (matrixRotation (U n η)⁻¹) (c n) ∂P)
      atTop (𝓝 0) := by
  let V (n : ℕ) (ω : Ω) := cavityOrientationLift (by omega : 0 < n+3) (U n ω)⁻¹
  have hm n : Measurable (V n) :=
    (measurable_cavityOrientationLift _).comp (hU n).inv
  have hl n : P.map (V n)=cavityOrientedBaseLaw (by omega : 0 < n+3) (P.map (U n)) := by
    change P.map ((fun W => cavityOrientationLift (by omega : 0 < n+3) W⁻¹) ∘ U n)=_
    exact (Measure.map_map ((measurable_cavityOrientationLift _).comp measurable_inv) (hU n)).symm
  have hv n : (P.map (V n)).IsMulLeftInvariant := by
    let : IsProbabilityMeasure (P.map (U n)) :=
      (Measure.isProbabilityMeasure_map_iff (hU n).aemeasurable).mpr inferInstance
    let : (P.map (U n)).IsMulRightInvariant := hHaar n
    rw [hl n]
    exact cavityOrientedBaseLaw_leftInvariant _ _
  have he n ω : rotatedPressure (eig n) (specialRotation (V n ω)) (c n)=
      rotatedPressure (eig n) (matrixRotation (U n ω)⁻¹) (c n) := by
    simp only [V,rotatedPressure,cavityOrientationLift_energy]
  have hh := ae_pressure_sub_mean_tendsto_zero hpub P V hm hv eig c K hK heig
  simpa only [he] using hh

end InvariantIsing

end

end OAI
