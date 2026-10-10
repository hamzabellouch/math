import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-!
# L2 averaging for the orbit-window argument

For an ergodic probability-preserving transformation, the Hilbert-space
mean ergodic theorem has a constant limit. This supplies actual Cesaro
averages, rather than an extra generic-point or averaging hypothesis.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

/-- The Koopman fixed subspace of an ergodic map consists of constants,
so its actual Cesaro averages converge in L2 to a constant. -/
theorem exists_constant_L2_orbit_average
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Ergodic T μ) (f : Lp ℝ 2 μ) :
    ∃ c : ℝ, Tendsto
      (fun N => birkhoffAverage ℝ (Lp.compMeasurePreserving T hT.toMeasurePreserving)
        id N f) atTop
      (𝓝 ((memLp_const c : MemLp (fun _ : X => c) 2 μ).toLp (fun _ => c))) := by
  let U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT.toMeasurePreserving).toContinuousLinearMap
  have hU : ‖U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖Lp.compMeasurePreserving T hT.toMeasurePreserving x‖ ≤ 1 * ‖x‖
    rw [Lp.norm_compMeasurePreserving, one_mul]
  let S := U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let q : S := S.orthogonalProjectionOnto f
  have hq : Lp.compMeasurePreserving T hT.toMeasurePreserving (q : Lp ℝ 2 μ) = q := by
    have h := q.property
    change U (q : Lp ℝ 2 μ) = (q : Lp ℝ 2 μ) at h
    exact h
  have hqae : (fun x => (q : Lp ℝ 2 μ) (T x)) =ᵐ[μ] (q : Lp ℝ 2 μ) := by
    have h := (Lp.coeFn_compMeasurePreserving (q : Lp ℝ 2 μ) hT.toMeasurePreserving).symm
    rwa [hq] at h
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae
    (Lp.aestronglyMeasurable (q : Lp ℝ 2 μ)) hqae
  have hconst : (q : Lp ℝ 2 μ) =
      (memLp_const c : MemLp (fun _ : X => c) 2 μ).toLp (fun _ => c) :=
    Lp.ext (hc.trans (memLp_const c).coeFn_toLp.symm)
  refine ⟨c, ?_⟩
  have hav := U.tendsto_birkhoffAverage_orthogonalProjection hU f
  change Tendsto (fun N => birkhoffAverage ℝ U id N f) atTop (𝓝 (q : Lp ℝ 2 μ)) at hav
  rw [hconst] at hav
  exact hav

end DukePrimeDegree

end

end OAI
