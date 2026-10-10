import OAI.Geometry.EinsteinFour.ReferenceCompression
import OAI.Geometry.EinsteinFour.SineAverage
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! Trace and curvature bounds for the concrete sine-weighted average. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup

private instance matrixContinuousENorm : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

private def entryCLM (i j : Fin 3) : NormalMatrix →L[ℝ] ℝ :=
  (show NormalMatrix →ₗ[ℝ] ℝ from
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

@[simp] private theorem entryCLM_apply (i j : Fin 3) (A : NormalMatrix) :
    entryCLM i j A = A i j := rfl

private def quadraticCLM (x : Fin 3 → ℝ) : NormalMatrix →L[ℝ] ℝ :=
  ∑ i, ∑ j, (x i * x j) • entryCLM i j

private theorem quadraticCLM_apply (x : Fin 3 → ℝ) (A : NormalMatrix) :
    quadraticCLM x A = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [quadraticCLM, _root_.sum_apply, _root_.smul_apply,
    entryCLM_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private def traceCLM : NormalMatrix →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

private theorem integral_sine_posSemidef {A : ℝ → NormalMatrix}
    (hi : Integrable A Averages.sineMeasure) (hpos : ∀ s, (A s).PosSemidef) :
    (∫ s, A s ∂Averages.sineMeasure).PosSemidef := by
  have he (i j : Fin 3) :
      (∫ s, A s ∂Averages.sineMeasure) i j = ∫ s, A s i j ∂Averages.sineMeasure := by
    have h := (entryCLM i j).integral_comp_comm hi
    exact h.symm
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    change (∫ s, A s ∂Averages.sineMeasure) j i =
      (∫ s, A s ∂Averages.sineMeasure) i j
    rw [he, he]
    apply integral_congr_ae
    filter_upwards [] with s
    exact congrFun (congrFun (hpos s).isHermitian.eq i) j
  · intro x
    rw [← quadraticCLM_apply]
    calc
      0 ≤ ∫ s, quadraticCLM x (A s) ∂Averages.sineMeasure := by
        apply integral_nonneg
        intro s
        change 0 ≤ quadraticCLM x (A s)
        rw [quadraticCLM_apply]
        exact (hpos s).dotProduct_mulVec_nonneg x
      _ = quadraticCLM x (∫ s, A s ∂Averages.sineMeasure) :=
        (quadraticCLM x).integral_comp_comm hi

theorem sine_average_trace {A : ℝ → NormalMatrix} (hA : Continuous A)
    (htrace : ∀ s, (A s).trace = 0) :
    (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s).trace = 0 := by
  rw [← Averages.integral_sineMeasure A]
  have h := traceCLM.integral_comp_comm (Averages.integrable_sineMeasure hA)
  change (∫ s, (A s).trace ∂Averages.sineMeasure) =
    (∫ s, A s ∂Averages.sineMeasure).trace at h
  simpa only [htrace, integral_zero] using h.symm

/-- Averaging preserves the lower normal-curvature bound. -/
theorem sine_average_add_one_posSemidef {A : ℝ → NormalMatrix} (hA : Continuous A)
    (hpos : ∀ s, (A s + 1).PosSemidef) :
    ((∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s) + 1).PosSemidef := by
  have hp := integral_sine_posSemidef
    ((Averages.integrable_sineMeasure hA).add (integrable_const 1)) hpos
  change (∫ s, (A s + 1) ∂Averages.sineMeasure).PosSemidef at hp
  rw [integral_add (Averages.integrable_sineMeasure hA) (integrable_const 1),
    integral_const] at hp
  simpa only [probReal_univ, one_smul, Averages.integral_sineMeasure] using hp

end

end PositiveEinsteinFour.Jacobi

end OAI
