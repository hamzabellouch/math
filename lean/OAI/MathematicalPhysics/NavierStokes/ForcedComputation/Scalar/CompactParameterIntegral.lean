import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowSuperposition
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Smooth compact parameter integrals via continuous functions and the
bounded Bochner integral. -/

noncomputable section
namespace ForcedComputation.Flow
open MeasureTheory
open scoped ContDiff

variable {K E F P : Type} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def compactIntegral (μ : Measure K) [IsFiniteMeasure μ] : C(K, F) →L[ℝ] F :=
  (MeasureTheory.L1.integralCLM (α := K) (E := F) (μ := μ)).comp
    (ContinuousMap.toLp 1 μ ℝ)

theorem compactIntegral_apply (μ : Measure K) [IsFiniteMeasure μ] (f : C(K, F)) :
    compactIntegral μ f = ∫ y, f y ∂μ := by
  change MeasureTheory.L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← MeasureTheory.L1.integral_eq, MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f)

theorem compactIntegral_hasFDerivAt (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(E, F)) (hf : ContDiff ℝ 1 (f : E → F))
    {v : P → C(K, E)} {p : P} {v' : P →L[ℝ] C(K, E)}
    (hv : HasFDerivAt v v' p) :
    HasFDerivAt (fun q => ∫ y, f (v q y) ∂μ)
      ((compactIntegral (F := F) μ).comp
        ((applyPath ⟨fun y => fderiv ℝ f (v p y),
          (hf.continuous_fderiv (by simp)).comp (v p).continuous⟩).comp v')) p := by
  have h := (compactIntegral (F := F) μ).hasFDerivAt.comp p
    ((postcompose_hasFDerivAt f hf (v p)).comp p hv)
  convert h using 1
  funext q
  exact (compactIntegral_apply μ (postcompose f (v q))).symm

theorem fderiv_compactIntegral_apply (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(E, F)) (hf : ContDiff ℝ 1 (f : E → F))
    {v : P → C(K, E)} {p : P} {v' : P →L[ℝ] C(K, E)}
    (hv : HasFDerivAt v v' p) (q : P) :
    fderiv ℝ (fun r => ∫ y, f (v r y) ∂μ) p q =
      ∫ y, fderiv ℝ f (v p y) (v' q y) ∂μ := by
  rw [(compactIntegral_hasFDerivAt μ f hf hv).fderiv]
  exact compactIntegral_apply μ _

theorem contDiff_compactIntegral (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(E, F)) (hf : ContDiff ℝ ∞ (f : E → F))
    (v : P → C(K, E)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun p => ∫ y, f (v p y) ∂μ) := by
  have h := (compactIntegral (F := F) μ).contDiff.comp
    ((postcompose_contDiff f hf).comp hv)
  convert h using 1
  funext p
  exact (compactIntegral_apply μ (postcompose f (v p))).symm

end ForcedComputation.Flow

end

end OAI
