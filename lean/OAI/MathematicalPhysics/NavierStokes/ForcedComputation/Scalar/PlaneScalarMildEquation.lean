import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildKernels
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetBilinear

namespace OAI

/-! Actual finite-jet scalar mild equations with the Gaussian heat and gradient operators. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Real MeasureTheory Set ShearFlows
open scoped Topology Interval BigOperators

/-- Multiplication by a bounded scalar jet, as a bounded linear operator on the unknown jet. -/
def multiplication (k : ℕ) (b : Jet k) : Jet k →L[ℝ] Jet k :=
  BoundedSpatialJets.operatorEquiv Plane ℝ ℝ k
    (BoundedSpatialJets.bilinearCLM Plane ℝ ℝ ℝ k (ContinuousLinearMap.mul ℝ ℝ) b)

theorem multiplication_apply (k : ℕ) (b u : Jet k) (x : Plane) :
    BoundedSpatialJets.function Plane ℝ k (multiplication k b u) x =
      BoundedSpatialJets.function Plane ℝ k b x * BoundedSpatialJets.function Plane ℝ k u x := by
  exact BoundedSpatialJets.function_bilinear Plane ℝ ℝ ℝ k (ContinuousLinearMap.mul ℝ ℝ) b u x

/-- A continuous coefficient jet curve induces a continuous curve of multiplication operators. -/
def coefficientCurve {T : ℝ} (k : ℕ) (b : C(Icc (0 : ℝ) T, Jet k)) :
    C(Icc (0 : ℝ) T, Jet k →L[ℝ] Jet k) :=
  ⟨fun t => multiplication k (b t),
    (BoundedSpatialJets.operatorEquiv Plane ℝ ℝ k).continuous.comp
      ((BoundedSpatialJets.bilinearCLM Plane ℝ ℝ ℝ k (ContinuousLinearMap.mul ℝ ℝ)).continuous.comp
        b.continuous)⟩

@[simp] theorem coefficientCurve_apply {T : ℝ} (k : ℕ) (b : C(Icc (0 : ℝ) T, Jet k))
    (t : Icc (0 : ℝ) T) : coefficientCurve k b t = multiplication k (b t) := rfl

private theorem integral_sum_eq_raw {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (b : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (u : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    (∑ i, ∫ s in 0..t.val, kernels hν k T i (t.val-s)
      (coefficientCurve k (b i) (projIcc 0 T hT s)
        (WeaklySingular.extendPath (Jet k) hT u s))) =
    ∑ i, ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
      (multiplication k (b i (projIcc 0 T hT s))
        (WeaklySingular.extendPath (Jet k) hT u s)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  dsimp only
  rw [kernels_eq_raw hν k ((sub_le_self _ hs.1).trans t.property.2) i]
  rfl

/-- The scalar mild equation is uniquely solvable on every finite time interval in every
finite jet order. The three coefficients are `div a`, `-a₀`, and `-a₁` in the drift equation. -/
theorem exists_unique_mild {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (b : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (a : WeaklySingular.Path (Jet k) T) :
    ∃! u : WeaklySingular.Path (Jet k) T, ∀ t : Icc (0 : ℝ) T, u t = a t +
      ∑ i, ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (multiplication k (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet k) hT u s)) := by
  obtain ⟨u, hu, huniq⟩ := WeaklySingular.exists_unique_integral_equation (Jet k) hT
    (kernels hν k T) (kernels_continuous hν k T) (kernelConstants ν T)
    (kernelConstants_nonneg ν T) (kernels_bound hν k T) (fun i => coefficientCurve k (b i)) a
  refine ⟨u, ?_, ?_⟩
  · intro t
    exact (hu t).trans (congrArg (fun v => a t + v) (integral_sum_eq_raw hT hν k b u t))
  · intro v hv
    apply huniq v
    intro t
    exact (hv t).trans (congrArg (fun w => a t + w) (integral_sum_eq_raw hT hν k b v t).symm)

end ForcedComputation.PlaneScalarMild

end

end OAI
