import OAI.Geometry.SurfaceImmersion.Primitive.WeightedPeriodicPrimitive
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCalculus

namespace OAI

/-! Mixed slow and angular derivative estimates for normalized primitives. -/
noncomputable section
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.SmoothPeriodicCalculus

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def angularIterated : ℕ → (P × ℝ → E) → P × ℝ → E
  | 0, F => F
  | n + 1, F => angleDerivative (angularIterated n F)

lemma contDiff_angularIterated {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (angularIterated n F) := by
  induction n with
  | zero => exact hF
  | succ n ih => exact contDiff_angleDerivative ih

variable [FiniteDimensional ℝ P] [CompleteSpace E]

lemma angleDerivative_primitive {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    angleDerivative (fun z : P × ℝ => PeriodicPrimitive.primitive (fun t => F (z.1, t)) z.2) = F := by
  funext z
  exact (angle_hasDerivAt (PeriodicPrimitive.contDiff_primitive_joint hF) z.1 z.2).unique
    (PeriodicPrimitive.primitive_hasDerivAt
      (hF.continuous.comp (continuous_const.prodMk continuous_id)) z.2)

lemma angularIterated_primitive_succ {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    angularIterated (n + 1)
      (fun z : P × ℝ => PeriodicPrimitive.primitive (fun t => F (z.1, t)) z.2) =
        angularIterated n F := by
  induction n with
  | zero => exact angleDerivative_primitive hF
  | succ n ih => change angleDerivative _ = angleDerivative _; rw [ih]

end ClosedSurfaceR4.SmoothPeriodicCalculus

namespace ClosedSurfaceR4.WeightedEstimates
open SmoothParameterIntegral SmoothPeriodicCalculus PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Slow derivatives carry the scale weight; angular derivatives do not.
The primitive adds no scale loss, uniformly at every mixed derivative order. -/
theorem mixed_weighted_primitive {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set P} (hU : IsOpen U) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (m : ℕ)
    (hb : ∀ j k, j + k ≤ m → ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (angularIterated k F) (p, t)‖ ≤ C) :
    ∀ j k, j + k ≤ m → ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (angularIterated k
        (fun z : P × ℝ => primitive (fun r => F (z.1, r)) z.2)) (p, t)‖ ≤ 2 * C := by
  intro j k hjk p hp t ht
  cases k with
  | zero =>
    have hh := weighted_periodicPrimitive hF hU hs hC m
      (fun r hr => hb r 0 (by simpa using hr)) ht j (by omega) p hp
    have hQ : ContDiff ℝ ∞ (fun q => primitive (fun r => F (q, r)) t) :=
      (contDiff_primitive_joint hF).comp (contDiff_id.prodMk contDiff_const)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((hQ.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt) hp] at hh
    exact hh
  | succ k =>
    rw [angularIterated_primitive_succ hF k]
    exact (hb j k (by omega) p hp t ht).trans (by linarith)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
