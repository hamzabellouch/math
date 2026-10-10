import OAI.Geometry.SurfaceImmersion.Primitive.MixedPeriodicBounds

namespace OAI

/-! Mean and fluctuation preserve mixed weighted periodic estimates. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.SmoothPeriodicCalculus
open SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma angleDerivative_sub {F G : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    angleDerivative (F - G) = angleDerivative F - angleDerivative G := by
  funext z
  unfold angleDerivative
  rw [((hF.differentiable (by simp) z).hasFDerivAt.sub
    (hG.differentiable (by simp) z).hasFDerivAt).fderiv]
  rfl

lemma angularIterated_sub {F G : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (n : ℕ) : angularIterated n (F - G) = angularIterated n F - angularIterated n G := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change angleDerivative (angularIterated n (F - G)) = _
    rw [ih, angleDerivative_sub (contDiff_angularIterated hF n) (contDiff_angularIterated hG n)]
    rfl

variable [FiniteDimensional ℝ P] [CompleteSpace E]

def meanLift (F : P × ℝ → E) (z : P × ℝ) : E := ∫ t in (0 : ℝ)..1, F (z.1, t)

lemma contDiff_meanLift {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (meanLift F) := (contDiff_integral hF 0 1).comp contDiff_fst

lemma angleDerivative_meanLift {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    angleDerivative (meanLift F) = 0 := by
  funext z
  exact (angle_hasDerivAt (contDiff_meanLift hF) z.1 z.2).unique
    (hasDerivAt_const z.2 (∫ t in (0 : ℝ)..1, F (z.1, t)))

lemma angularIterated_meanLift_succ {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    angularIterated (n + 1) (meanLift F) = 0 := by
  induction n with
  | zero => exact angleDerivative_meanLift hF
  | succ n ih =>
    change angleDerivative (angularIterated (n + 1) (meanLift F)) = 0
    rw [ih]
    funext z
    simp [angleDerivative]

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma partialIterated_sub {F G : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (z : P × ℝ) :
    partialIterated n (F - G) z = partialIterated n F z - partialIterated n G z := by
  exact iteratedFDeriv_sub_apply
    (((hF.comp (contDiff_id.prodMk contDiff_const)).of_le
      (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt)
    (((hG.comp (contDiff_id.prodMk contDiff_const)).of_le
      (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt)

end ClosedSurfaceR4.SmoothPeriodicCalculus

namespace ClosedSurfaceR4.WeightedEstimates
open SmoothParameterIntegral SmoothPeriodicCalculus

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Averaging does not increase the mixed weighted bound. -/
theorem mixed_weighted_mean {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set P} (hU : IsOpen U) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (m : ℕ)
    (hb : ∀ j k, j + k ≤ m → ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (angularIterated k F) (p, t)‖ ≤ C) :
    ∀ j k, j + k ≤ m → ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (angularIterated k (meanLift F)) (p, t)‖ ≤ C := by
  have hm := weighted_parameter_integral hF hU hs m 0 1
    (fun j hj p hp t ht => hb j 0 (by simpa using hj) p hp t (by simpa using ht))
  simp only [sub_zero, abs_one, mul_one] at hm
  intro j k hjk p hp t _
  cases k with
  | zero =>
    have hh := hm j (by omega) p hp
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (((contDiff_integral hF 0 1).of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt) hp] at hh
    exact hh
  | succ k =>
    rw [angularIterated_meanLift_succ hF k]
    simpa [partialIterated] using hC

/-- Subtracting the mean costs at most a factor of two and no scale loss. -/
theorem mixed_weighted_fluctuation {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set P} (hU : IsOpen U) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (m : ℕ)
    (hb : ∀ j k, j + k ≤ m → ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (angularIterated k F) (p, t)‖ ≤ C) :
    ∀ j k, j + k ≤ m → ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (angularIterated k (F - meanLift F)) (p, t)‖ ≤ 2 * C := by
  have hm := mixed_weighted_mean hF hU hs hC m hb
  intro j k hjk p hp t ht
  rw [angularIterated_sub hF (contDiff_meanLift hF),
    partialIterated_sub (contDiff_angularIterated hF k)
      (contDiff_angularIterated (contDiff_meanLift hF) k)]
  calc
    _ ≤ s ^ j * (‖partialIterated j (angularIterated k F) (p, t)‖ +
        ‖partialIterated j (angularIterated k (meanLift F)) (p, t)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hs.le j)
    _ ≤ C + C := by
      rw [mul_add]
      exact add_le_add (hb j k hjk p hp t ht) (hm j k hjk p hp t ht)
    _ = 2 * C := by ring

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
