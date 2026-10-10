import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldParameterLimit

namespace OAI

/-! Bounded coefficient errors acting on the approximate outgoing columns.
Vanishing coefficient errors give vanishing normalized forcing. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def boundedCircularCoefficientAction (A B : ℝ →ᵇ ℂ) (Z : CircularTailSpace) :
    CircularTailSpace := by
  let N := fun t => circularCoefficientAction (A t) (B t) (circularTailEvaluation Z t)
  have hc : Continuous N := by
    dsimp [N,circularCoefficientAction,circularTailEvaluation]
    fun_prop
  have hb (t : ℝ) : ‖N t‖ ≤ (‖A‖+‖B‖)*‖Z‖ := by
    exact (circularCoefficientAction_norm _ _ _).trans
      (mul_le_mul (add_le_add (A.norm_coe_le_norm t) (B.norm_coe_le_norm t))
        (circularTailEvaluation_norm Z t) (norm_nonneg _) (by positivity))
  exact (BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (N t).1)
    hc.fst ((‖A‖+‖B‖)*‖Z‖) (fun t => (norm_fst_le (N t)).trans (hb t)),
    BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (N t).2)
    hc.snd ((‖A‖+‖B‖)*‖Z‖) (fun t => (norm_snd_le (N t)).trans (hb t)))

theorem boundedCircularCoefficientAction_evaluation (A B : ℝ →ᵇ ℂ) (Z : CircularTailSpace) (t : ℝ) :
    circularTailEvaluation (boundedCircularCoefficientAction A B Z) t=
      circularCoefficientAction (A t) (B t) (circularTailEvaluation Z t) := rfl

theorem boundedCircularCoefficientAction_norm (A B : ℝ →ᵇ ℂ) (Z : CircularTailSpace) :
    ‖boundedCircularCoefficientAction A B Z‖ ≤ (‖A‖+‖B‖)*‖Z‖ := by
  have hb (t : ℝ) : ‖circularCoefficientAction (A t) (B t) (circularTailEvaluation Z t)‖ ≤
      (‖A‖+‖B‖)*‖Z‖ := by
    exact (circularCoefficientAction_norm _ _ _).trans
      (mul_le_mul (add_le_add (A.norm_coe_le_norm t) (B.norm_coe_le_norm t))
        (circularTailEvaluation_norm Z t) (norm_nonneg _) (by positivity))
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro t
    exact (norm_fst_le _).trans (hb t)
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro t
    exact (norm_snd_le _).trans (hb t)

theorem boundedCircularCoefficientAction_tendsto_zero (A B : ℕ → ℝ →ᵇ ℂ)
    (Z : ℕ → CircularTailSpace) (Z₀ : CircularTailSpace)
    (hA : Tendsto A atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 0))
    (hZ : Tendsto Z atTop (𝓝 Z₀)) :
    Tendsto (fun n => boundedCircularCoefficientAction (A n) (B n) (Z n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => boundedCircularCoefficientAction_norm (A n) (B n) (Z n))
  simpa only [norm_zero,add_zero,zero_mul] using (hA.norm.add hB.norm).mul hZ.norm

end DefocusingNLS

end OAI
