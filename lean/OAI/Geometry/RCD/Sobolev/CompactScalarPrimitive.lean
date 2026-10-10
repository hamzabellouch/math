import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Two primitives of a compact scalar second derivative

Only continuity and compact support of the prescribed second derivative
are needed. Both primitives vanish at zero and have global Lipschitz bounds.
-/

open Set Filter MeasureTheory
open scoped NNReal Interval
noncomputable section
namespace RegularPointCoordinates

theorem compact_scalar_two_primitives {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) :
    ∃ (Φ φ : ℝ → ℝ) (C D B E : ℝ≥0),
      LipschitzWith C Φ ∧ LipschitzWith D φ ∧ Φ 0=0 ∧ φ 0=0 ∧
      (∀ a, HasDerivAt Φ (φ a) a) ∧ (∀ a, HasDerivAt φ (ψ a) a) ∧
      (∀ a, |φ a| ≤ B) ∧ (∀ a, |ψ a| ≤ E) ∧
      (∀ a, φ a=∫ s in 0..a, ψ s) ∧ (∀ a, Φ a=∫ s in 0..a, φ s) := by
  let φ := fun a => ∫ s in 0..a, ψ s
  let Φ := fun a => ∫ s in 0..a, φ s
  have hi : Integrable ψ volume := hc.integrable_of_hasCompactSupport hs
  let B : ℝ≥0 := ⟨∫ s, ‖ψ s‖,integral_nonneg fun _ => norm_nonneg _⟩
  obtain ⟨E,hE⟩ := hs.exists_bound_of_continuous hc
  let En : ℝ≥0 := ⟨E,(norm_nonneg (ψ 0)).trans (hE 0)⟩
  have hdφ (a : ℝ) : HasDerivAt φ (ψ a) a :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun a => (hdφ a).continuousAt
  have hdΦ (a : ℝ) : HasDerivAt Φ (φ a) a :=
    intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable _ _)
      hφ.aestronglyMeasurable.stronglyMeasurableAtFilter hφ.continuousAt
  have hb (a : ℝ) : |φ a| ≤ B := by
    calc
      |φ a| = ‖φ a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in Ι (0 : ℝ) a, ‖ψ s‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s, ‖ψ s‖ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun _ => norm_nonneg _) hi.norm
      _ = B := rfl
  have hlφ : LipschitzWith En φ := lipschitzWith_of_nnnorm_deriv_le
    (fun a => (hdφ a).differentiableAt) (fun a => by
      rw [(hdφ a).deriv]
      exact NNReal.coe_le_coe.mp (hE a))
  have hlΦ : LipschitzWith B Φ := lipschitzWith_of_nnnorm_deriv_le
    (fun a => (hdΦ a).differentiableAt) (fun a => by
      rw [(hdΦ a).deriv]
      apply NNReal.coe_le_coe.mp
      simpa only [coe_nnnorm,Real.norm_eq_abs] using hb a)
  refine ⟨Φ,φ,B,En,B,En,hlΦ,hlφ,?_,?_,hdΦ,hdφ,hb,?_,fun _ => rfl,fun _ => rfl⟩
  · exact intervalIntegral.integral_same
  · exact intervalIntegral.integral_same
  · intro a; exact hE a

end RegularPointCoordinates

end

end OAI
