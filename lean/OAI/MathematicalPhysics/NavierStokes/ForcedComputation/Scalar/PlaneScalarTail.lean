import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarSupersolution

namespace OAI

/-! Integrable diffusion tails on each finite time cylinder, from bounded comparison. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

theorem PlaneScalarSolution.tail_bound {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w)
    (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ t ∈ Icc 0 T, ∀ x,
      w t x ≤ C * Real.exp (K * t) * planeTailProfile x := by
  obtain ⟨A, hA, hAb⟩ := hc.drift_bound ha T hT
  obtain ⟨C, hC, hCb⟩ := hc.source_tail_bound hh T hT
  let K := 24 * ν + 8 * A + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let v : ℝ → Plane → ℝ := fun t x => C * Real.exp (K * t) * planeTailProfile x
  refine ⟨C, K, hC, hK, ?_⟩
  apply hw.le_supersolution hT hν ha hc
    (d := fun t x => K * v t x)
  · have hs : ContDiff ℝ ∞ (Function.uncurry v) := by
      exact ((contDiff_const.mul
        ((contDiff_const.mul contDiff_fst).exp)).mul
          (planeTailProfile_smooth.comp contDiff_snd))
    exact hs.continuous.continuousOn
  · intro t _
    exact contDiff_const.mul planeTailProfile_smooth
  · intro t _ x
    apply HasDerivAt.hasDerivWithinAt
    simpa only [v, id_eq, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using
      ((((hasDerivAt_id t).const_mul K).exp.const_mul C).mul_const (planeTailProfile x))
  · intro t ht x
    have hcoef : 0 ≤ C * Real.exp (K * t) := mul_nonneg hC (Real.exp_pos _).le
    have hg := mul_le_mul_of_nonneg_left
      (planeTailProfile_generator_bound hν hA (a t) (hAb t ⟨ht.1.le, ht.2⟩) x) hcoef
    have he : 1 ≤ Real.exp (K * t) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hK ht.1.le)
    have hce : C ≤ C * Real.exp (K * t) := by nlinarith
    have hh' : h t x ≤ v t x := (hCb t ⟨ht.1.le, ht.2⟩ x).trans
      (mul_le_mul_of_nonneg_right hce (planeTailProfile_pos x).le)
    change scalarGenerator ν (a t)
      (fun y => (C * Real.exp (K * t)) * planeTailProfile y) x + h t x ≤ K * v t x
    rw [scalarGenerator_const_mul planeTailProfile_smooth]
    dsimp only [K, v] at *
    nlinarith
  · intro t _ x
    exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (planeTailProfile_pos x).le

theorem PlaneScalarSolution.integrable {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w)
    (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    ∀ t ∈ Icc 0 T, Integrable (w t) := by
  obtain ⟨C, K, _, _, hb⟩ := hw.tail_bound hT hν ha hh hc
  have hnonneg := hw.nonnegative hT hν ha hc hpos
  intro t ht
  apply (planeTailProfile_integrable.const_mul (C * Real.exp (K * t))).mono'
    (hw.slice_smooth ht).continuous.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht x)]
  exact hb t ht x

end ForcedComputation.VelocityDetector

end

end OAI
