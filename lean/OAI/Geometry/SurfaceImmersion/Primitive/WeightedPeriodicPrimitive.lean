import OAI.Geometry.SurfaceImmersion.Geometry.ParameterIntegralDerivatives
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicPrimitive

namespace OAI

/-! Periodic integration preserves weighted slow-parameter estimates. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.SmoothParameterIntegral
open PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Every slow parameter derivative commutes with the normalized primitive. -/
theorem partialIterated_primitive {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (p : P) (x : ℝ) :
    partialIterated n (fun z : P × ℝ => primitive (fun t => F (z.1, t)) z.2) (p, x) =
      primitive (fun t => partialIterated n F (p, t)) x := by
  let G : P × ℝ → E := fun z => rawPrimitive (fun t => F (z.1, t)) z.2
  have hG : ContDiff ℝ ∞ G := contDiff_rawPrimitive_joint hF
  have hr : ContDiff ℝ ∞ (fun q => rawPrimitive (fun t => F (q, t)) x) :=
    contDiff_integral hF 0 x
  have hm : ContDiff ℝ ∞ (fun q => ∫ t in (0 : ℝ)..1, G (q, t)) :=
    contDiff_integral hG 0 1
  change iteratedFDeriv ℝ n
    ((fun q => rawPrimitive (fun t => F (q, t)) x) -
      (fun q => ∫ t in (0 : ℝ)..1, G (q, t))) p = _
  rw [iteratedFDeriv_sub_apply ((hr.of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt)
    ((hm.of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt)]
  change iteratedFDeriv ℝ n (fun q => ∫ t in (0 : ℝ)..x, F (q, t)) p -
    iteratedFDeriv ℝ n (fun q => ∫ t in (0 : ℝ)..1, G (q, t)) p = _
  rw [iteratedFDeriv_integral hF 0 x, iteratedFDeriv_integral hG 0 1]
  change (∫ t in (0 : ℝ)..x, partialIterated n F (p, t)) -
    (∫ t in (0 : ℝ)..1, partialIterated n G (p, t)) =
    (∫ t in (0 : ℝ)..x, partialIterated n F (p, t)) -
      (∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..t, partialIterated n F (p, r))
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact iteratedFDeriv_integral hF 0 t n p

end ClosedSurfaceR4.SmoothParameterIntegral

namespace ClosedSurfaceR4.WeightedEstimates
open SmoothParameterIntegral PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem weighted_rawPrimitive {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set P} (hU : IsOpen U) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (m : ℕ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j F (p, t)‖ ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    WeightedBound U s m C (fun p => rawPrimitive (fun t => F (p, t)) x) := by
  have h := weighted_parameter_integral hF hU hs m 0 x (fun j hj p hp t ht =>
    hb j hj p hp t (by
      rw [Set.uIcc_of_le hx.1] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩))
  apply h.mono_const
  simpa only [sub_zero, abs_of_nonneg hx.1] using mul_le_of_le_one_right hC hx.2

/-- The normalized primitive has weighted parameter norm at most twice
that of its input, uniformly over a fundamental period and at every order. -/
theorem weighted_periodicPrimitive {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set P} (hU : IsOpen U) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (m : ℕ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j F (p, t)‖ ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    WeightedBound U s m (2 * C) (fun p => primitive (fun t => F (p, t)) x) := by
  let G : P × ℝ → E := fun z => rawPrimitive (fun t => F (z.1, t)) z.2
  have hG : ContDiff ℝ ∞ G := contDiff_rawPrimitive_joint hF
  have hGb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j G (p, t)‖ ≤ C := by
    intro j hj p hp t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hh := weighted_rawPrimitive hF hU hs hC m hb ht j hj p hp
    have hGt : ContDiff ℝ ∞ (fun q => G (q, t)) :=
      hG.comp (contDiff_id.prodMk contDiff_const)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((hGt.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt) hp] at hh
    exact hh
  have hmean := weighted_parameter_integral hG hU hs m 0 1 hGb
  simp only [sub_zero, abs_one, mul_one] at hmean
  have hraw := weighted_rawPrimitive hF hU hs hC m hb hx
  have hr : ContDiffOn ℝ ∞ (fun p => rawPrimitive (fun t => F (p, t)) x) U :=
    (hG.comp (contDiff_id.prodMk contDiff_const)).contDiffOn
  have hm : ContDiffOn ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, G (p, t)) U :=
    (contDiff_integral hG 0 1).contDiffOn
  have h := hraw.sub hU.uniqueDiffOn hs.le hr hm hmean
  convert h using 1 <;> (first | rfl | ring)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
