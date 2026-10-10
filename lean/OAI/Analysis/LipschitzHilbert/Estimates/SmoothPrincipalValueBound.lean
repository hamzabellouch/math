import OAI.Analysis.LipschitzHilbert.Estimates.ShortTransformMeasurable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

namespace OAI

/-! Uniform truncation bounds pass to the symmetric principal value.
Fatou's lemma yields the strong bound, and Chebyshev's inequality gives
its weak `(2,2)` consequence. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace LipschitzHilbert

theorem smoothPrincipalValue_eLpNorm_le
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞}
    (hbound : ∀ ε : ℝ, 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C) :
    eLpNorm (smoothPrincipalValue v a f) 2 volume ≤ C := by
  let ε := fun n : ℕ => a/(((n+1:ℕ):ℝ)+1)
  have hpos (n : ℕ) : 0 < ε n := div_pos ha (by positivity)
  have hlt (n : ℕ) : ε n < a := by
    apply (div_lt_iff₀ (by positivity : 0 < ((n+1:ℕ):ℝ)+1)).mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htend : Tendsto ε atTop (𝓝 (0:ℝ)) := by
    have hs := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.comp
      (tendsto_add_atTop_nat 1)
    simpa only [ε,div_eq_mul_inv,one_mul,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := a)).mul hs
  have hright : Tendsto ε atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend,Eventually.of_forall hpos⟩
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall (fun n => hbound (ε n) (hpos n) (hlt n)))
    (fun n => (shortTransform_continuous hv hf.continuous (hpos n)
      (hlt n).le).aestronglyMeasurable)
    (smoothPrincipalValue_measurable hv hf ha).aestronglyMeasurable
  exact Eventually.of_forall fun x =>
    (shortTransform_tendsto_smoothPrincipalValue v hf ha x).comp hright

theorem smoothPrincipalValue_memLp
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞} (hC : C < ∞)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C) :
    MemLp (smoothPrincipalValue v a f) 2 volume :=
  (smoothPrincipalValue_eLpNorm_le hv hf ha hbound).trans_lt hC

theorem smoothPrincipalValue_weak_two
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞}
    (hbound : ∀ ε : ℝ, 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C)
    {level : ℝ≥0∞} (hlevel : level ≠ 0) (hleveltop : level ≠ ∞) :
    volume {x | level < ‖smoothPrincipalValue v a f x‖ₑ} ≤ level⁻¹ ^ 2 * C ^ 2 := by
  have hmarkov := meas_ge_le_mul_pow_eLpNorm_enorm (p := (2:ℝ≥0∞)) volume
    (by norm_num) (by norm_num) hlevel (by exact fun h => (hleveltop h).elim)
    (f := smoothPrincipalValue v a f)
  have hnorm := smoothPrincipalValue_eLpNorm_le hv hf ha hbound
  calc
    volume {x | level < ‖smoothPrincipalValue v a f x‖ₑ} ≤
        volume {x | level ≤ ‖smoothPrincipalValue v a f x‖ₑ} :=
      measure_mono (by
        intro x hx
        change level < ‖smoothPrincipalValue v a f x‖ₑ at hx
        change level ≤ ‖smoothPrincipalValue v a f x‖ₑ
        exact le_of_lt hx)
    _ ≤ level⁻¹ ^ 2 * eLpNorm (smoothPrincipalValue v a f) 2 volume ^ 2 := by
      simpa using hmarkov
    _ ≤ level⁻¹ ^ 2 * C ^ 2 := by gcongr

end LipschitzHilbert

end

end OAI
