import OAI.Analysis.LipschitzHilbert.Estimates.SmoothPrincipalValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! Spatial measurability for positive inner cutoffs and the symmetric
principal value. Continuity of the direction field suffices; its value
is frozen at each output point throughout the time integration. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

theorem shortTransform_continuous
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Continuous f)
    {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a) :
    Continuous (shortTransform v ε a f) := by
  let kernel := fun (x : DirectionPlane) (t : ℝ) =>
    (max ε t)⁻¹ • (f (sample v t x)-f (sample v (-t) x))
  have hk : Continuous kernel.uncurry := by
    have hn : Continuous (fun z : DirectionPlane×ℝ => (max ε z.2)⁻¹) :=
      (continuous_const.max continuous_snd).inv₀ (fun z =>
        (hε.trans_le (le_max_left ε z.2)).ne')
    have hs : Continuous (fun z : DirectionPlane×ℝ => sample v z.2 z.1) := by
      exact continuous_fst.sub (continuous_snd.smul (hv.comp continuous_fst))
    have hneg : Continuous (fun z : DirectionPlane×ℝ => sample v (-z.2) z.1) := by
      exact continuous_fst.sub (continuous_snd.neg.smul (hv.comp continuous_fst))
    exact hn.smul ((hf.comp hs).sub (hf.comp hneg))
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hk ε a
  have heq : shortTransform v ε a f = (fun x => ∫ t in ε..a, kernel x t) := by
    funext x
    unfold shortTransform
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hεa] at ht
    dsimp only [kernel]
    rw [max_eq_right ht.1]
  rw [heq]
  exact hc

theorem smoothPrincipalValue_measurable
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) : Measurable (smoothPrincipalValue v a f) := by
  let ε := fun n : ℕ => a/((n:ℝ)+1)
  have hpos (n : ℕ) : 0 < ε n := div_pos ha (by positivity)
  have hle (n : ℕ) : ε n ≤ a := by
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htend : Tendsto ε atTop (𝓝 (0:ℝ)) := by
    simpa only [ε,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_const_nhds (x := a)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hright : Tendsto ε atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend,Eventually.of_forall hpos⟩
  apply measurable_of_tendsto_metrizable
    (fun n => (shortTransform_continuous hv hf.continuous (hpos n) (hle n)).measurable)
  apply tendsto_pi_nhds.mpr
  intro x
  exact (shortTransform_tendsto_smoothPrincipalValue v hf ha x).comp hright

end LipschitzHilbert

end

end OAI
