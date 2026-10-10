import OAI.Analysis.LipschitzHilbert.Estimates.MaskComparison
import OAI.Analysis.LipschitzHilbert.Estimates.WeakTwoIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Integrate the actual finite mask error using the weak L2 top count.
Integrability is proved from the distribution bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem mask_error_integral {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (F : ι → Ω → EuclideanSpace ℂ κ) (mask weight : ι → Ω → ℝ)
    (hFmeas : ∀ i, Measurable (F i)) (hmmeas : ∀ i, Measurable (mask i))
    (hwmeas : ∀ i, Measurable (weight i)) (T ε K : ℝ)
    (hT : 0 ≤ T) (hε : 0 ≤ ε) (hK : 0 < K)
    (hw : ∀ i x, 0 ≤ weight i x)
    (hF : ∀ᵐ x ∂μ, ∀ i, ‖F i x‖ ≤ T*(weight i x)^8)
    (hmask : ∀ i x, |1-mask i x| * T*(weight i x)^7 ≤ ε)
    (hweak : ∀ s : ℝ, 0 < s →
      μ {x | s < ∑ i, weight i x} ≤ ENNReal.ofReal (K^2/s^2)) :
    Integrable (fun x => ‖(∑ i, F i x)-(∑ i, mask i x • F i x)‖) μ ∧
      (∫ x, ‖(∑ i, F i x)-(∑ i, mask i x • F i x)‖ ∂μ) ≤
        2*ε*K*Real.sqrt ((μ univ).toReal) := by
  let error : Ω → EuclideanSpace ℂ κ := fun x => (∑ i, F i x)-(∑ i, mask i x • F i x)
  let count : Ω → ℝ := fun x => ∑ i, weight i x
  have he : Measurable error := by
    apply Measurable.sub
    · exact Finset.measurable_sum _ (fun i _ => hFmeas i)
    · exact Finset.measurable_sum _ (fun i _ => (hmmeas i).smul (hFmeas i))
  have hc : Measurable count := Finset.measurable_sum _ (fun i _ => hwmeas i)
  have hc0 (x : Ω) : 0 ≤ count x := Finset.sum_nonneg (fun i _ => hw i x)
  have hp : ∀ᵐ x ∂μ, ‖error x‖ ≤ ε*count x := hF.mono fun x hx =>
    norm_sum_sub_mask_le (fun i => F i x) (fun i => mask i x) (fun i => weight i x)
      T ε hT hε (fun i => hw i x) hx (fun i => hmask i x)
  have hcount := weak_two_lintegral μ hμ count hc.aemeasurable
    (Filter.Eventually.of_forall hc0) K hK hweak
  have hb : (∫⁻ x, ENNReal.ofReal ‖error x‖ ∂μ) ≤
      ENNReal.ofReal (2*ε*K*Real.sqrt ((μ univ).toReal)) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (ε*count x) ∂μ :=
        lintegral_mono_ae (hp.mono fun _ h => ENNReal.ofReal_le_ofReal h)
      _ = ENNReal.ofReal ε*(∫⁻ x, ENNReal.ofReal (count x) ∂μ) := by
        simp_rw [ENNReal.ofReal_mul hε]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ε*ENNReal.ofReal (2*K*Real.sqrt ((μ univ).toReal)) :=
        mul_le_mul' le_rfl hcount
      _ = _ := by rw [← ENNReal.ofReal_mul hε]; congr 1; ring
  have hint : Integrable (fun x => ‖error x‖) μ :=
    ⟨he.norm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun x => norm_nonneg (error x)))).mpr
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hint,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => norm_nonneg (error x)))] at hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg (error x))),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*ε*K*Real.sqrt ((μ univ).toReal))] using hreal

end LipschitzHilbert

end

end OAI
