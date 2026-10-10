import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! Nonnegative increasing finite sums with a uniform square-integral
bound have a finite L² limit almost everywhere. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_monotone_L2_limit {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} (hf : ∀ n, Measurable (f n))
    (hf2 : ∀ n, MemLp (f n) 2 μ) (hf0 : ∀ n x, 0 ≤ f n x)
    (hmono : ∀ x, Monotone (fun n => f n x)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, (∫ x, f n x^2 ∂μ) ≤ B) :
    ∃ P : X → ℝ, Measurable P ∧ (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧
      (∫ x, P x^2 ∂μ) ≤ B ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (P x)) ∧ ∀ n, f n x ≤ P x) := by
  let Q := fun x => ⨆ n, ENNReal.ofReal (f n x)
  have hQ : Measurable Q := Measurable.iSup (fun n => (hf n).ennreal_ofReal)
  have ht (x : X) : Tendsto (fun n => ENNReal.ofReal (f n x)) atTop (𝓝 (Q x)) :=
    tendsto_atTop_iSup (fun i j hij => ENNReal.ofReal_le_ofReal (hmono x hij))
  have hi : (∫⁻ x, Q x^2 ∂μ) ≤ ENNReal.ofReal B := by
    have hconv := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
      (fun n => ((hf n).ennreal_ofReal.pow_const 2).aemeasurable)
      (Eventually.of_forall (fun x i j hij => pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hmono x hij)) 2))
      (Eventually.of_forall (fun x => ENNReal.Tendsto.pow (ht x)))
    apply le_of_tendsto hconv
    apply Eventually.of_forall
    intro n
    have he : (∫⁻ x, ENNReal.ofReal (f n x)^2 ∂μ) = ENNReal.ofReal (∫ x, f n x^2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hf2 n).integrable_sq
        (Eventually.of_forall (fun x => sq_nonneg (f n x)))]
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_pow (hf0 n x) 2).symm
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfinite : ∀ᵐ x ∂μ, Q x ≠ ∞ := by
    filter_upwards [ae_lt_top (hQ.pow_const 2) (ne_of_lt (hi.trans_lt ENNReal.ofReal_lt_top))] with x hx
    intro he
    simp only [he,ENNReal.top_pow (by norm_num : (2:ℕ) ≠ 0),lt_self_iff_false] at hx
  let P := fun x => (Q x).toReal
  have hP : Measurable P := hQ.ennreal_toReal
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (P x)) ∧ ∀ n, f n x ≤ P x := by
    filter_upwards [hfinite] with x hx
    constructor
    · have h := (ENNReal.continuousAt_toReal hx).tendsto.comp (ht x)
      simpa only [Function.comp_def,ENNReal.toReal_ofReal (hf0 _ _)] using h
    · intro n
      have hle : ENNReal.ofReal (f n x) ≤ Q x := le_iSup (fun n => ENNReal.ofReal (f n x)) n
      simpa only [ENNReal.toReal_ofReal (hf0 _ _)] using ENNReal.toReal_mono hx hle
  have hPint : (∫⁻ x, ENNReal.ofReal (P x^2) ∂μ) ≤ ENNReal.ofReal B := by
    apply le_trans _ hi
    apply lintegral_mono
    intro x
    change ENNReal.ofReal ((Q x).toReal^2) ≤ Q x^2
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
  have hPi : Integrable (fun x => P x^2) μ :=
    ⟨(hP.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => sq_nonneg (P x)))).mpr
        (hPint.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨P,hP,(fun _ => ENNReal.toReal_nonneg),
    (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).mpr hPi,?_,hlim⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hPi (Eventually.of_forall (fun x => sq_nonneg (P x)))] at hPint
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hPint

end CircleDomainRigidity

end

end OAI
