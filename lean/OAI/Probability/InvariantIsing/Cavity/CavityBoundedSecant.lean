import OAI.Probability.InvariantIsing.Pressure.RandomBoundedDerivative
import Mathlib.Probability.Moments.SubGaussian

namespace OAI

/-! Bounded Gibbs tests can be compared through logarithmic generating
functions. Hoeffding's bound makes the finite-difference error uniform
over the reference probability, including cavity cutoffs. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma cavity_bounded_cgf_secant {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Y : X → ℝ) (hY : Measurable Y)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, |Y x| ≤ B) (s : ℝ) :
    s * (∫ x, Y x ∂ν) ≤ cgf Y ν s ∧
      cgf Y ν s ≤ s * (∫ x, Y x ∂ν) + B ^ 2 * s ^ 2 / 2 := by
  have hi := exp_mul_integrable_of_bound ν hY hbound s
  have hpos : 0 < mgf Y ν s := MeasureTheory.integral_exp_pos hi
  have hlow : s * (∫ x, Y x ∂ν) ≤ cgf Y ν s := by
    apply (Real.le_log_iff_exp_le hpos).mpr
    have hh := exp_integral_le_partition ((bounded_integrable ν hY hbound).const_mul s) hi
    simpa only [integral_const_mul, mgf] using hh
  have hsub := hasSubgaussianMGF_of_mem_Icc hY.aemeasurable
    (ae_of_all ν (fun x => abs_le.mp (hbound x)))
  have hu := hsub.cgf_le s
  have hshift : cgf (fun x => Y x - ∫ y, Y y ∂ν) ν s =
      cgf Y ν s - s * (∫ x, Y x ∂ν) := by
    change Real.log (mgf (fun x => Y x + -(∫ y, Y y ∂ν)) ν s) = _
    rw [mgf_add_const, Real.log_mul hpos.ne' (Real.exp_ne_zero _), Real.log_exp]
    unfold cgf
    ring
  rw [hshift] at hu
  have hn : (((‖B - -B‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = B ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
      Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (add_nonneg hB hB)]
    norm_num
  rw [hn] at hu
  exact ⟨hlow, by linarith⟩

lemma cavity_secant_comparison_algebra {a b F G B ε s : ℝ} (hs : 0 < s)
    (hF : s * a ≤ F ∧ F ≤ s * a + B ^ 2 * s ^ 2 / 2)
    (hG : s * b ≤ G ∧ G ≤ s * b + B ^ 2 * s ^ 2 / 2)
    (hFG : |F - G| ≤ ε) :
    |a - b| ≤ ε / s + B ^ 2 * s / 2 := by
  have hε := abs_le.mp hFG
  have hh : |s * (a - b)| ≤ ε + B ^ 2 * s ^ 2 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hF.1, hF.2, hG.1, hG.2]
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    |a - b| * s = |s * (a - b)| := by rw [abs_mul, abs_of_pos hs, mul_comm]
    _ ≤ ε + B ^ 2 * s ^ 2 / 2 := hh
    _ = (ε / s + B ^ 2 * s / 2) * s := by field_simp

theorem cavity_bounded_random_test_compare {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν η : Ω → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (η ω)]
    (Y : Ω → X → ℝ) (hY : Measurable (Function.uncurry Y))
    {B ε s : ℝ} (hB : 0 ≤ B) (hbound : ∀ ω x, |Y ω x| ≤ B) (hs : 0 < s)
    (hcgf : |(∫ ω, cgf (Y ω) (ν ω) s ∂P) -
      ∫ ω, cgf (Y ω) (η ω) s ∂P| ≤ ε) :
    |(∫ ω, ∫ x, Y ω x ∂ν ω ∂P) - ∫ ω, ∫ x, Y ω x ∂η ω ∂P| ≤
      ε / s + B ^ 2 * s / 2 := by
  have hiν : Integrable (fun ω => ∫ x, Y ω x ∂ν ω) P := by
    simpa only [zero_mul, tilted_const] using
      integrable_bounded_random_tilted_mean P ν hν Y hY B hbound 0
  have hiη : Integrable (fun ω => ∫ x, Y ω x ∂η ω) P := by
    simpa only [zero_mul, tilted_const] using
      integrable_bounded_random_tilted_mean P η hη Y hY B hbound 0
  have hbounds (μ : Ω → Measure X) (hμ : Measurable μ)
      [∀ ω, IsProbabilityMeasure (μ ω)]
      (hi : Integrable (fun ω => ∫ x, Y ω x ∂μ ω) P) :
      s * (∫ ω, ∫ x, Y ω x ∂μ ω ∂P) ≤ ∫ ω, cgf (Y ω) (μ ω) s ∂P ∧
      (∫ ω, cgf (Y ω) (μ ω) s ∂P) ≤
        s * (∫ ω, ∫ x, Y ω x ∂μ ω ∂P) + B ^ 2 * s ^ 2 / 2 := by
    have hic := integrable_bounded_random_cgf P μ hμ (Function.uncurry Y) hY B hbound s
    have hb (ω : Ω) := cavity_bounded_cgf_secant (μ ω) (Y ω)
      (hY.comp (measurable_const.prodMk measurable_id)) hB (hbound ω) s
    constructor
    · have hh := integral_mono (hi.const_mul s) hic (fun ω => (hb ω).1)
      simpa only [integral_const_mul, Function.uncurry_apply_pair] using hh
    · have hh := integral_mono hic ((hi.const_mul s).add (integrable_const _))
        (fun ω => (hb ω).2)
      simpa only [Pi.add_apply, Function.uncurry_apply_pair,
        integral_add (hi.const_mul s) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul] using hh
  exact cavity_secant_comparison_algebra hs (hbounds ν hν hiν) (hbounds η hη hiη) hcgf

end InvariantIsing

end

end OAI
