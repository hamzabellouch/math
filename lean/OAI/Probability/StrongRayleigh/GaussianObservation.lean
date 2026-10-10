import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336AdditiveD139
namespace GaussianObservation

theorem gaussianPDFReal_binary_shift (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) (y : ℝ) :
    gaussianPDFReal ((t : ℝ) * boolReal b) t y =
      Real.exp ((y - (t : ℝ) / 2) * boolReal b) * gaussianPDFReal 0 t y := by
  cases b with
  | false => simp [boolReal]
  | true =>
    simp only [boolReal, ite_true, mul_one]
    have ht' : (t : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr ht
    have he : -(y - (t : ℝ)) ^ 2 / (2 * (t : ℝ)) =
        (y - (t : ℝ) / 2) + (-y ^ 2 / (2 * (t : ℝ))) := by
      field_simp [ht']
      ring
    simp only [gaussianPDFReal, sub_zero]
    rw [he, Real.exp_add]
    ring

theorem gaussianPDF_binary_shift (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) (y : ℝ) :
    gaussianPDF ((t : ℝ) * boolReal b) t y =
      ENNReal.ofReal (Real.exp ((y - (t : ℝ) / 2) * boolReal b)) * gaussianPDF 0 t y := by
  rw [gaussianPDF, gaussianPDFReal_binary_shift t ht]
  exact ENNReal.ofReal_mul (Real.exp_nonneg _)

def likelihood {F : Type u_1} [Fintype F] (t : ℝ≥0) (x : F → Bool) (y : F → ℝ) : ℝ :=
  Real.exp (∑ i, (y i - (t : ℝ) / 2) * boolReal (x i))

lemma likelihood_pos {F : Type u_2} [Fintype F] (t : ℝ≥0) (x : F → Bool) (y : F → ℝ) :
    0 < likelihood t x y := Real.exp_pos _

lemma measurable_likelihood {F : Type u_3} [Fintype F] (t : ℝ≥0) (x : F → Bool) :
    Measurable (likelihood t x) := by
  unfold likelihood
  fun_prop

theorem gaussianPDFReal_product_binary_shift {F : Type u_4} [Fintype F]
    (t : ℝ≥0) (ht : t ≠ 0) (x : F → Bool) (y : F → ℝ) :
    (∏ i, gaussianPDFReal ((t : ℝ) * boolReal (x i)) t (y i)) =
      likelihood t x y * ∏ i, gaussianPDFReal 0 t (y i) := by
  classical
  simp_rw [gaussianPDFReal_binary_shift t ht]
  rw [Finset.prod_mul_distrib, likelihood, Real.exp_sum]

theorem gaussianReal_binary_shift (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) :
    gaussianReal ((t : ℝ) * boolReal b) t =
      (gaussianReal 0 t).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((y - (t : ℝ) / 2) * boolReal b))) := by
  rw [gaussianReal_of_var_ne_zero _ ht, gaussianReal_of_var_ne_zero _ ht,
    ← withDensity_mul volume (measurable_gaussianPDF 0 t) (by fun_prop)]
  congr 1
  funext y
  rw [gaussianPDF_binary_shift t ht]
  exact mul_comm _ _

theorem pi_withDensity_ofReal {F : Type u_5} [Fintype F]
    (μ : F → Measure ℝ) [∀ i, SigmaFinite (μ i)] (f : F → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hnonneg : ∀ i y, 0 ≤ f i y) :
    Measure.pi (fun i => (μ i).withDensity (fun y => ENNReal.ofReal (f i y))) =
      (Measure.pi μ).withDensity (fun y => ENNReal.ofReal (∏ i, f i (y i))) := by
  classical
  have : ∀ i, IsFiniteMeasure ((μ i).withDensity (fun y => ENNReal.ofReal (f i y))) :=
    fun i => isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (hnonneg i))).mp (hf i).2).ne
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hp : Integrable (fun y : F → ℝ => ∏ i, f i (y i))
      (Measure.pi (fun i => (μ i).restrict (s i))) :=
    Integrable.fintype_prod (fun i => (hf i).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hp
    (ae_of_all _ (fun y => Finset.prod_nonneg (fun i _ => hnonneg i (y i)))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hnonneg i))

lemma integrable_binary_likelihood (t : ℝ≥0) (ht : t ≠ 0) (b : Bool) :
    Integrable (fun y => Real.exp ((y - (t : ℝ) / 2) * boolReal b))
      (gaussianReal 0 t) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => Real.exp_nonneg _))]
  have hm := congrArg (fun ν : Measure ℝ => ν Set.univ) (gaussianReal_binary_shift t ht b)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
  rw [← hm]
  exact ENNReal.one_lt_top

theorem gaussianReal_pi_binary_shift {F : Type u_6} [Fintype F]
    (t : ℝ≥0) (ht : t ≠ 0) (x : F → Bool) :
    Measure.pi (fun i => gaussianReal ((t : ℝ) * boolReal (x i)) t) =
      (Measure.pi (fun _ : F => gaussianReal 0 t)).withDensity
        (fun y => ENNReal.ofReal (likelihood t x y)) := by
  classical
  simp_rw [gaussianReal_binary_shift t ht]
  rw [pi_withDensity_ofReal _ _ (fun i => integrable_binary_likelihood t ht (x i))
    (fun _ _ => Real.exp_nonneg _)]
  congr 1
  funext y
  congr 1
  exact (Real.exp_sum _ _).symm

end GaussianObservation
end Problem336AdditiveD139

end

end OAI
