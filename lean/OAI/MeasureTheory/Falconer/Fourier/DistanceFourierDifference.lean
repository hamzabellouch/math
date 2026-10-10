import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate

noncomputable def distanceDifferenceMeasure (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun z : ℝ × ℝ => z.1-z.2)

instance distanceDifferenceMeasure_finite (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (distanceDifferenceMeasure μ) := by
  unfold distanceDifferenceMeasure
  infer_instance

theorem integral_distanceDifferenceMeasure (μ : Measure ℝ) (F : ℝ → ℂ)
    (hF : StronglyMeasurable F) :
    (∫ s, F s ∂distanceDifferenceMeasure μ) = ∫ z, F (z.1-z.2) ∂μ.prod μ :=
  integral_map_of_stronglyMeasurable (by fun_prop) hF

theorem charFun_distanceDifferenceMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    charFun (distanceDifferenceMeasure μ) r = (‖charFun μ r‖^2:ℂ) := by
  rw [charFun_apply_real,integral_distanceDifferenceMeasure μ _ (by fun_prop)]
  have he : (fun z : ℝ × ℝ => Complex.exp ((r*(z.1-z.2):ℝ)*Complex.I)) =
      fun z => Complex.exp ((r*z.1:ℝ)*Complex.I) *
        conj (Complex.exp ((r*z.2:ℝ)*Complex.I)) := by
    funext z
    rw [← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  simp only [Complex.ofReal_mul] at he
  rw [he,integral_prod_mul (fun x : ℝ => Complex.exp ((r:ℂ)*x*Complex.I))
    (fun y : ℝ => conj (Complex.exp ((r:ℂ)*y*Complex.I))),integral_conj,← charFun_apply_real,Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq (charFun μ r)

theorem integral_charFun_scale_swap (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    (∫ s, charFun μ (A*s) ∂ν) = ∫ r, charFun ν (A*r) ∂μ := by
  simp only [charFun_apply_real]
  rw [integral_integral_swap]
  · apply integral_congr_ae
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with s
    congr 2
    push_cast
    ring
  · exact (integrable_const (1:ℝ)).mono (by fun_prop)
      (by filter_upwards with z; simp [Function.uncurry,Complex.norm_exp])

end PlanarFalconer

end OAI
