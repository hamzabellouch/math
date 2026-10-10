import OAI.Analysis.KadisonKastler.PoissonVectorAverage
import OAI.Analysis.KadisonKastler.SmoothedNormalizerLimit
import Mathlib.Analysis.Complex.Circle

namespace OAI

/-! # The strong-star boundary comparison used in modular smoothing

The demodulated Cauchy averages are actual bounded operators. Their products
converge strongly-* even though the polar smoothing paths need not converge.
-/

namespace KadisonKastler

open Filter MeasureTheory
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem norm_unitary_le_one' (v : unitary (H →L[ℂ] H)) :
    ‖(v : H →L[ℂ] H)‖ ≤ 1 := by
  nontriviality (H →L[ℂ] H)
  exact (CStarRing.norm_coe_unitary v).le

def modulatedUnitaryField (W : ℝ → unitary (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  (Circle.exp t : ℂ) • (W t : H →L[ℂ] H)

theorem modulatedUnitaryField_continuous (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (x : H) :
    Continuous (fun t => modulatedUnitaryField W t x) :=
  (continuous_subtype_val.comp Circle.exp.continuous).smul (hW x)

theorem modulatedUnitaryField_star_continuous (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x)) (x : H) :
    Continuous (fun t => star (modulatedUnitaryField W t) x) := by
  have hc : Continuous (fun t : ℝ => star (Circle.exp t : ℂ)) :=
    (continuous_subtype_val.comp Circle.exp.continuous).star
  have he (t : ℝ) : star (modulatedUnitaryField W t) x =
      star (Circle.exp t : ℂ) • star (W t : H →L[ℂ] H) x := by
    simp only [modulatedUnitaryField, star_smul, smul_apply]
  simp_rw [he]
  exact hc.smul (hW x)

theorem norm_modulatedUnitaryField_le_one (W : ℝ → unitary (H →L[ℂ] H)) (t : ℝ) :
    ‖modulatedUnitaryField W t‖ ≤ 1 := by
  simpa only [modulatedUnitaryField, norm_smul, Circle.norm_coe, one_mul] using
    norm_unitary_le_one' (W t)

/-- The scalar factor is `exp(-i(t+ir)) = exp(r) exp(-it)`. -/
def poissonBoundaryApprox (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (t r : ℝ) : H →L[ℂ] H :=
  ((Real.exp r : ℂ) * star (Circle.exp t : ℂ)) •
    poissonVectorAverage (modulatedUnitaryField W)
      (modulatedUnitaryField_continuous W hW) 1 (norm_modulatedUnitaryField_le_one W) t r

theorem norm_poissonBoundaryApprox_le (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (t r : ℝ) :
    ‖poissonBoundaryApprox W hW t r‖ ≤ Real.exp r := by
  have hb := norm_probabilityOperatorIntegral_le (ProbabilityTheory.cauchyMeasure 0 1)
    (fun s => modulatedUnitaryField W (t + r * s))
    (fun x => ((modulatedUnitaryField_continuous W hW x).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable) zero_le_one
    (ae_of_all _ fun _ => norm_modulatedUnitaryField_le_one W _)
  have hs : ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r := by
    rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]
  rw [poissonBoundaryApprox, norm_smul, hs]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos r).le).trans_eq (mul_one _)

theorem poissonBoundaryApprox_tendsto (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (t : ℝ) (x : H) :
    Tendsto (fun r => poissonBoundaryApprox W hW t r x) (𝓝 0)
      (𝓝 ((W t : H →L[ℂ] H) x)) := by
  have hs : Tendsto (fun r : ℝ => (Real.exp r : ℂ) * star (Circle.exp t : ℂ))
      (𝓝 0) (𝓝 (star (Circle.exp t : ℂ))) := by
    simpa only [Function.comp_apply, Real.exp_zero, Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.comp Real.continuous_exp).continuousAt (x := 0)).tendsto.mul_const
        (star (Circle.exp t : ℂ))
  have h := hs.smul (poissonVectorAverage_tendsto (modulatedUnitaryField W)
    (modulatedUnitaryField_continuous W hW) 1 (norm_modulatedUnitaryField_le_one W) t x)
  have hz : star (Circle.exp t : ℂ) * (Circle.exp t : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul']
    simp only [Circle.norm_coe, one_pow, Complex.ofReal_one]
  simpa only [poissonBoundaryApprox, smul_apply, modulatedUnitaryField,
    smul_smul, hz, one_smul] using h

theorem poissonBoundaryApprox_star_tendsto (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hWs : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x)) (t : ℝ) (x : H) :
    Tendsto (fun r => star (poissonBoundaryApprox W hW t r) x) (𝓝 0)
      (𝓝 (star (W t : H →L[ℂ] H) x)) := by
  have hs : Tendsto (fun r : ℝ => star ((Real.exp r : ℂ) * star (Circle.exp t : ℂ)))
      (𝓝 0) (𝓝 (Circle.exp t : ℂ)) := by
    simpa only [Function.comp_apply, Real.exp_zero, Complex.ofReal_one, one_mul, star_star] using
      (((Complex.continuous_ofReal.comp Real.continuous_exp).continuousAt (x := 0)).tendsto.mul_const
        (star (Circle.exp t : ℂ))).star
  have h := hs.smul (poissonVectorAverage_star_tendsto (modulatedUnitaryField W)
    (modulatedUnitaryField_continuous W hW) (modulatedUnitaryField_star_continuous W hWs)
      1 (norm_modulatedUnitaryField_le_one W) t x)
  have hz : (Circle.exp t : ℂ) * star (Circle.exp t : ℂ) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.conj_mul']
    simp only [Circle.norm_coe, one_pow, Complex.ofReal_one]
  simpa only [poissonBoundaryApprox, star_smul, smul_apply, modulatedUnitaryField,
    smul_smul, hz, one_smul] using h

omit [CompleteSpace H] in
/-- Multiplication is strongly continuous on a family with bounded left
operator norms; the right arguments may also vary. -/
theorem tendsto_operator_comp_of_uniform_bound {ι : Type*} {l : Filter ι}
    (A B : ι → H →L[ℂ] H) (T S : H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ᶠ i in l, ‖A i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x)))
    (hB : ∀ x, Tendsto (fun i => B i x) l (𝓝 (S x))) (x : H) :
    Tendsto (fun i => (A i * B i) x) l (𝓝 ((T * S) x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hconstS : Tendsto (fun _ : ι => S x) l (𝓝 (S x)) := tendsto_const_nhds
  have hconstT : Tendsto (fun _ : ι => T (S x)) l (𝓝 (T (S x))) := tendsto_const_nhds
  have h₁ : Tendsto (fun i => C * ‖B i x - S x‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (((hB x).sub hconstS).norm.const_mul C)
  have h₂ : Tendsto (fun i => ‖A i (S x) - T (S x)‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hA (S x)).sub hconstT).norm
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [add_zero] using h₁.add h₂)
  filter_upwards [hbound] with i hi
  have he : (A i * B i) x - (T * S) x =
      A i (B i x - S x) + (A i (S x) - T (S x)) := by
    simp only [mul_apply_eq_comp, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))) le_rfl)

def poissonBoundaryQuotient (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (t r : ℝ) : H →L[ℂ] H :=
  poissonBoundaryApprox W hW t r * star (poissonBoundaryApprox W hW 0 r)

theorem norm_poissonBoundaryQuotient_le (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (t r : ℝ) :
    ‖poissonBoundaryQuotient W hW t r‖ ≤ Real.exp r * Real.exp r := by
  apply (norm_mul_le _ _).trans
  exact mul_le_mul (norm_poissonBoundaryApprox_le W hW t r)
    ((norm_star _).le.trans (norm_poissonBoundaryApprox_le W hW 0 r))
    (norm_nonneg _) (Real.exp_pos _).le

/-- The product comparison used in the UCP limit converges strongly-* at
all fixed times. -/
theorem poissonBoundaryQuotient_tendsto (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hWs : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x))
    (hzero : W 0 = 1) (t : ℝ) (x : H) :
    Tendsto (fun r => poissonBoundaryQuotient W hW t r x) (𝓝 0)
      (𝓝 ((W t : H →L[ℂ] H) x)) ∧
    Tendsto (fun r => star (poissonBoundaryQuotient W hW t r) x) (𝓝 0)
      (𝓝 (star (W t : H →L[ℂ] H) x)) := by
  have hbound (s : ℝ) : ∀ᶠ r : ℝ in 𝓝 0,
      ‖poissonBoundaryApprox W hW s r‖ ≤ Real.exp 1 := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact (norm_poissonBoundaryApprox_le W hW s r).trans
      (Real.exp_le_exp.mpr hr.le)
  constructor
  · have h := tendsto_operator_comp_of_uniform_bound
      (fun r => poissonBoundaryApprox W hW t r)
      (fun r => star (poissonBoundaryApprox W hW 0 r))
      (W t) (star (W 0 : H →L[ℂ] H)) (Real.exp 1) (hbound t)
      (poissonBoundaryApprox_tendsto W hW t)
      (poissonBoundaryApprox_star_tendsto W hW hWs 0) x
    simpa only [poissonBoundaryQuotient, hzero, OneMemClass.coe_one,
      star_one, mul_one] using h
  · have h := tendsto_operator_comp_of_uniform_bound
      (fun r => poissonBoundaryApprox W hW 0 r)
      (fun r => star (poissonBoundaryApprox W hW t r))
      (W 0) (star (W t : H →L[ℂ] H)) (Real.exp 1) (hbound 0)
      (poissonBoundaryApprox_tendsto W hW 0)
      (poissonBoundaryApprox_star_tendsto W hW hWs t) x
    simpa only [poissonBoundaryQuotient, star_mul, star_star, hzero,
      OneMemClass.coe_one, one_mul] using h

end

end KadisonKastler

end OAI
