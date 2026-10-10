import OAI.Probability.SLE.Stochastic.GaussianTaylorMean

namespace OAI

/-! The two-coordinate Gaussian generator estimate. Its error is uniform
under the compact smooth test bounds used for stopped planar Brownian motion. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def planarGaussianMean (δ : ℝ≥0) (f : ℝ × ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ y, ∫ x, f (a+x,b+y) ∂gaussianReal 0 δ ∂gaussianReal 0 δ

lemma planar_gaussian_generator_error
    (f : ℝ × ℝ → ℝ) (hf : Continuous f) (K : ℝ≥0)
    (hx : ∀ b, ContDiff ℝ 3 (fun a => f (a,b)))
    (hy : ∀ a, ContDiff ℝ 3 (fun b => f (a,b)))
    (hxb : ∀ a b j, j ≤ 3 → |iteratedDeriv j (fun x => f (x,b)) a| ≤ K)
    (hyb : ∀ a b j, j ≤ 3 → |iteratedDeriv j (fun y => f (a,y)) b| ≤ K)
    (hxy : ∀ a, LipschitzWith K (fun b => iteratedDeriv 2 (fun x => f (x,b)) a))
    (δ : ℝ≥0) (a b : ℝ) :
    |planarGaussianMean δ f a b-f (a,b)-(1/2:ℝ)*(δ:ℝ)*
      (iteratedDeriv 2 (fun x => f (x,b)) a+iteratedDeriv 2 (fun y => f (a,y)) b)| ≤
      (K:ℝ)*(δ:ℝ)*Real.sqrt δ*
        (2*standardGaussianAbsMoment 3+(1/2:ℝ)*standardGaussianAbsMoment 1) := by
  let μ := gaussianReal 0 δ
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let A (y : ℝ) := ∫ x, f (a+x,b+y) ∂μ
  let D (y : ℝ) := iteratedDeriv 2 (fun x => f (x,y)) a
  let R (y : ℝ) := A y-f (a,b+y)-(1/2:ℝ)*(δ:ℝ)*D (b+y)
  let e := (K:ℝ)*(δ:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 3
  have hμ : HasLaw (fun y : ℝ => y) μ μ := ⟨measurable_id.aemeasurable, by simp⟩
  have hfbound (x y : ℝ) : |f (x,y)| ≤ K := by
    simpa only [iteratedDeriv_zero] using hxb x y 0 (by decide)
  have hAi : Integrable A μ := by
    have hprod : Integrable (fun p : ℝ × ℝ => f (a+p.2,b+p.1)) (μ.prod μ) := by
      apply Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable K
      filter_upwards [] with p
      simpa only [Function.comp_apply,Real.norm_eq_abs] using hfbound (a+p.2) (b+p.1)
    exact hprod.integral_prod_left
  have hfi : Integrable (fun y => f (a,b+y)) μ := by
    apply Integrable.of_bound ((hy a).continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable K
    filter_upwards [] with y
    simpa only [Function.comp_apply,Pi.add_apply,id_eq,Real.norm_eq_abs] using hfbound a (b+y)
  have hDi : Integrable (fun y => D (b+y)) μ := by
    apply Integrable.of_bound ((hxy a).continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable K
    filter_upwards [] with y
    simpa only [Function.comp_apply,Pi.add_apply,id_eq,D,Real.norm_eq_abs] using hxb a (b+y) 2 (by decide)
  have hRi : Integrable R μ := (hAi.sub hfi).sub (hDi.const_mul _)
  have hR (y : ℝ) : |R y| ≤ e :=
    gaussian_second_taylor_integral (fun x => f (x,b+y)) (hx (b+y)) K
      (fun x j hj => hxb x (b+y) j hj) δ a
  have hRint : |∫ y, R y ∂μ| ≤ e := by
    simpa only [probReal_univ,mul_one,Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := R) (C := e)
        (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hR y)
  have hY : |(∫ y, f (a,b+y) ∂μ)-f (a,b)-(1/2:ℝ)*(δ:ℝ)*
      iteratedDeriv 2 (fun y => f (a,y)) b| ≤ e :=
    gaussian_second_taylor_integral (fun y => f (a,y)) (hy a) K
      (fun y j hj => hyb a y j hj) δ b
  have hDD : Integrable (fun y => D (b+y)-D b) μ := hDi.sub (integrable_const _)
  have hDDb (y : ℝ) : |D (b+y)-D b| ≤ (K:ℝ)*|y| := by
    simpa only [D,Real.dist_eq,add_sub_cancel_left] using (hxy a).dist_le_mul (b+y) b
  have hDDint : |(∫ y, D (b+y) ∂μ)-D b| ≤
      (K:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 1 := by
    have he : (∫ y, D (b+y)-D b ∂μ)=(∫ y, D (b+y) ∂μ)-D b := by
      rw [integral_sub hDi (integrable_const _)]
      simp
    rw [← he]
    calc
      |∫ y, D (b+y)-D b ∂μ| ≤ ∫ y, |D (b+y)-D b| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ) (fun y => D (b+y)-D b)
      _ ≤ ∫ y, (K:ℝ)*|y| ∂μ := integral_mono hDD.abs
        (by simpa only [pow_one] using (gaussian_abs_moment_integrable hμ 1 (by decide)).const_mul (K:ℝ)) hDDb
      _ = (K:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 1 := by
        rw [integral_const_mul]
        have he := gaussian_abs_moment hμ 1
        simp only [pow_one] at he
        rw [he]
        ring
  have he : planarGaussianMean δ f a b-f (a,b)-(1/2:ℝ)*(δ:ℝ)*
      (D b+iteratedDeriv 2 (fun y => f (a,y)) b) =
      (∫ y, R y ∂μ)+
      ((∫ y, f (a,b+y) ∂μ)-f (a,b)-(1/2:ℝ)*(δ:ℝ)*iteratedDeriv 2 (fun y => f (a,y)) b)+
      (1/2:ℝ)*(δ:ℝ)*((∫ y, D (b+y) ∂μ)-D b) := by
    have h0i : Integrable (fun y => A y-f (a,b+y)) μ := hAi.sub hfi
    have h1i : Integrable (fun y => (1/2:ℝ)*(δ:ℝ)*D (b+y)) μ := hDi.const_mul _
    have hRcalc : (∫ y, R y ∂μ)=(∫ y, A y ∂μ)-(∫ y, f (a,b+y) ∂μ)-
        (1/2:ℝ)*(δ:ℝ)*(∫ y, D (b+y) ∂μ) := by
      dsimp only [R]
      rw [integral_sub h0i h1i,integral_sub hAi hfi,integral_const_mul]
    rw [hRcalc]
    change (∫ y, A y ∂μ)-f (a,b)-(1/2:ℝ)*(δ:ℝ)*(D b+_)=_
    ring
  change |planarGaussianMean δ f a b-f (a,b)-(1/2:ℝ)*(δ:ℝ)*(D b+_)| ≤ _
  rw [he]
  calc
    _ ≤ |∫ y, R y ∂μ|+
        |(∫ y, f (a,b+y) ∂μ)-f (a,b)-(1/2:ℝ)*(δ:ℝ)*iteratedDeriv 2 (fun y => f (a,y)) b|+
        |(1/2:ℝ)*(δ:ℝ)*((∫ y, D (b+y) ∂μ)-D b)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ e+e+(1/2:ℝ)*(δ:ℝ)*((K:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 1) := by
      apply add_le_add (add_le_add hRint hY)
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)*(δ:ℝ))]
      exact mul_le_mul_of_nonneg_left hDDint (by positivity)
    _ = _ := by dsimp [e]; ring

end SLEExactGauge

end

end OAI
