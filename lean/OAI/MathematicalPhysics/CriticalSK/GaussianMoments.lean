import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

lemma gaussian_square_density (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_square_integral (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_square_density]
  rw [integral_const_mul, integral_gaussian]
  have ha : 0 < 1 / 2 - t := by linarith
  have hb : 0 < 1 - 2 * t := by linarith
  apply (mul_left_inj' (Real.sqrt_ne_zero'.mpr hb)).mp
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hb)]
  have he : Real.sqrt (Real.pi / (1 / 2 - t)) * Real.sqrt (1 - 2 * t) =
      Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / (1 / 2 - t) * (1 - 2 * t) =
      2 * Real.pi by field_simp]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1 / 2 - t)) *
        Real.sqrt (1 - 2 * t) = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by
          rw [mul_assoc, he]
    _ = 1 := inv_mul_cancel₀ (by positivity)

lemma gaussian_square_integrable (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  apply mgf_pos_iff.mp
  change 0 < ∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1
  rw [gaussian_square_integral t ht]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

def chiSquare (m : ℕ) (x : Fin m → ℝ) : ℝ := ∑ i, x i ^ 2

def standardGaussianProduct (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

section

open Set Filter MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

def gaussianScalarPi (v : ℝ≥0) : Measure (ι → ℝ) := Measure.pi fun _ => gaussianReal 0 v

instance (v : ℝ≥0) : IsProbabilityMeasure (gaussianScalarPi (ι := ι) v) := by unfold gaussianScalarPi; infer_instance

def gaussianLinear (a : ι → ℝ) (z : ι → ℝ) : ℝ := ∑ i, a i*z i

lemma gaussianLinear_continuous (a : ι → ℝ) : Continuous (gaussianLinear a) := by
  unfold gaussianLinear
  fun_prop

lemma gaussian_exp_integrable (v : ℝ≥0) (a : ι → ℝ) :
    Integrable (fun z => Real.exp (gaussianLinear a z)) (gaussianScalarPi v) := by
  simp only [gaussianLinear,Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a i))

lemma gaussian_exp_integral (v : ℝ≥0) (a : ι → ℝ) :
    (∫ z, Real.exp (gaussianLinear a z) ∂gaussianScalarPi v) = Real.exp ((v:ℝ)*(∑ i, a i^2)/2) := by
  simp only [gaussianLinear,Real.exp_sum,gaussianScalarPi]
  rw [integral_fintype_prod_eq_prod (μ := fun _ => gaussianReal 0 v) (fun i (z : ℝ) => Real.exp (a i*z))]
  have he (i : ι) : (∫ z : ℝ, Real.exp (a i*z) ∂gaussianReal 0 v) = Real.exp ((v:ℝ)*(a i)^2/2) := by
    have hh := mgf_gaussianReal (p := gaussianReal 0 v) (X := id) (μ := 0) (v := v) (by simp) (a i)
    simpa only [mgf,zero_mul,zero_add,id_eq] using hh
  simp_rw [he]
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_div]

lemma gaussianLinear_neg (a z : ι → ℝ) : gaussianLinear (-a) z = -gaussianLinear a z := by
  simp [gaussianLinear]

lemma gaussianLinear_add (a b z : ι → ℝ) : gaussianLinear (a+b) z = gaussianLinear a z+gaussianLinear b z := by
  simp [gaussianLinear,add_mul,Finset.sum_add_distrib]

lemma gaussianLinear_sub (a b z : ι → ℝ) : gaussianLinear (a-b) z = gaussianLinear a z-gaussianLinear b z := by
  simp [gaussianLinear,sub_mul,Finset.sum_sub_distrib]

lemma gaussian_cosh_integrable (v : ℝ≥0) (a : ι → ℝ) :
    Integrable (fun z => Real.cosh (gaussianLinear a z)) (gaussianScalarPi v) := by
  simp_rw [Real.cosh_eq,← gaussianLinear_neg]
  exact ((gaussian_exp_integrable v a).add (gaussian_exp_integrable v (-a))).div_const 2

lemma gaussian_cosh_integral (v : ℝ≥0) (a : ι → ℝ) :
    (∫ z, Real.cosh (gaussianLinear a z) ∂gaussianScalarPi v) = Real.exp ((v:ℝ)*(∑ i, a i^2)/2) := by
  simp_rw [Real.cosh_eq,← gaussianLinear_neg]
  rw [integral_div,integral_add (gaussian_exp_integrable v a) (gaussian_exp_integrable v (-a)),gaussian_exp_integral,gaussian_exp_integral]
  simp only [Pi.neg_apply,neg_sq]
  ring

lemma cosh_mul_cosh_identity (a b : ℝ) : Real.cosh a*Real.cosh b = (Real.cosh (a+b)+Real.cosh (a-b))/2 := by
  rw [Real.cosh_add,Real.cosh_sub]
  ring

lemma gaussian_cosh_product_integrable (v : ℝ≥0) (a b : ι → ℝ) :
    Integrable (fun z => Real.cosh (gaussianLinear a z)*Real.cosh (gaussianLinear b z)) (gaussianScalarPi v) := by
  simp_rw [cosh_mul_cosh_identity,← gaussianLinear_add,← gaussianLinear_sub]
  exact ((gaussian_cosh_integrable v (a+b)).add (gaussian_cosh_integrable v (a-b))).div_const 2

lemma gaussian_cosh_product_integral (v : ℝ≥0) (a b : ι → ℝ) :
    (∫ z, Real.cosh (gaussianLinear a z)*Real.cosh (gaussianLinear b z) ∂gaussianScalarPi v) =
      Real.exp ((v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2))/2)*Real.cosh ((v:ℝ)*∑ i, a i*b i) := by
  simp_rw [cosh_mul_cosh_identity,← gaussianLinear_add,← gaussianLinear_sub]
  rw [integral_div,integral_add (gaussian_cosh_integrable v (a+b)) (gaussian_cosh_integrable v (a-b)),gaussian_cosh_integral,gaussian_cosh_integral]
  have hp : (∑ i, (a+b) i^2) = (∑ i, a i^2)+(∑ i, b i^2)+2*∑ i, a i*b i := by
    simp only [Pi.add_apply,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hm : (∑ i, (a-b) i^2) = (∑ i, a i^2)+(∑ i, b i^2)-2*∑ i, a i*b i := by
    simp only [Pi.sub_apply,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hp,hm,Real.cosh_eq]
  rw [show (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2)+2*∑ i, a i*b i)/2 =
    (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2))/2+(v:ℝ)*∑ i, a i*b i by ring,
    show (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2)-2*∑ i, a i*b i)/2 =
    (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2))/2+(-((v:ℝ)*∑ i, a i*b i)) by ring,
    Real.exp_add,Real.exp_add]
  ring

lemma cosh_pow_exp_bound (z : ℝ) (m : ℕ) :
    Real.cosh z^m ≤ Real.exp ((m:ℝ)*z)+Real.exp (-((m:ℝ)*z)) := by
  have hc : Real.cosh z ≤ Real.exp |z| := by
    rw [Real.cosh_eq]
    have hp := Real.exp_le_exp.mpr (le_abs_self z)
    have hm := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  have hh := pow_le_pow_left₀ (Real.cosh_pos z).le hc m
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans (by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz]
      linarith [Real.exp_pos (-((m:ℝ)*z))]
    · rw [abs_of_neg (lt_of_not_ge hz),mul_neg]
      linarith [Real.exp_pos ((m:ℝ)*z)])

lemma gaussian_cosh_pow_bound (v : ℝ≥0) (a : ι → ℝ) (m : ℕ) :
    Integrable (fun z => Real.cosh (gaussianLinear a z)^m) (gaussianScalarPi v) ∧
    (∫ z, Real.cosh (gaussianLinear a z)^m ∂gaussianScalarPi v) ≤
      2*Real.exp ((m:ℝ)^2*(v:ℝ)*(∑ i, a i^2)/2) := by
  let b : ι → ℝ := fun i => (m:ℝ)*a i
  have he (z : ι → ℝ) : gaussianLinear b z = (m:ℝ)*gaussianLinear a z := by
    simp only [gaussianLinear,b,Finset.mul_sum,mul_assoc]
  have hib := (gaussian_exp_integrable v b).add (gaussian_exp_integrable v (-b))
  have hi : Integrable (fun z => Real.cosh (gaussianLinear a z)^m) (gaussianScalarPi v) := by
    apply hib.mono' (((Real.continuous_cosh.comp (gaussianLinear_continuous a)).pow m).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Pi.add_apply, Pi.pow_apply, Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le _),gaussianLinear_neg,he]
      exact cosh_pow_exp_bound _ _)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z, Real.exp (gaussianLinear b z)+Real.exp (gaussianLinear (-b) z) ∂gaussianScalarPi v :=
      integral_mono hi hib (fun z => by rw [gaussianLinear_neg,he]; exact cosh_pow_exp_bound _ _)
    _ = _ := by
      rw [integral_add (gaussian_exp_integrable v b) (gaussian_exp_integrable v (-b)),gaussian_exp_integral,gaussian_exp_integral]
      simp only [Pi.neg_apply,neg_sq,b,mul_pow,← Finset.mul_sum]
      ring_nf

lemma cosh_sub_one_quadratic {z : ℝ} (hz : |z| ≤ 1) : Real.cosh z-1 ≤ (Real.exp 1-1)*z^2 := by
  have hz2 : z^2 ≤ 1 := by nlinarith [sq_abs z,abs_nonneg z]
  have hc := (convexOn_exp.2 (show (0:ℝ) ∈ univ from trivial) (show (1:ℝ) ∈ univ from trivial)
    (show 0 ≤ 1-z^2 by nlinarith) (sq_nonneg z) (by ring))
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,Real.exp_zero] at hc
  have he := (Real.cosh_le_exp_half_sq z).trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z] : z^2/2 ≤ z^2))
  nlinarith

end

open Set Filter MeasureTheory ProbabilityTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def coshMixture (p : κ → ℝ) (a : κ → ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ x, p x*Real.cosh (gaussianLinear (a x) z)

lemma coshMixture_continuous (p : κ → ℝ) (a : κ → ι → ℝ) : Continuous (coshMixture p a) := by
  unfold coshMixture
  apply continuous_finsetSum
  intro x _
  exact continuous_const.mul (Real.continuous_cosh.comp (gaussianLinear_continuous _))

lemma coshMixture_nonneg {p : κ → ℝ} (hp : ∀ x, 0 ≤ p x) (a : κ → ι → ℝ) (z : ι → ℝ) : 0 ≤ coshMixture p a z := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (Real.cosh_pos _).le)

lemma coshMixture_integrable (v : ℝ≥0) (p : κ → ℝ) (a : κ → ι → ℝ) :
    Integrable (coshMixture p a) (gaussianScalarPi v) :=
  integrable_finsetSum _ (fun x _ => (gaussian_cosh_integrable v (a x)).const_mul (p x))

lemma coshMixture_integral (v : ℝ≥0) {p : κ → ℝ} (hpsum : ∑ x, p x = 1)
    (a : κ → ι → ℝ) {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s) :
    (∫ z, coshMixture p a z ∂gaussianScalarPi v) = Real.exp ((v:ℝ)*s/2) := by
  unfold coshMixture
  rw [integral_finsetSum _ (fun x _ => (gaussian_cosh_integrable v (a x)).const_mul (p x))]
  simp_rw [integral_const_mul,gaussian_cosh_integral,hs]
  rw [← Finset.sum_mul,hpsum,one_mul]

lemma coshMixture_pow_integrable_bound (v : ℝ≥0) {p : κ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hpsum : ∑ x, p x = 1) (a : κ → ι → ℝ) {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s) (m : ℕ) :
    Integrable (fun z => coshMixture p a z^m) (gaussianScalarPi v) ∧
    (∫ z, coshMixture p a z^m ∂gaussianScalarPi v) ≤ 2*Real.exp ((m:ℝ)^2*(v:ℝ)*s/2) := by
  have hib : Integrable (fun z => ∑ x, p x*Real.cosh (gaussianLinear (a x) z)^m) (gaussianScalarPi v) :=
    integrable_finsetSum _ (fun x _ => ((gaussian_cosh_pow_bound v (a x) m).1.const_mul _))
  have hbound (z : ι → ℝ) : coshMixture p a z^m ≤ ∑ x, p x*Real.cosh (gaussianLinear (a x) z)^m :=
    Real.pow_arith_mean_le_arith_mean_pow _ _ _ (fun x _ => hp x) hpsum (fun _ _ => (Real.cosh_pos _).le) m
  have hi : Integrable (fun z => coshMixture p a z^m) (gaussianScalarPi v) := by
    apply hib.mono' ((coshMixture_continuous p a).pow m).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by simp only [Pi.pow_apply]; rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (coshMixture_nonneg hp a z) _)]; exact hbound z)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z, ∑ x, p x*Real.cosh (gaussianLinear (a x) z)^m ∂gaussianScalarPi v := integral_mono hi hib hbound
    _ = ∑ x, p x*(∫ z, Real.cosh (gaussianLinear (a x) z)^m ∂gaussianScalarPi v) := by
      rw [integral_finsetSum _ (fun x _ => ((gaussian_cosh_pow_bound v (a x) m).1.const_mul _))]
      simp only [integral_const_mul]
    _ ≤ ∑ x, p x*(2*Real.exp ((m:ℝ)^2*(v:ℝ)*s/2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hp x)
      simpa only [hs] using (gaussian_cosh_pow_bound v (a x) m).2
    _ = _ := by rw [← Finset.sum_mul,hpsum,one_mul]

lemma coshMixture_square (p : κ → ℝ) (a : κ → ι → ℝ) (z : ι → ℝ) :
    coshMixture p a z^2 = ∑ x, ∑ y, p x*p y*(Real.cosh (gaussianLinear (a x) z)*Real.cosh (gaussianLinear (a y) z)) := by
  simp only [coshMixture,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma coshMixture_square_integral (v : ℝ≥0) (p : κ → ℝ) (a : κ → ι → ℝ)
    {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s) :
    (∫ z, coshMixture p a z^2 ∂gaussianScalarPi v) =
      Real.exp ((v:ℝ)*s)*(∑ x, ∑ y, p x*p y*Real.cosh ((v:ℝ)*∑ i, a x i*a y i)) := by
  simp_rw [coshMixture_square]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => (gaussian_cosh_product_integrable v (a x) (a y)).const_mul (p x*p y)))]
  simp_rw [integral_finsetSum _ (fun y _ => (gaussian_cosh_product_integrable v _ (a y)).const_mul _),integral_const_mul,gaussian_cosh_product_integral,hs]
  rw [show (v:ℝ)*(s+s)/2 = (v:ℝ)*s by ring]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma coshMixture_centered_integrable_bound (v : ℝ≥0) {p : κ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hpsum : ∑ x, p x = 1) (a : κ → ι → ℝ) {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s)
    (hc : ∀ x y, |(v:ℝ)*∑ i, a x i*a y i| ≤ 1) :
    Integrable (fun z => (coshMixture p a z-Real.exp ((v:ℝ)*s/2))^2) (gaussianScalarPi v) ∧
    (∫ z, (coshMixture p a z-Real.exp ((v:ℝ)*s/2))^2 ∂gaussianScalarPi v) ≤
      Real.exp ((v:ℝ)*s)*(Real.exp 1-1)*(∑ x, ∑ y, p x*p y*((v:ℝ)*∑ i, a x i*a y i)^2) := by
  let m := Real.exp ((v:ℝ)*s/2)
  have hi := (coshMixture_pow_integrable_bound v hp hpsum a hs 2).1
  have hmi := coshMixture_integrable v p a
  have he (z : ι → ℝ) : (coshMixture p a z-m)^2 = coshMixture p a z^2-2*m*coshMixture p a z+m^2 := by ring
  have hiz : Integrable (fun z => (coshMixture p a z-m)^2) (gaussianScalarPi v) := by
    simp_rw [he]
    exact (hi.sub (hmi.const_mul _)).add (integrable_const _)
  refine ⟨hiz,?_⟩
  have hm2 : m^2 = Real.exp ((v:ℝ)*s) := by dsimp only [m]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsum : (∑ x, ∑ y, p x*p y) = 1 := by simp only [← Finset.mul_sum,hpsum,mul_one]
  have hid : (∫ z, (coshMixture p a z-m)^2 ∂gaussianScalarPi v) =
      Real.exp ((v:ℝ)*s)*(∑ x, ∑ y, p x*p y*(Real.cosh ((v:ℝ)*∑ i, a x i*a y i)-1)) := by
    simp_rw [he]
    rw [integral_add (f := fun z => coshMixture p a z^2-2*m*coshMixture p a z) (g := fun _ => m^2) (hi.sub (hmi.const_mul _)) (integrable_const _),integral_sub (f := fun z => coshMixture p a z^2) (g := fun z => 2*m*coshMixture p a z) hi (hmi.const_mul _),integral_const_mul,
      coshMixture_integral v hpsum a hs,coshMixture_square_integral v p a hs,integral_const,probReal_univ,one_smul]
    change Real.exp ((v:ℝ)*s)*_-2*m*m+m^2 = _
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hsum]
    nlinarith
  rw [hid]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  nlinarith [mul_le_mul_of_nonneg_left (cosh_sub_one_quadratic (hc x y)) (mul_nonneg (hp x) (hp y))]

end CriticalSK

end

end OAI
