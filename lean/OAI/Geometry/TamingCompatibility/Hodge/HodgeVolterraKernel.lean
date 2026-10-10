import Mathlib

namespace OAI

section

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraBounds
open MeasureTheory Set Metric
open scoped Topology
variable {X B : Type*} [PseudoMetricSpace X]

def weight (N : ℕ) (t : ℝ) (x y : X) : ℝ := (1 + dist x y / Real.sqrt t)^N

lemma weight_one_le (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    1 ≤ weight N t x y := by
  apply one_le_pow₀
  have := div_nonneg (dist_nonneg (x := x) (y := y)) (Real.sqrt_pos.2 ht).le
  linarith

lemma weight_pos (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < weight N t x y := lt_of_lt_of_le zero_lt_one (weight_one_le N ht x y)

lemma weight_symm (N : ℕ) (t : ℝ) (x y : X) : weight N t x y = weight N t y x := by
  simp only [weight, dist_comm]

lemma weight_submultiplicative (N : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x z y : X) : weight N (t+s) x y ≤ weight N t x z * weight N s z y := by
  rw [weight, weight, weight, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hT : 0 < Real.sqrt (t+s) := Real.sqrt_pos.2 (add_pos ht hs)
  have h1 := div_le_div_of_nonneg_left (dist_nonneg (x := x) (y := z))
    (Real.sqrt_pos.2 ht) (Real.sqrt_le_sqrt (le_add_of_nonneg_right hs.le))
  have h2 := div_le_div_of_nonneg_left (dist_nonneg (x := z) (y := y))
    (Real.sqrt_pos.2 hs) (Real.sqrt_le_sqrt (le_add_of_nonneg_left ht.le))
  have hd := div_le_div_of_nonneg_right (dist_triangle x z y) hT.le
  rw [add_div] at hd
  have hmul : 0 ≤ (dist x z / Real.sqrt t) * (dist z y / Real.sqrt s) := by positivity
  nlinarith

lemma weight_continuous (N : ℕ) (t : ℝ) (x : X) : Continuous (weight N t x) := by
  unfold weight
  fun_prop

variable [MeasurableSpace X] [NormedRing B] [NormedAlgebra ℝ B]

lemma spatial_convolution_bound (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hA : 0 ≤ A)
    (K L : X → X → B) (x y : X)
    (hK : ∀ z, weight N t x z * ‖K x z‖ ≤ A)
    (hL : Integrable (fun z => weight N s z y * ‖L z y‖) μ)
    (hLI : (∫ z, weight N s z y * ‖L z y‖ ∂μ) ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K x z * L z y) μ) :
    Integrable (fun z => K x z * L z y) μ ∧
      weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ≤ A*C := by
  have hw := weight_pos N (add_pos ht hs) x y
  have hpoint (z : X) : weight N (t+s) x y * ‖K x z * L z y‖ ≤
      A * (weight N s z y * ‖L z y‖) := by
    calc
      _ ≤ (weight N t x z * weight N s z y) * (‖K x z‖*‖L z y‖) :=
        mul_le_mul (weight_submultiplicative N ht hs x z y) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (weight_pos N ht x z).le (weight_pos N hs z y).le)
      _ = (weight N t x z * ‖K x z‖) * (weight N s z y * ‖L z y‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hK z)
        (mul_nonneg (weight_pos N hs z y).le (norm_nonneg _))
  have hint : Integrable (fun z => K x z * L z y) μ := by
    apply (hL.const_mul (A / weight N (t+s) x y)).mono' hprod
    filter_upwards [] with z
    have h := (le_div_iff₀ hw).mpr (show ‖K x z * L z y‖ * weight N (t+s) x y ≤
      A * (weight N s z y * ‖L z y‖) by simpa only [mul_comm] using hpoint z)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨hint, ?_⟩
  calc
    _ ≤ weight N (t+s) x y * (∫ z, ‖K x z * L z y‖ ∂μ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ z, weight N (t+s) x y * ‖K x z * L z y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ z, A * (weight N s z y * ‖L z y‖) ∂μ :=
      integral_mono (hint.norm.const_mul _) (hL.const_mul _) hpoint
    _ = A * (∫ z, weight N s z y * ‖L z y‖ ∂μ) := integral_const_mul _ _
    _ ≤ A*C := mul_le_mul_of_nonneg_left hLI hA

lemma spatial_convolution_bound_right (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C)
    (K L : X → X → B) (x y : X)
    (hK : Integrable (fun z => weight N t x z * ‖K x z‖) μ)
    (hKI : (∫ z, weight N t x z * ‖K x z‖ ∂μ) ≤ A)
    (hL : ∀ z, weight N s z y * ‖L z y‖ ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K x z * L z y) μ) :
    Integrable (fun z => K x z * L z y) μ ∧
      weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ≤ A*C := by
  have hw := weight_pos N (add_pos ht hs) x y
  have hpoint (z : X) : weight N (t+s) x y * ‖K x z * L z y‖ ≤
      C * (weight N t x z * ‖K x z‖) := by
    calc
      _ ≤ (weight N t x z * weight N s z y) * (‖K x z‖*‖L z y‖) :=
        mul_le_mul (weight_submultiplicative N ht hs x z y) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (weight_pos N ht x z).le (weight_pos N hs z y).le)
      _ = (weight N s z y * ‖L z y‖) * (weight N t x z * ‖K x z‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hL z)
        (mul_nonneg (weight_pos N ht x z).le (norm_nonneg _))
  have hint : Integrable (fun z => K x z * L z y) μ := by
    apply (hK.const_mul (C / weight N (t+s) x y)).mono' hprod
    filter_upwards [] with z
    have h := (le_div_iff₀ hw).mpr (show ‖K x z * L z y‖ * weight N (t+s) x y ≤
      C * (weight N t x z * ‖K x z‖) by simpa only [mul_comm] using hpoint z)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨hint, ?_⟩
  calc
    _ ≤ weight N (t+s) x y * (∫ z, ‖K x z * L z y‖ ∂μ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ z, weight N (t+s) x y * ‖K x z * L z y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ z, C * (weight N t x z * ‖K x z‖) ∂μ :=
      integral_mono (hint.norm.const_mul _) (hK.const_mul _) hpoint
    _ = C * (∫ z, weight N t x z * ‖K x z‖ ∂μ) := integral_const_mul _ _
    _ ≤ C*A := mul_le_mul_of_nonneg_left hKI hC
    _ = A*C := mul_comm _ _

lemma time_integrand_bound (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hst : s < t) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (K L : ℝ → X → X → B) (x y : X)
    (hKsup : ∀ z, weight N (t-s) x z * ‖K (t-s) x z‖ ≤ A/(t-s)^2)
    (hLsup : ∀ z, weight N s z y * ‖L s z y‖ ≤ C/s^2)
    (hK : Integrable (fun z => weight N (t-s) x z * ‖K (t-s) x z‖) μ)
    (hL : Integrable (fun z => weight N s z y * ‖L s z y‖) μ)
    (hKI : (∫ z, weight N (t-s) x z * ‖K (t-s) x z‖ ∂μ) ≤ A)
    (hLI : (∫ z, weight N s z y * ‖L s z y‖ ∂μ) ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K (t-s) x z * L s z y) μ) :
    Integrable (fun z => K (t-s) x z * L s z y) μ ∧
      weight N t x y * ‖∫ z, K (t-s) x z * L s z y ∂μ‖ ≤ 4*A*C/t^2 := by
  have hts : 0 < t-s := sub_pos.mpr hst
  have hleft := spatial_convolution_bound μ N hts hs (by positivity : 0 ≤ A/(t-s)^2)
    (K (t-s)) (L s) x y hKsup hL hLI hprod
  refine ⟨hleft.1, ?_⟩
  by_cases hhalf : s ≤ t/2
  · have hden : t^2/4 ≤ (t-s)^2 := by nlinarith [sq_nonneg (t/2-s)]
    have hdiv : A/(t-s)^2 ≤ 4*A/t^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hts) (sq_pos_of_pos ht)).2
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hden)]
    calc
      _ ≤ (A/(t-s)^2)*C := by simpa using hleft.2
      _ ≤ (4*A/t^2)*C := mul_le_mul_of_nonneg_right hdiv hC
      _ = _ := by ring
  · have hden : t^2/4 ≤ s^2 := by nlinarith [sq_nonneg (s-t/2)]
    have hdiv : C/s^2 ≤ 4*C/t^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos ht)).2
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hden)]
    have hright := spatial_convolution_bound_right μ N hts hs
      (by positivity : 0 ≤ C/s^2) (K (t-s)) (L s) x y hK hKI hLsup hprod
    calc
      _ ≤ A*(C/s^2) := by simpa using hright.2
      _ ≤ A*(4*C/t^2) := mul_le_mul_of_nonneg_left hdiv hA
      _ = _ := by ring

lemma time_convolution_bound (μ : Measure X) (N : ℕ) {t A C : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (K L : ℝ → X → X → B) (x y : X)
    (hKsup : ∀ s ∈ Ioo 0 t, ∀ z, weight N (t-s) x z * ‖K (t-s) x z‖ ≤ A/(t-s)^2)
    (hLsup : ∀ s ∈ Ioo 0 t, ∀ z, weight N s z y * ‖L s z y‖ ≤ C/s^2)
    (hK : ∀ s ∈ Ioo 0 t, Integrable (fun z => weight N (t-s) x z * ‖K (t-s) x z‖) μ)
    (hL : ∀ s ∈ Ioo 0 t, Integrable (fun z => weight N s z y * ‖L s z y‖) μ)
    (hKI : ∀ s ∈ Ioo 0 t, (∫ z, weight N (t-s) x z * ‖K (t-s) x z‖ ∂μ) ≤ A)
    (hLI : ∀ s ∈ Ioo 0 t, (∫ z, weight N s z y * ‖L s z y‖ ∂μ) ≤ C)
    (hprod : ∀ s ∈ Ioo 0 t, AEStronglyMeasurable (fun z => K (t-s) x z * L s z y) μ)
    (htime : AEStronglyMeasurable (fun s => ∫ z, K (t-s) x z * L s z y ∂μ)
      (volume.restrict (Ioo 0 t))) :
    IntegrableOn (fun s => ∫ z, K (t-s) x z * L s z y ∂μ) (Ioo 0 t) ∧
      weight N t x y * ‖∫ s in Ioo 0 t, ∫ z, K (t-s) x z * L s z y ∂μ‖ ≤ 4*A*C/t := by
  have hw := weight_pos N ht x y
  have hpoint (s : ℝ) (hs : s ∈ Ioo 0 t) := (time_integrand_bound μ N ht hs.1 hs.2
    hA hC K L x y (hKsup s hs) (hLsup s hs) (hK s hs) (hL s hs)
    (hKI s hs) (hLI s hs) (hprod s hs)).2
  have hi : IntegrableOn (fun s => ∫ z, K (t-s) x z * L s z y ∂μ) (Ioo 0 t) := by
    apply (integrableOn_const (C := 4*A*C/t^2/weight N t x y)
      (hs := measure_Ioo_lt_top.ne)).mono' htime
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (le_div_iff₀ hw).2
    simpa only [mul_comm] using hpoint s hs
  refine ⟨hi, ?_⟩
  calc
    _ ≤ weight N t x y * (∫ s in Ioo 0 t, ‖∫ z, K (t-s) x z * L s z y ∂μ‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ s in Ioo 0 t, weight N t x y * ‖∫ z, K (t-s) x z * L s z y ∂μ‖ :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ _s in Ioo 0 t, 4*A*C/t^2 := by
      apply integral_mono_ae (hi.norm.const_mul _)
        (integrableOn_const (hs := measure_Ioo_lt_top.ne))
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hpoint s hs
    _ = 4*A*C/t := by
      simp only [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le ht.le,
        smul_eq_mul, sub_zero]
      field_simp

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.SchurIntegration
open MeasureTheory
variable {X Y B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
variable (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma product_integrable {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C) :
    Integrable (fun p : X × Y => f p.1 * g p.1 p.2) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : X × Y => f p.1 * g p.1 p.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => (hgi x).const_mul (f x)), ?_⟩
  have hi (x : X) : (∫ y, ‖f x*g x y‖ ∂ν) = f x * ∫ y, g x y ∂ν := by
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hf0 x) (hg0 x _))]
    exact integral_const_mul _ _
  simp_rw [hi]
  apply (hf.mul_const C).mono'
    (by simpa only [hi] using hm.norm.integral_prod_right')
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (mul_nonneg (hf0 x) (integral_nonneg (hg0 x)))]
    exact mul_le_mul_of_nonneg_left (hC x) (hf0 x)

omit [SFinite μ] in
lemma product_integral_le {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C) :
    (∫ x, ∫ y, f x*g x y ∂ν ∂μ) ≤ C * ∫ x, f x ∂μ := by
  have hi := product_integrable μ ν hf hf0 hg hg0 hgi hC
  rw [mul_comm C, ← integral_mul_const]
  apply integral_mono hi.integral_prod_left (hf.mul_const C)
  intro x
  change (∫ y, f x*g x y ∂ν) ≤ f x*C
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (hf0 x)

lemma norm_integral_row {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C)
    (H : X → Y → B) (hH : StronglyMeasurable (Function.uncurry H))
    (hdom : ∀ x y, ‖H x y‖ ≤ f x*g x y) :
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
      (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ C * ∫ x, f x ∂μ := by
  have hi := product_integrable μ ν hf hf0 hg hg0 hgi hC
  have hHi : Integrable (Function.uncurry H) (μ.prod ν) :=
    hi.mono' hH.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hdom p.1 p.2)
  refine ⟨hHi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, f x*g x y ∂μ ∂ν := by
      apply integral_mono_ae hHi.integral_prod_right.norm hi.integral_prod_right
      filter_upwards [hi.prod_left_ae] with y hy
      exact norm_integral_le_of_norm_le hy (Filter.Eventually.of_forall fun x => hdom x y)
    _ = ∫ x, ∫ y, f x*g x y ∂ν ∂μ := (integral_integral_swap hi).symm
    _ ≤ _ := product_integral_le μ ν hf hf0 hg hg0 hgi hC

lemma integral_row_bound {F : X → ℝ} (hF : Integrable F μ)
    (H : X → Y → B) (hH : StronglyMeasurable (Function.uncurry H))
    (hHi : ∀ x, Integrable (H x) ν)
    (hrow : ∀ x, (∫ y, ‖H x y‖ ∂ν) ≤ F x) :
    Integrable (Function.uncurry H) (μ.prod ν) ∧
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
    (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ ∫ x, F x ∂μ := by
  have hi : Integrable (Function.uncurry H) (μ.prod ν) := by
    apply (integrable_prod_iff hH.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hHi, ?_⟩
    apply hF.mono' hH.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hrow x
  refine ⟨hi, hi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, ‖H x y‖ ∂μ ∂ν := by
      exact integral_mono hi.integral_prod_right.norm hi.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = ∫ x, ∫ y, ‖H x y‖ ∂ν ∂μ := (integral_integral_swap hi.norm).symm
    _ ≤ _ := integral_mono hi.norm.integral_prod_left hF hrow

lemma integral_row_bound_ae {F : X → ℝ} (hF : Integrable F μ)
    (H : X → Y → B) (hH : AEStronglyMeasurable (Function.uncurry H) (μ.prod ν))
    (hHi : ∀ᵐ x ∂μ, Integrable (H x) ν)
    (hrow : ∀ᵐ x ∂μ, (∫ y, ‖H x y‖ ∂ν) ≤ F x) :
    Integrable (Function.uncurry H) (μ.prod ν) ∧
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
    (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ ∫ x, F x ∂μ := by
  have hi : Integrable (Function.uncurry H) (μ.prod ν) := by
    apply (integrable_prod_iff hH).mpr
    refine ⟨hHi, ?_⟩
    apply hF.mono' hH.norm.integral_prod_right'
    filter_upwards [hrow] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hx
  refine ⟨hi, hi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, ‖H x y‖ ∂μ ∂ν := by
      exact integral_mono hi.integral_prod_right.norm hi.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = ∫ x, ∫ y, ‖H x y‖ ∂ν ∂μ := (integral_integral_swap hi.norm).symm
    _ ≤ _ := integral_mono_ae hi.norm.integral_prod_left hF hrow

end TamingCompatibility.GeometricHilbert.SchurIntegration

end
end

noncomputable section
namespace TamingCompatibility.GeometricHilbert.SchurKernel
open MeasureTheory VolterraBounds
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

lemma convolution_row (N : ℕ) {t s A C : ℝ} (ht : 0 < t) (hs : 0 < s)
    (K L : X → X → B) (x : X)
    (hK : Integrable (fun z => weight N t x z * ‖K x z‖) μ)
    (hKI : (∫ z, weight N t x z * ‖K x z‖ ∂μ) ≤ A)
    (hL : StronglyMeasurable (fun zy : X × X => weight N s zy.1 zy.2 * ‖L zy.1 zy.2‖))
    (hLi : ∀ z, Integrable (fun y => weight N s z y * ‖L z y‖) μ)
    (hLI : ∀ z, (∫ y, weight N s z y * ‖L z y‖ ∂μ) ≤ C)
    (hC : 0 ≤ C)
    (hH : StronglyMeasurable (fun zy : X × X =>
      weight N (t+s) x zy.2 • (K x zy.1 * L zy.1 zy.2))) :
    Integrable (fun y => weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖) μ ∧
    (∫ y, weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ∂μ) ≤ A*C := by
  have hb : ∀ z y, ‖weight N (t+s) x y • (K x z * L z y)‖ ≤
      (weight N t x z*‖K x z‖)*(weight N s z y*‖L z y‖) := by
    intro z y
    rw [norm_smul, Real.norm_of_nonneg (weight_pos N (add_pos ht hs) x y).le]
    calc
      _ ≤ weight N (t+s) x y*(‖K x z‖*‖L z y‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (weight_pos N (add_pos ht hs) x y).le
      _ ≤ (weight N t x z*weight N s z y)*(‖K x z‖*‖L z y‖) :=
        mul_le_mul_of_nonneg_right (weight_submultiplicative N ht hs x z y) (by positivity)
      _ = _ := by ring
  have hh := SchurIntegration.norm_integral_row μ μ
    (g := fun z y => weight N s z y*‖L z y‖) hK
    (fun z => mul_nonneg (weight_pos N ht x z).le (norm_nonneg _)) hL
    (fun z y => mul_nonneg (weight_pos N hs z y).le (norm_nonneg _))
    hLi hLI (fun z y => weight N (t+s) x y • (K x z * L z y)) hH hb
  have he (y : X) : ‖∫ z, weight N (t+s) x y • (K x z * L z y) ∂μ‖ =
      weight N (t+s) x y*‖∫ z, K x z * L z y ∂μ‖ := by
    rw [integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N (add_pos ht hs) x y).le]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hh.1.norm
  · have h := hh.2
    simp_rw [he] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hKI hC])

end TamingCompatibility.GeometricHilbert.SchurKernel

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open MeasureTheory Set VolterraBounds
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

abbrev Kernel := ℝ → X → X → B

def MeasurableKernel (K : Kernel (X := X) (B := B)) : Prop :=
  StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2)

def spatial (K L : Kernel (X := X) (B := B)) (t s : ℝ) (x y : X) : B :=
  ∫ z, K (t-s) x z * L s z y ∂μ

def convolution (K L : Kernel (X := X) (B := B)) (t : ℝ) (x y : X) : B :=
  ∫ s in Ioo 0 t, spatial μ K L t s x y

lemma spatial_measurable (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) :
    StronglyMeasurable (fun p : (ℝ × X × X) × ℝ =>
      spatial μ K L p.1.1 p.2 p.1.2.1 p.1.2.2) := by
  have hKm : Measurable (fun q : ((ℝ × X × X) × ℝ) × X =>
      (q.1.1.1-q.1.2, q.1.1.2.1, q.2)) := by fun_prop
  have hLm : Measurable (fun q : ((ℝ × X × X) × ℝ) × X =>
      (q.1.2, q.2, q.1.1.2.2)) := by fun_prop
  exact ((hK.comp_measurable hKm).mul (hL.comp_measurable hLm)).integral_prod_right

lemma convolution_measurable (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) :
    MeasurableKernel (convolution μ K L) := by
  have hm := spatial_measurable μ K L hK hL
  have hset : MeasurableSet {p : (ℝ × X × X) × ℝ | p.2 ∈ Ioo 0 p.1.1} := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.fst))
  have hmi : StronglyMeasurable (Function.uncurry (fun (p : ℝ × X × X) (s : ℝ) =>
      (Ioo 0 p.1).indicator (fun s => spatial μ K L p.1 s p.2.1 p.2.2) s)) :=
    hm.indicator hset
  have hi := hmi.integral_prod_right (ν := volume)
  simpa only [MeasurableKernel, convolution, integral_indicator measurableSet_Ioo] using hi

omit [NormedAlgebra ℝ B] in
lemma kernel_section (K : Kernel (X := X) (B := B)) (hK : MeasurableKernel K)
    (t : ℝ) : StronglyMeasurable (fun p : X × X => K t p.1 p.2) :=
  hK.comp_measurable (measurable_const.prodMk measurable_id)

lemma spatial_section (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) (t x y) :
    StronglyMeasurable (fun s => spatial μ K L t s x y) :=
  (spatial_measurable μ K L hK hL).comp_measurable
    (show Measurable (fun s : ℝ => ((t,x,y),s)) from
      measurable_const.prodMk measurable_id)

omit [NormedAlgebra ℝ B] in
lemma product_section (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) (t s x y) :
    StronglyMeasurable (fun z => K (t-s) x z * L s z y) := by
  exact (hK.comp_measurable (measurable_const.prodMk
    (measurable_const.prodMk measurable_id))).mul
    (hL.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const)))

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

structure HeatBound (N : ℕ) (T A : ℝ) (K : Kernel (X := X) (B := B)) : Prop where
  measurable : MeasurableKernel K
  nonneg : 0 ≤ A
  sup : ∀ t ∈ Ioc 0 T, ∀ x y, weight N t x y*‖K t x y‖ ≤ A/t^2
  row_int : ∀ t ∈ Ioc 0 T, ∀ x, Integrable (fun y => weight N t x y*‖K t x y‖) μ
  row : ∀ t ∈ Ioc 0 T, ∀ x, (∫ y, weight N t x y*‖K t x y‖ ∂μ) ≤ A
  col_int : ∀ t ∈ Ioc 0 T, ∀ y, Integrable (fun x => weight N t x y*‖K t x y‖) μ
  col : ∀ t ∈ Ioc 0 T, ∀ y, (∫ x, weight N t x y*‖K t x y‖ ∂μ) ≤ A

omit [BorelSpace X] [SecondCountableTopology X] in
lemma convolution_sup (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    IntegrableOn (fun s => spatial μ K L t s x y) (Ioo 0 t) ∧
    weight N t x y*‖convolution μ K L t x y‖ ≤ 4*A*C/t := by
  have ha (s : ℝ) (hs : s ∈ Ioo 0 t) : t-s ∈ Ioc 0 T :=
    ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  exact time_convolution_bound μ N ht.1 hK.nonneg hL.nonneg K L x y
    (fun s hs z => hK.sup _ (ha s hs) x z)
    (fun s hs z => hL.sup _ (hb s hs) z y)
    (fun s hs => hK.row_int _ (ha s hs) x)
    (fun s hs => hL.col_int _ (hb s hs) y)
    (fun s hs => hK.row _ (ha s hs) x)
    (fun s hs => hL.col _ (hb s hs) y)
    (fun s _ => (product_section K L hK.measurable hL.measurable t s x y).aestronglyMeasurable)
    (spatial_section μ K L hK.measurable hL.measurable t x y).aestronglyMeasurable

omit [NormedAlgebra ℝ B] in
lemma weighted_section (N : ℕ) (K : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (t : ℝ) :
    StronglyMeasurable (fun p : X × X => weight N t p.1 p.2*‖K t p.1 p.2‖) := by
  have hw : Continuous (fun p : X × X => weight N t p.1 p.2) := by
    unfold weight
    fun_prop
  exact hw.stronglyMeasurable.mul (kernel_section K hK t).norm

lemma spatial_row (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (x : X) :
    Integrable (fun y => weight N t x y*‖spatial μ K L t s x y‖) μ ∧
    (∫ y, weight N t x y*‖spatial μ K L t s x y‖ ∂μ) ≤ A*C := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  have hweight : StronglyMeasurable (fun zy : X × X => weight N ((t-s)+s) x zy.2) :=
    ((weight_continuous N ((t-s)+s) x).comp continuous_snd).stronglyMeasurable
  have hKm : StronglyMeasurable (fun zy : X × X => K (t-s) x zy.1) :=
    hK.measurable.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  have hr := SchurKernel.convolution_row μ N ha.1 hb.1 (K (t-s)) (L s) x
    (hK.row_int _ ha x) (hK.row _ ha x) (weighted_section N L hL.measurable s)
    (hL.row_int _ hb) (hL.row _ hb) hL.nonneg
    (hweight.smul (hKm.mul (kernel_section L hL.measurable s)))
  simpa [spatial] using hr

lemma convolution_row (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : X) :
    Integrable (fun y => weight N t x y*‖convolution μ K L t x y‖) μ ∧
    (∫ y, weight N t x y*‖convolution μ K L t x y‖ ∂μ) ≤ t*A*C := by
  let H : ℝ → X → B := fun s y => weight N t x y • spatial μ K L t s x y
  have he (s : ℝ) (y : X) : ‖H s y‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]
  have hm : StronglyMeasurable (Function.uncurry H) := by
    have hweight : StronglyMeasurable (fun p : ℝ × X => weight N t x p.2) :=
      ((weight_continuous N t x).comp continuous_snd).stronglyMeasurable
    have hsp := (spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,x,p.2),p.1)) from by fun_prop)
    exact hweight.smul hsp
  have hi : ∀ᵐ s ∂volume.restrict (Ioo 0 t), Integrable (H s) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (integrable_norm_iff (hm.comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp
    change Integrable (fun y => ‖H s y‖) μ
    simpa only [he] using (spatial_row μ N K L hK hL ht hs x).1
  have hr : ∀ᵐ s ∂volume.restrict (Ioo 0 t), (∫ y, ‖H s y‖ ∂μ) ≤ A*C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [he] using (spatial_row μ N K L hK hL ht hs x).2
  have hh := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrableOn_const (C := A*C) (hs := measure_Ioo_lt_top.ne)) H hm.aestronglyMeasurable hi hr
  have hei (y : X) : ‖∫ s in Ioo 0 t, H s y‖ = weight N t x y*‖convolution μ K L t x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le,
      convolution]
  refine ⟨?_, ?_⟩
  · simpa only [hei] using hh.2.1.norm
  · have hb := hh.2.2
    simp only [hei, integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul] at hb
    simpa only [mul_assoc] using hb

lemma spatial_col (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (y : X) :
    Integrable (fun x => weight N t x y*‖spatial μ K L t s x y‖) μ ∧
    (∫ x, weight N t x y*‖spatial μ K L t s x y‖ ∂μ) ≤ A*C := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  let f : X → ℝ := fun z => weight N s z y*‖L s z y‖
  let g : X → X → ℝ := fun z x => weight N (t-s) x z*‖K (t-s) x z‖
  let H : X → X → B := fun z x => weight N t x y • (K (t-s) x z * L s z y)
  have hdom (z x : X) : ‖H z x‖ ≤ f z*g z x := by
    rw [show ‖H z x‖ = weight N t x y*‖K (t-s) x z * L s z y‖ by
      simp [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]]
    have hw : weight N t x y ≤ weight N (t-s) x z*weight N s z y := by
      simpa using weight_submultiplicative N ha.1 hb.1 x z y
    calc
      _ ≤ (weight N (t-s) x z*weight N s z y)*(‖K (t-s) x z‖*‖L s z y‖) :=
        mul_le_mul hw (norm_mul_le _ _) (norm_nonneg _)
          (mul_nonneg (weight_pos N ha.1 x z).le (weight_pos N hb.1 z y).le)
      _ = _ := by dsimp [f,g]; ring
  have hg : StronglyMeasurable (Function.uncurry g) :=
    (weighted_section N K hK.measurable (t-s)).comp_measurable measurable_swap
  have hH : StronglyMeasurable (Function.uncurry H) := by
    have hw : Continuous (fun p : X × X => weight N t p.2 y) := by unfold weight; fun_prop
    have hk := (kernel_section K hK.measurable (t-s)).comp_measurable measurable_swap
    have hl : StronglyMeasurable (fun p : X × X => L s p.1 y) :=
      hL.measurable.comp_measurable (measurable_const.prodMk (measurable_fst.prodMk measurable_const))
    exact hw.stronglyMeasurable.smul (hk.mul hl)
  have hh := SchurIntegration.norm_integral_row μ μ (g := g) (hL.col_int _ hb y)
    (fun z => mul_nonneg (weight_pos N hb.1 z y).le (norm_nonneg _)) hg
    (fun z x => mul_nonneg (weight_pos N ha.1 x z).le (norm_nonneg _))
    (hK.col_int _ ha) (hK.col _ ha) H hH hdom
  have he (x : X) : ‖∫ z, H z x ∂μ‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le, spatial]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hh.1.norm
  · have h := hh.2
    simp only [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hL.col _ hb y) hK.nonneg)

lemma convolution_col (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (y : X) :
    Integrable (fun x => weight N t x y*‖convolution μ K L t x y‖) μ ∧
    (∫ x, weight N t x y*‖convolution μ K L t x y‖ ∂μ) ≤ t*A*C := by
  let H : ℝ → X → B := fun s x => weight N t x y • spatial μ K L t s x y
  have he (s : ℝ) (x : X) : ‖H s x‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]
  have hm : StronglyMeasurable (Function.uncurry H) := by
    have hw : Continuous (fun p : ℝ × X => weight N t p.2 y) := by unfold weight; fun_prop
    have hsp := (spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,p.2,y),p.1)) from by fun_prop)
    exact hw.stronglyMeasurable.smul hsp
  have hi : ∀ᵐ s ∂volume.restrict (Ioo 0 t), Integrable (H s) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (integrable_norm_iff (hm.comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp
    change Integrable (fun x => ‖H s x‖) μ
    simpa only [he] using (spatial_col μ N K L hK hL ht hs y).1
  have hr : ∀ᵐ s ∂volume.restrict (Ioo 0 t), (∫ x, ‖H s x‖ ∂μ) ≤ A*C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [he] using (spatial_col μ N K L hK hL ht hs y).2
  have hh := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrableOn_const (C := A*C) (hs := measure_Ioo_lt_top.ne)) H hm.aestronglyMeasurable hi hr
  have hei (x : X) : ‖∫ s in Ioo 0 t, H s x‖ = weight N t x y*‖convolution μ K L t x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le,
      convolution]
  refine ⟨?_, ?_⟩
  · simpa only [hei] using hh.2.1.norm
  · have hb := hh.2.2
    simp only [hei, integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul] at hb
    simpa only [mul_assoc] using hb

lemma convolution_heatBound (N : ℕ) {T A C : ℝ} (hT : 0 ≤ T)
    (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L) :
    HeatBound μ N T (4*T*A*C) (convolution μ K L) := by
  refine ⟨convolution_measurable μ K L hK.measurable hL.measurable,
    by have hA := hK.nonneg; have hC := hL.nonneg; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x y
    apply (convolution_sup μ N K L hK hL ht x y).2.trans
    apply (div_le_div_iff₀ ht.1 (sq_pos_of_pos ht.1)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
      (mul_nonneg (mul_nonneg hK.nonneg hL.nonneg) ht.1.le)]
  · intro t ht x
    exact (convolution_row μ N K L hK hL ht x).1
  · intro t ht x
    apply (convolution_row μ N K L hK hL ht x).2.trans
    have ht' : t ≤ 4*T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' hK.nonneg) hL.nonneg
  · intro t ht y
    exact (convolution_col μ N K L hK hL ht y).1
  · intro t ht y
    apply (convolution_col μ N K L hK hL ht y).2.trans
    have ht' : t ≤ 4*T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' hK.nonneg) hL.nonneg

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end
end

end

end OAI
