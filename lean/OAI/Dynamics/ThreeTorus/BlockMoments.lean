import Mathlib

namespace OAI

/-! Finite-color moment laws, binomial estimates, and phase expansion. -/

section
noncomputable section
open scoped BigOperators
namespace ThreeTorus

lemma binomial_quadratic_remainder (n : ℕ) (y : ℝ) :
    |(1+y)^n-1-(n:ℝ)*y| ≤ (n:ℝ)^2/2*y^2*(1+|y|)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : 0 ≤ |y| := abs_nonneg y
    have hp : 1 ≤ (1+|y|)^(n+1) := one_le_pow₀ (by linarith)
    have hid : (1+y)^(n+1)-1-((n+1:ℕ):ℝ)*y =
        (1+y)*((1+y)^n-1-(n:ℝ)*y)+(n:ℝ)*y^2 := by
      rw [pow_succ]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ |(1+y)*((1+y)^n-1-(n:ℝ)*y)|+|(n:ℝ)*y^2| := abs_add_le _ _
      _ = |1+y| *|(1+y)^n-1-(n:ℝ)*y|+(n:ℝ)*y^2 := by
        rw [abs_mul, show |(n:ℝ)*y^2| = (n:ℝ)*y^2 from
          abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))]
      _ ≤ (1+|y|)*((n:ℝ)^2/2*y^2*(1+|y|)^n)+(n:ℝ)*y^2 := by
        gcongr
        simpa only [abs_one] using abs_add_le (1:ℝ) y
      _ = (n:ℝ)^2/2*y^2*(1+|y|)^(n+1)+(n:ℝ)*y^2 := by rw [pow_succ]; ring
      _ ≤ ((n+1:ℕ):ℝ)^2/2*y^2*(1+|y|)^(n+1) := by
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hp (mul_nonneg hn (sq_nonneg y))
        have hz : 0 ≤ y^2*(1+|y|)^(n+1) := by positivity
        push_cast
        nlinarith

lemma binomial_exponential_remainder (n : ℕ) (y : ℝ) :
    |(1+y)^n-1-(n:ℝ)*y| ≤ ((n:ℝ)*|y|)^2/2*Real.exp ((n:ℝ)*|y|) := by
  have he : (1+|y|)^n ≤ Real.exp ((n:ℝ)*|y|) := by
    calc
      _ ≤ (Real.exp |y|)^n := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp |y|]
      _ = _ := by rw [← Real.exp_nat_mul]
  calc
    _ ≤ (n:ℝ)^2/2*y^2*(1+|y|)^n := binomial_quadratic_remainder n y
    _ ≤ (n:ℝ)^2/2*y^2*Real.exp ((n:ℝ)*|y|) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [mul_pow,sq_abs]; ring

end ThreeTorus
noncomputable section
open MeasureTheory Complex Set Filter
open scoped Topology ComplexConjugate
namespace ThreeTorus

abbrev phaseHaar : Measure UnitAddCircle := AddCircle.haarAddCircle
abbrev phaseProduct (n : ℕ) : Measure (Fin n → UnitAddCircle) :=
  Measure.pi (fun _ => phaseHaar)

private lemma integrable_circle {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    Integrable f phaseHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def blockFactor (ell : ℝ) (a : ℂ) (z : UnitAddCircle) : ℝ :=
  1+2*ell*(a*conj (fourier 1 z)).re

def blockFactorC (ell : ℝ) (a : ℂ) (z : UnitAddCircle) : ℂ :=
  1+(ell:ℂ)*a*fourier (-1) z+(ell:ℂ)*conj a*fourier 1 z

lemma blockFactor_cast (ell : ℝ) (a : ℂ) (z : UnitAddCircle) :
    (blockFactor ell a z : ℂ) = blockFactorC ell a z := by
  rw [blockFactorC, fourier_neg]
  apply Complex.ext <;> simp [blockFactor, mul_re, mul_im] <;> ring

lemma continuous_blockFactor (ell : ℝ) (a : ℂ) : Continuous (blockFactor ell a) := by
  unfold blockFactor
  fun_prop

lemma continuous_blockFactorC (ell : ℝ) (a : ℂ) : Continuous (blockFactorC ell a) := by
  unfold blockFactorC
  fun_prop

lemma blockFactor_bounds {ell : ℝ} (hell : 0 ≤ ell) (a : ℂ) (z : UnitAddCircle) :
    1-2*ell*‖a‖ ≤ blockFactor ell a z ∧ blockFactor ell a z ≤ 1+2*ell*‖a‖ := by
  have hz : ‖fourier 1 z‖ = 1 := Circle.norm_coe _
  have he : |(a*conj (fourier 1 z)).re| ≤ ‖a‖ := by
    simpa only [norm_mul, norm_conj, hz, mul_one] using abs_re_le_norm (a*conj (fourier 1 z))
  obtain ⟨hl,hr⟩ := abs_le.mp he
  change 1-2*ell*‖a‖ ≤ 1+2*ell*(a*conj (fourier 1 z)).re ∧ 1+2*ell*(a*conj (fourier 1 z)).re ≤ 1+2*ell*‖a‖
  constructor <;> nlinarith

lemma integral_phase_character (k : ℤ) :
    (∫ z : UnitAddCircle, fourier k z ∂phaseHaar) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := phaseHaar)
      (fourier_add_half_inv_index hk (by norm_num))

lemma integral_character_blockFactorC (ell : ℝ) (a : ℂ) (k : ℤ) :
    (∫ z : UnitAddCircle, fourier k z * blockFactorC ell a z ∂phaseHaar) =
      (if k = 0 then 1 else 0)+(ell:ℂ)*a*(if k = 1 then 1 else 0)+
        (ell:ℂ)*conj a*(if k = -1 then 1 else 0) := by
  have he (z : UnitAddCircle) : fourier k z*blockFactorC ell a z =
      fourier k z+(ell:ℂ)*a*fourier (k-1) z+(ell:ℂ)*conj a*fourier (k+1) z := by
    rw [show k-1 = k+(-1) by omega, fourier_add, fourier_add]
    dsimp [blockFactorC]
    ring
  simp_rw [he]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul]
  · simp only [integral_phase_character, sub_eq_zero, add_eq_zero_iff_eq_neg]
  all_goals
    apply integrable_circle
    fun_prop

lemma integral_blockFactorC (ell : ℝ) (a : ℂ) :
    (∫ z, blockFactorC ell a z ∂phaseHaar) = 1 := by
  simpa using integral_character_blockFactorC ell a 0

lemma integral_blockFactor (ell : ℝ) (a : ℂ) :
    (∫ z, blockFactor ell a z ∂phaseHaar) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [blockFactor_cast]
  exact integral_blockFactorC ell a

lemma integral_blockFactorC_mul (ell : ℝ) (a b : ℂ) :
    (∫ z, blockFactorC ell a z * blockFactorC ell b z ∂phaseHaar) =
      1+(ell:ℂ)^2*(a*conj b+conj a*b) := by
  have he (z : UnitAddCircle) : blockFactorC ell a z*blockFactorC ell b z =
      blockFactorC ell b z + ((ell:ℂ)*a)*(fourier (-1) z*blockFactorC ell b z) +
        ((ell:ℂ)*conj a)*(fourier 1 z*blockFactorC ell b z) := by
    dsimp [blockFactorC]; ring
  simp_rw [he]
  rw [integral_add,integral_add,integral_const_mul,integral_const_mul]
  · rw [integral_blockFactorC,integral_character_blockFactorC,integral_character_blockFactorC]
    norm_num
    ring
  all_goals
    apply integrable_circle
    unfold blockFactorC
    fun_prop

lemma integral_blockFactor_mul (ell : ℝ) (a b : ℂ) :
    (∫ z, blockFactor ell a z * blockFactor ell b z ∂phaseHaar) =
      1+2*ell^2*(a*conj b).re := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, blockFactor_cast]
  rw [integral_blockFactorC_mul]
  apply Complex.ext <;> simp [mul_re,mul_im] <;> ring

def blockProduct (n : ℕ) (ell : ℝ) (a : ℂ) (z : Fin n → UnitAddCircle) : ℝ :=
  ∏ i, blockFactor ell a (z i)

lemma integral_blockProduct (n : ℕ) (ell : ℝ) (a : ℂ) :
    (∫ z, blockProduct n ell a z ∂phaseProduct n) = 1 := by
  unfold blockProduct
  rw [integral_fintype_prod_eq_pow]
  simp only [integral_blockFactor,one_pow]

lemma integral_blockProduct_mul (n : ℕ) (ell : ℝ) (a b : ℂ) :
    (∫ z, blockProduct n ell a z*blockProduct n ell b z ∂phaseProduct n) =
      (1+2*ell^2*(a*conj b).re)^n := by
  unfold blockProduct
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_pow (fun z => blockFactor ell a z*blockFactor ell b z),
    integral_blockFactor_mul,Fintype.card_fin]

lemma blockProduct_nonneg (n : ℕ) {ell : ℝ} (hell : 0 ≤ ell) (a : ℂ)
    (ha : 2*ell*‖a‖ ≤ 1) (z : Fin n → UnitAddCircle) : 0 ≤ blockProduct n ell a z := by
  apply Finset.prod_nonneg
  intro i _
  linarith [(blockFactor_bounds hell a (z i)).1]

lemma square_root_polynomial_bound {x : ℝ} (hx : 0 ≤ x) :
    1+(x-1)/2-(x-1)^2 ≤ Real.sqrt x := by
  have hs := Real.sq_sqrt hx
  have hp : 0 ≤ (Real.sqrt x-1)^2*((Real.sqrt x)^2+2*Real.sqrt x+1/2) := by positivity
  nlinarith [Real.sqrt_nonneg x]

lemma continuous_blockProduct (n : ℕ) (ell : ℝ) (a : ℂ) :
    Continuous (blockProduct n ell a) := by
  unfold blockProduct blockFactor
  fun_prop

private lemma integrable_phaseProduct {n : ℕ} {f : (Fin n → UnitAddCircle) → ℝ}
    (hf : Continuous f) : Integrable f (phaseProduct n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def blockMixture {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ)
    (z : Fin n → UnitAddCircle) : ℝ := ∑ r, t r * blockProduct n ell (a r) z

lemma continuous_blockMixture {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ) :
    Continuous (blockMixture t a n ell) := by
  unfold blockMixture
  apply continuous_finsetSum
  intro r _
  exact continuous_const.mul (continuous_blockProduct n ell (a r))

lemma integral_blockMixture {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ) :
    (∫ z, blockMixture t a n ell z ∂phaseProduct n) = ∑ r, t r := by
  unfold blockMixture
  rw [integral_finsetSum]
  · simp only [integral_const_mul,integral_blockProduct,mul_one]
  · intro r _
    exact (integrable_phaseProduct (continuous_blockProduct n ell (a r))).const_mul (t r)

lemma integral_blockMixture_sq {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) (n : ℕ) (ell : ℝ) :
    (∫ z, (blockMixture t a n ell z)^2 ∂phaseProduct n) =
      ∑ r, ∑ s, t r*t s*(1+2*ell^2*(a r*conj (a s)).re)^n := by
  have he (z : Fin n → UnitAddCircle) : (blockMixture t a n ell z)^2 =
      ∑ r, ∑ s, (t r*t s)*(blockProduct n ell (a r) z*blockProduct n ell (a s) z) := by
    simp only [blockMixture,pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    rw [integral_finsetSum]
    · simp only [integral_const_mul,integral_blockProduct_mul]
    · intro s _
      apply integrable_phaseProduct
      exact continuous_const.mul ((continuous_blockProduct n ell (a r)).mul (continuous_blockProduct n ell (a s)))
  · intro r _
    apply integrable_phaseProduct
    apply continuous_finsetSum
    intro s _
    exact continuous_const.mul ((continuous_blockProduct n ell (a r)).mul (continuous_blockProduct n ell (a s)))

lemma integral_blockMixture_variance {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ)
    (n : ℕ) (ell : ℝ) (ht : ∑ r, t r = 1) :
    (∫ z, (blockMixture t a n ell z-1)^2 ∂phaseProduct n) =
      (∑ r, ∑ s, t r*t s*(1+2*ell^2*(a r*conj (a s)).re)^n)-1 := by
  have hc := continuous_blockMixture t a n ell
  have hi := integrable_phaseProduct hc
  have hi2 := integrable_phaseProduct (hc.pow 2)
  simp_rw [show ∀ x : ℝ, (x-1)^2 = x^2-2*x+1 by intro x; ring]
  have hd : Integrable (fun z => (blockMixture t a n ell z)^2-2*blockMixture t a n ell z) (phaseProduct n) := hi2.sub (hi.const_mul 2)
  rw [integral_add hd (integrable_const (1:ℝ)),
    integral_sub (f := fun z => (blockMixture t a n ell z)^2) (g := fun z => 2*blockMixture t a n ell z) hi2 (hi.const_mul 2), integral_const_mul,
    integral_blockMixture_sq,integral_blockMixture,ht]
  simp
  ring

lemma blockMixture_nonneg {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) {ell : ℝ}
    (hell : 0 ≤ ell) (ht : ∀ r, 0 ≤ t r) (ha : ∀ r, 2*ell*‖a r‖ ≤ 1)
    (z : Fin n → UnitAddCircle) : 0 ≤ blockMixture t a n ell z := by
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (ht r) (blockProduct_nonneg n hell (a r) (ha r) z))

end ThreeTorus
noncomputable section
open MeasureTheory Complex
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

lemma weighted_complex_cross {m : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ) :
    (∑ r, ∑ s, t r*t s*(a r*conj (a s)).re) = ‖∑ r, (t r:ℂ)*a r‖^2 := by
  rw [← Complex.ofReal_re (‖∑ r, (t r:ℂ)*a r‖^2), Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im]
  ring

lemma block_pair_bound {n : ℕ} {ell delta : ℝ} (_hd : 0 ≤ delta)
    (hn : (n:ℝ)*ell^2 ≤ delta) {a b : ℂ} (ha : ‖a‖ ≤ 3) (hb : ‖b‖ ≤ 3) :
    (1+2*ell^2*(a*conj b).re)^n ≤ 1+2*(n:ℝ)*ell^2*(a*conj b).re+
      162*Real.exp (18*delta)*delta^2 := by
  have hnorm : |(a*conj b).re| ≤ 9 := by
    calc
      _ ≤ ‖a*conj b‖ := Complex.abs_re_le_norm _
      _ = ‖a‖*‖b‖ := by rw [norm_mul,Complex.norm_conj]
      _ ≤ 3*3 := mul_le_mul ha hb (norm_nonneg _) (by norm_num)
      _ = 9 := by norm_num
  have hy : (n:ℝ)*|2*ell^2*(a*conj b).re| ≤ 18*delta := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*ell^2 by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ (n:ℝ)*ell^2 by positivity)]
  have he := binomial_exponential_remainder n (2*ell^2*(a*conj b).re)
  have hr : ((n:ℝ)*|2*ell^2*(a*conj b).re|)^2/2*
      Real.exp ((n:ℝ)*|2*ell^2*(a*conj b).re|) ≤ 162*Real.exp (18*delta)*delta^2 := by
    calc
      _ ≤ (18*delta)^2/2*Real.exp (18*delta) := by gcongr
      _ = _ := by ring
  have hle := le_trans (le_abs_self _) (le_trans he hr)
  linarith

lemma blockMixture_variance_bound {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ)
    {ell delta : ℝ} (ht0 : ∀ r, 0 ≤ t r) (ht : ∑ r, t r = 1)
    (ha : ∀ r, ‖a r‖ ≤ 3) (hd : 0 ≤ delta) (hn : (n:ℝ)*ell^2 ≤ delta) :
    (∫ z, (blockMixture t a n ell z-1)^2 ∂phaseProduct n) ≤
      2*delta*‖∑ r, (t r:ℂ)*a r‖^2+162*Real.exp (18*delta)*delta^2 := by
  rw [integral_blockMixture_variance t a n ell ht]
  have he := fun r s => mul_le_mul_of_nonneg_left
    (block_pair_bound hd hn (ha r) (ha s)) (mul_nonneg (ht0 r) (ht0 s))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => he r s))
  have hmass : (∑ r, ∑ s, t r*t s) = 1 := by
    simp only [← Finset.mul_sum,ht,mul_one]
  have hid : (∑ r, ∑ s, t r*t s*(1+2*(n:ℝ)*ell^2*(a r*conj (a s)).re+
      162*Real.exp (18*delta)*delta^2)) =
      1+2*(n:ℝ)*ell^2*‖∑ r, (t r:ℂ)*a r‖^2+162*Real.exp (18*delta)*delta^2 := by
    rw [← weighted_complex_cross t a]
    have hid' (r s : Fin m) : t r*t s*(1+2*(n:ℝ)*ell^2*(a r*conj (a s)).re+
        162*Real.exp (18*delta)*delta^2) =
        t r*t s + (2*(n:ℝ)*ell^2)*(t r*t s*(a r*conj (a s)).re)+
        (t r*t s)*(162*Real.exp (18*delta)*delta^2) := by ring
    simp_rw [hid',Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
    simp only [ht,hmass]
    ring
  rw [hid] at hs
  have hn' := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖∑ r, (t r:ℂ)*a r‖)
  linarith

lemma blockMixture_hellinger_bound {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ)
    {ell delta : ℝ} (hell : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (ht0 : ∀ r, 0 ≤ t r) (ht : ∑ r, t r = 1)
    (ha : ∀ r, ‖a r‖ ≤ 3) (hd : 0 ≤ delta) (hn : (n:ℝ)*ell^2 ≤ delta) :
    1-2*delta*‖∑ r, (t r:ℂ)*a r‖^2-162*Real.exp (18*delta)*delta^2 ≤
      ∫ z, Real.sqrt (blockMixture t a n ell z) ∂phaseProduct n := by
  have hc := continuous_blockMixture t a n ell
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := phaseProduct n)
  have hiv := ((hc.sub (continuous_const (y := (1:ℝ)))).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := phaseProduct n)
  have his := (Real.continuous_sqrt.comp hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := phaseProduct n)
  have hp (z : Fin n → UnitAddCircle) : 0 ≤ blockMixture t a n ell z :=
    blockMixture_nonneg t a hell ht0 (fun r => by nlinarith [ha r]) z
  have hl := integral_mono
    (((integrable_const (1:ℝ)).add ((hi.sub (integrable_const (1:ℝ))).div_const 2)).sub hiv)
    his (fun z => square_root_polynomial_bound (hp z))
  simp only [Pi.sub_apply,Pi.add_apply,Pi.pow_apply,Function.comp_apply] at hl
  have he : (∫ z, 1+(blockMixture t a n ell z-1)/2-
      (blockMixture t a n ell z-1)^2 ∂phaseProduct n) =
      1-(∫ z, (blockMixture t a n ell z-1)^2 ∂phaseProduct n) := by
    rw [integral_sub (f := fun z => 1+(blockMixture t a n ell z-1)/2)
      (g := fun z => (blockMixture t a n ell z-1)^2) ((integrable_const (1:ℝ)).add
      ((hi.sub (integrable_const (1:ℝ))).div_const 2)) hiv,
      integral_add (f := fun _ => (1:ℝ)) (g := fun z => (blockMixture t a n ell z-1)/2) (integrable_const (1:ℝ)) ((hi.sub (integrable_const (1:ℝ))).div_const 2),
      integral_div,integral_sub (f := blockMixture t a n ell) (g := fun _ => (1:ℝ)) hi (integrable_const (1:ℝ)),integral_blockMixture,ht]
    simp
  rw [he] at hl
  linarith [blockMixture_variance_bound t a ht0 ht ha hd hn]

lemma block_hellinger_numerical_constant {delta : ℝ} (_hd0 : 0 ≤ delta) (hd : delta ≤ 1/100) :
    2*delta^2+162*Real.exp (18*delta)*delta^2*Real.sqrt 2 ≤ 300*delta^2 := by
  have he : Real.exp (18*delta) ≤ 50/41 := by
    calc
      _ ≤ Real.exp (18/100) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1/(1-18/100) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hs : Real.sqrt 2 ≤ (3:ℝ)/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]
  have hb : 162*Real.exp (18*delta)*delta^2*Real.sqrt 2 ≤
      162*(50/41)*delta^2*(3/2) := by gcongr
  nlinarith [sq_nonneg delta]

end ThreeTorus

noncomputable section
open MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
variable {X : Type*} [MeasurableSpace X] {mu : Measure X} [SigmaFinite mu]

/-- Tensor density on an n-fold product probability space. -/
def weightedProduct (h : X → ℝ) (n : ℕ) (z : Fin n → X) : ℝ := ∏ i, h (z i)

lemma weightedProduct_one_factor (h : X → ℝ) (g : X → ℂ) {n : ℕ} (i : Fin n)
    (hh : (∫ x, h x ∂mu) = 1) :
    (∫ z, (weightedProduct h n z:ℂ)*g (z i) ∂Measure.pi (fun _ : Fin n => mu)) =
      ∫ x, (h x:ℂ)*g x ∂mu := by
  classical
  have he (z : Fin n → X) : (weightedProduct h n z:ℂ)*g (z i) =
      ∏ k, ((h (z k):ℂ)*(if k=i then g (z k) else 1)) := by
    rw [Finset.prod_mul_distrib]
    simp [weightedProduct]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun k x => (h x:ℂ)*(if k=i then g x else 1))]
  have hi (k : Fin n) : (∫ x, (h x:ℂ)*(if k=i then g x else 1) ∂mu) =
      if k=i then ∫ x, (h x:ℂ)*g x ∂mu else 1 := by
    split_ifs <;> simp [integral_complex_ofReal,hh]
  simp_rw [hi]
  simp

lemma weightedProduct_two_centered (h : X → ℝ) (f : X → ℂ) {n : ℕ} (i j : Fin n)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ z, (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j))
        ∂Measure.pi (fun _ : Fin n => mu)) =
      if i=j then ∫ x, (h x:ℂ)*f x*conj (f x) ∂mu else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    simpa only [mul_assoc] using weightedProduct_one_factor h (fun x => f x*conj (f x)) i hh
  · rw [ite_eq_right hij]
    have he (z : Fin n → X) : (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j)) =
        ∏ k, ((h (z k):ℂ)*(if k=i then f (z k) else 1)*(if k=j then conj (f (z k)) else 1)) := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
      simp [weightedProduct]
    simp_rw [he]
    rw [integral_fintype_prod_eq_prod (fun k x => (h x:ℂ)*(if k=i then f x else 1)*(if k=j then conj (f x) else 1))]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [hij] using hf

variable [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X] [IsFiniteMeasure mu]

omit [MeasurableSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma continuous_weightedProduct (h : X → ℝ) (hc : Continuous h) (n : ℕ) :
    Continuous (weightedProduct h n) := by
  unfold weightedProduct
  fun_prop

lemma integral_weightedProduct_centered_sum (h : X → ℝ) (f : X → ℂ) (n : ℕ)
    (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ z, (weightedProduct h n z:ℂ)*(∑ i, f (z i))
      ∂Measure.pi (fun _ : Fin n => mu)) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · simp only [weightedProduct_one_factor h f _ hh,hf,Finset.sum_const_zero]
  · intro i _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (Complex.continuous_ofReal.comp (continuous_weightedProduct h hc n)).mul
      (fc.comp (continuous_apply i))

lemma integral_weightedProduct_centered_sq (h : X → ℝ) (f : X → ℂ) (n : ℕ)
    (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ z, weightedProduct h n z*‖∑ i, f (z i)‖^2
      ∂Measure.pi (fun _ : Fin n => mu)) =
        (n:ℝ) * ∫ x, h x*‖f x‖^2 ∂mu := by
  apply Complex.ofReal_injective
  push_cast
  rw [← integral_complex_ofReal,← integral_complex_ofReal]
  have he (z : Fin n → X) : (↑(weightedProduct h n z*‖∑ i, f (z i)‖^2):ℂ) =
      ∑ i, ∑ j, (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j)) := by
    push_cast
    rw [← Complex.mul_conj',map_sum]
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  have hi (i j : Fin n) : Integrable
      (fun z => (weightedProduct h n z:ℂ)*f (z i)*conj (f (z j)))
      (Measure.pi (fun _ : Fin n => mu)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact ((Complex.continuous_ofReal.comp (continuous_weightedProduct h hc n)).mul
      (fc.comp (continuous_apply i))).mul (Complex.continuous_conj.comp (fc.comp (continuous_apply j)))
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j),weightedProduct_two_centered h f _ _ hh hf]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  push_cast
  rw [mul_assoc,Complex.mul_conj']

end ThreeTorus

noncomputable section
open MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma integral_weighted_norm_sub_sq {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    {mu : Measure X} [IsFiniteMeasure mu]
    (h : X → ℝ) (f : X → ℂ) (c : ℂ) (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = c) :
    (∫ x, h x*‖f x-c‖^2 ∂mu) = (∫ x, h x*‖f x‖^2 ∂mu)-‖c‖^2 := by
  have intC {g : X → ℂ} (hg : Continuous g) : Integrable g mu :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : X) : (↑(h x*‖f x-c‖^2):ℂ) =
      (↑(h x*‖f x‖^2):ℂ) - ((h x:ℂ)*f x)*conj c -
      conj ((h x:ℂ)*f x)*c + (h x:ℂ)*(c*conj c) := by
    push_cast
    rw [← Complex.mul_conj',← Complex.mul_conj',map_sub,map_mul,Complex.conj_ofReal]
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [← integral_complex_ofReal,← integral_complex_ofReal]
  simp_rw [he]
  rw [integral_add,integral_sub,integral_sub,integral_mul_const,integral_mul_const,
    integral_mul_const,integral_conj,hf,integral_complex_ofReal,integral_complex_ofReal,hh]
  · simp only [mul_comm (conj c) c,Complex.mul_conj']
    push_cast
    ring
  all_goals apply intC; fun_prop

lemma integral_block_centered (ell : ℝ) (a : ℂ) :
    (∫ z, (blockFactor ell a z:ℂ)*(fourier 1 z-(ell:ℂ)*a) ∂phaseHaar) = 0 := by
  have hi := integrable_circle (continuous_blockFactorC ell a)
  simp_rw [blockFactor_cast,mul_sub]
  rw [integral_sub (by apply integrable_circle; unfold blockFactorC; fun_prop) (hi.mul_const _),integral_mul_const]
  have he := integral_character_blockFactorC ell a 1
  norm_num at he
  rw [show (∫ z, blockFactorC ell a z*fourier 1 z ∂phaseHaar) = (ell:ℂ)*a by
    simpa [mul_comm] using he,integral_blockFactorC]
  ring

lemma integral_block_centered_sq (ell : ℝ) (a : ℂ) :
    (∫ z, blockFactor ell a z*‖fourier 1 z-(ell:ℂ)*a‖^2 ∂phaseHaar) =
      1-ell^2*‖a‖^2 := by
  have he := integral_character_blockFactorC ell a 1
  have hm : (∫ z, (blockFactor ell a z:ℂ)*fourier 1 z ∂phaseHaar) = (ell:ℂ)*a := by
    simp_rw [blockFactor_cast]
    simpa [mul_comm] using he
  rw [integral_weighted_norm_sub_sq (blockFactor ell a) (fourier 1) ((ell:ℂ)*a)
    (continuous_blockFactor ell a) ((fourier 1).continuous) (integral_blockFactor ell a) hm]
  simp only [fourier_apply,norm_mul,Circle.norm_coe,one_pow,mul_one,Complex.norm_real,
    Real.norm_eq_abs,mul_pow,sq_abs]
  rw [integral_blockFactor]

lemma integral_block_sum_centered (ell : ℝ) (a : ℂ) (n : ℕ) :
    (∫ z, (blockProduct n ell a z:ℂ)*(∑ i, (fourier 1 (z i)-(ell:ℂ)*a))
      ∂phaseProduct n) = 0 := by
  exact integral_weightedProduct_centered_sum (blockFactor ell a)
    (fun z => fourier 1 z-(ell:ℂ)*a) n (continuous_blockFactor ell a)
    (((fourier 1).continuous).sub continuous_const) (integral_blockFactor ell a)
    (integral_block_centered ell a)

lemma integral_block_sum_centered_sq (ell : ℝ) (a : ℂ) (n : ℕ) :
    (∫ z, blockProduct n ell a z*‖∑ i, (fourier 1 (z i)-(ell:ℂ)*a)‖^2
      ∂phaseProduct n) = (n:ℝ)*(1-ell^2*‖a‖^2) := by
  change (∫ z, weightedProduct (blockFactor ell a) n z*‖∑ i, (fourier 1 (z i)-(ell:ℂ)*a)‖^2
      ∂phaseProduct n) = _
  rw [integral_weightedProduct_centered_sq (blockFactor ell a)
    (fun z => fourier 1 z-(ell:ℂ)*a) n (continuous_blockFactor ell a)
    (((fourier 1).continuous).sub continuous_const) (integral_blockFactor ell a)
    (integral_block_centered ell a),integral_block_centered_sq]

def blockEstimatorNoise (n : ℕ) (ell : ℝ) (a : ℂ) (z : Fin n → UnitAddCircle) : ℂ :=
  ((n:ℂ)*(ell:ℂ))⁻¹ * ∑ i, (fourier 1 (z i)-(ell:ℂ)*a)

lemma continuous_blockEstimatorNoise (n : ℕ) (ell : ℝ) (a : ℂ) :
    Continuous (blockEstimatorNoise n ell a) := by
  unfold blockEstimatorNoise
  fun_prop

lemma integral_blockEstimatorNoise (n : ℕ) (ell : ℝ) (a : ℂ) :
    (∫ z, (blockProduct n ell a z:ℂ)*blockEstimatorNoise n ell a z ∂phaseProduct n) = 0 := by
  unfold blockEstimatorNoise
  simp_rw [mul_left_comm (blockProduct n ell a _:ℂ)]
  rw [integral_const_mul,integral_block_sum_centered,mul_zero]

lemma integral_blockEstimatorNoise_sq {n : ℕ} (ell : ℝ) (a : ℂ)
    (hn : n ≠ 0) (he : ell ≠ 0) :
    (∫ z, blockProduct n ell a z*‖blockEstimatorNoise n ell a z‖^2 ∂phaseProduct n) =
      (1-ell^2*‖a‖^2)/((n:ℝ)*ell^2) := by
  simp only [blockEstimatorNoise,norm_mul,norm_inv,Complex.norm_natCast,Complex.norm_real,
    Real.norm_eq_abs,mul_pow,inv_pow,sq_abs]
  simp_rw [mul_left_comm (blockProduct n ell a _) ]
  rw [integral_const_mul,integral_block_sum_centered_sq]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

lemma integral_weighted_norm_add_centered {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    {mu : Measure X} [IsFiniteMeasure mu]
    (h : X → ℝ) (f : X → ℂ) (c : ℂ) (hc : Continuous h) (fc : Continuous f)
    (hh : (∫ x, h x ∂mu) = 1) (hf : (∫ x, (h x:ℂ)*f x ∂mu) = 0) :
    (∫ x, h x*‖c+f x‖^2 ∂mu) = ‖c‖^2+(∫ x, h x*‖f x‖^2 ∂mu) := by
  have intC {g : X → ℂ} (hg : Continuous g) : Integrable g mu :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid (x : X) : (↑(h x*‖c+f x‖^2):ℂ) =
      (h x:ℂ)*(c*conj c)+((h x:ℂ)*f x)*conj c+
      conj ((h x:ℂ)*f x)*c+(↑(h x*‖f x‖^2):ℂ) := by
    push_cast
    rw [← Complex.mul_conj',← Complex.mul_conj',map_add,map_mul,Complex.conj_ofReal]
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [← integral_complex_ofReal,← integral_complex_ofReal]
  simp_rw [hid]
  rw [integral_add,integral_add,integral_add,integral_mul_const,integral_mul_const,
    integral_mul_const,integral_conj,hf,integral_complex_ofReal,hh]
  · simp [Complex.mul_conj']
  all_goals apply intC; fun_prop

lemma block_estimator_previous_error {n : ℕ} (ell : ℝ) (a c : ℂ)
    (hn : n ≠ 0) (he : ell ≠ 0) :
    (∫ z, blockProduct n ell a z * ‖c+blockEstimatorNoise n ell a z‖^2 ∂phaseProduct n) =
      ‖c‖^2 + (1-ell^2*‖a‖^2)/((n:ℝ)*ell^2) := by
  rw [integral_weighted_norm_add_centered (blockProduct n ell a)
    (blockEstimatorNoise n ell a) c (continuous_blockProduct n ell a)
    (continuous_blockEstimatorNoise n ell a) (integral_blockProduct n ell a)
    (integral_blockEstimatorNoise n ell a),integral_blockEstimatorNoise_sq ell a hn he]

lemma block_estimator_variance_bound {n : ℕ} {ell delta : ℝ} (a : ℂ)
    (hd : 0 < delta) (hn : delta/2 ≤ (n:ℝ)*ell^2) :
    (1-ell^2*‖a‖^2)/((n:ℝ)*ell^2) ≤ 2/delta := by
  have hm : 0 < (n:ℝ)*ell^2 := by linarith
  rw [div_le_div_iff₀ hm hd]
  nlinarith [mul_nonneg (sq_nonneg ell) (sq_nonneg ‖a‖)]

end ThreeTorus

/-! Finite phase tests.  These are integral tests,
not a claim that a one-dimensional diagonal has product distribution. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology RealInnerProductSpace FourierTransform
namespace ThreeTorus

lemma circle_fourierCoeff_realIntegral (f : UnitAddCircle → ℂ) (n : ℤ) :
    fourierCoeff f n = ∫ v : ℝ, 𝐞 (-(v*(n : ℝ))) •
      (Ioc (0 : ℝ) 1).indicator (fun x : ℝ => f (x : UnitAddCircle)) v := by
  rw [fourierCoeff_eq_intervalIntegral f n 0]
  simp only [div_one, one_smul, zero_add]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : v ∈ Ioc (0 : ℝ) 1
  · simp only [indicator_of_mem hv, fourier_coe_apply, Circle.smul_def,
      Real.fourierChar_apply, Int.cast_neg, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_intCast, Complex.ofReal_one, div_one]
    congr 2
    ring
  · simp only [indicator_of_notMem hv, smul_zero]

lemma circle_fourierCoeff_tendsto (f : UnitAddCircle → ℂ) :
    Tendsto (fourierCoeff f) cofinite (𝓝 0) := by
  change Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0)
  simp_rw [circle_fourierCoeff_realIntegral]
  exact (Real.tendsto_integral_exp_smul_cocompact _).comp Int.tendsto_coe_cofinite

/-- A quantitative last-nonzero-frequency estimate. It admits an arbitrary
additional lower bound at each successive choice of L. -/
lemma separated_frequency_large {n : ℕ} {R D : ℤ} {L ν : Fin n → ℤ}
    (hL : ∀ i, 0 ≤ L i) (hν : ν ≠ 0) (hD : ∀ i, |ν i| ≤ D)
    (hgap : ∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) :
    R < |∑ i, ν i * L i| := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => ν i ≠ 0)
  have hs : s.Nonempty := by
    by_contra hh
    apply hν
    ext i
    have : i ∉ s := fun hi => hh ⟨i,hi⟩
    simpa [s] using this
  let j := s.max' hs
  have hj : ν j ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hmax (i : Fin n) (hi : j < i) : ν i = 0 := by
    by_contra hh
    have := Finset.le_max' s i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hh⟩)
    exact (not_le_of_gt hi) this
  let t := Finset.univ.filter (fun i : Fin n => i < j)
  have ht : t ⊆ Finset.univ.erase j := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hi).2.ne, Finset.mem_univ i⟩
  have he : (∑ i ∈ Finset.univ.erase j, ν i * L i) = ∑ i ∈ t, ν i * L i := by
    symm
    apply Finset.sum_subset ht
    intro i hi hn
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hij' : ¬ i < j := by simpa [t] using hn
    rw [hmax i (lt_of_le_of_ne (le_of_not_gt hij') (Ne.symm hij)), zero_mul]
  have hsum : (∑ i, ν i * L i) = (∑ i ∈ t, ν i * L i) + ν j * L j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),he]
  have hb : |∑ i ∈ t, ν i * L i| ≤ D * ∑ i ∈ t, L i := by
    calc
      _ ≤ ∑ i ∈ t, |ν i * L i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ t, D * L i := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [abs_mul,abs_of_nonneg (hL i)]
        exact mul_le_mul_of_nonneg_right (hD i) (hL i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hj1 : 1 ≤ |ν j| := by have := abs_pos.mpr hj; omega
  have hm : L j ≤ |ν j * L j| := by
    rw [abs_mul,abs_of_nonneg (hL j)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hj1 (hL j)
  have ha := abs_add_le (-(∑ i ∈ t, ν i * L i)) (∑ i, ν i * L i)
  rw [hsum, neg_add_cancel_left, abs_neg] at ha
  have hg := hgap j
  change R + D * ∑ i ∈ t, L i < L j at hg
  rw [hsum]
  omega

/-- Uniform Riemann--Lebesgue bounds for a finite coefficient list. -/
lemma finite_fourierCoeff_bound {ι : Type*} [Finite ι] (c : ι → UnitAddCircle → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℤ, 0 ≤ R ∧ ∀ k : ℤ, R < |k| → ∀ i, ‖fourierCoeff (c i) k‖ < ε := by
  have hh : ∀ᶠ k : ℤ in cofinite, ∀ i, ‖fourierCoeff (c i) k‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have ht := (circle_fourierCoeff_tendsto (c i)).norm
    exact ht.eventually (gt_mem_nhds (by simpa using hε))
  have hs : {k : ℤ | ¬ ∀ i, ‖fourierCoeff (c i) k‖ < ε}.Finite :=
    Filter.eventually_cofinite.mp hh
  obtain ⟨R,hR⟩ := (hs.image (fun k => |k|)).bddAbove
  refine ⟨max 0 R,le_max_left _ _,?_⟩
  intro k hk
  by_contra hn
  have hb : |k| ≤ R := hR ⟨k,hn,rfl⟩
  omega

local instance : MeasureSpace UnitAddCircle := ⟨phaseHaar⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure phaseHaar)

lemma phase_integral_mFourier {n : ℕ} (ν : Fin n → ℤ) :
    (∫ y : UnitAddTorus (Fin n), UnitAddTorus.mFourier ν y) =
      if ν = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin n))) 0 ν
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    eq_comm] using! h

lemma mFourier_diagonal {n : ℕ} (ν L : Fin n → ℤ) (z : UnitAddCircle) :
    UnitAddTorus.mFourier ν (fun i => L i • z) = fourier (∑ i, ν i * L i) z := by
  classical
  have h (s : Finset (Fin n)) :
      (∏ i ∈ s, fourier (ν i) (L i • z)) = fourier (∑ i ∈ s, ν i * L i) z := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, fourier_add,ih]
      congr 1
      simp only [fourier_apply,smul_smul]
  exact h Finset.univ

/-- A finite Laurent expression, with coefficients depending measurably on
its original circle variable. -/
def phaseTest {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ)
    (z : UnitAddCircle) (y : UnitAddTorus (Fin n)) : ℂ :=
  ∑ i, c i z * UnitAddTorus.mFourier (ν i) y

lemma integral_phaseTest_independent {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ)
    (hc : ∀ i, Integrable (c i) phaseHaar) :
    (∫ z, ∫ y, phaseTest c ν z y ∂volume ∂phaseHaar) =
      ∑ i, if ν i = 0 then ∫ z, c i z ∂phaseHaar else 0 := by
  classical
  have hm (i : ι) : Integrable (UnitAddTorus.mFourier (ν i)) :=
    (UnitAddTorus.mFourier (ν i)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (z : UnitAddCircle) : (∫ y, phaseTest c ν z y) =
      ∑ i, if ν i = 0 then c i z else 0 := by
    simp only [phaseTest]
    rw [integral_finsetSum _ (fun i _ => (hm i).const_mul (c i z))]
    simp_rw [integral_const_mul,phase_integral_mFourier]
    apply Finset.sum_congr rfl
    intro i _hi
    split_ifs <;> simp
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    split_ifs <;> simp
  · intro i _hi
    split_ifs
    · exact hc i
    · exact integrable_zero _ _ _

lemma integral_phaseTest_diagonal {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ)
    (hc : ∀ i, Integrable (c i) phaseHaar) (L : Fin n → ℤ) :
    (∫ z, phaseTest c ν z (fun i => L i • z) ∂phaseHaar) =
      ∑ i, fourierCoeff (c i) (-(∑ j, ν i j * L j)) := by
  simp only [phaseTest,mFourier_diagonal]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    simp only [fourierCoeff,neg_neg,smul_eq_mul,mul_comm]
  · intro i _hi
    simpa only [smul_eq_mul,mul_comm] using
      (hc i).fourier_smul (∑ j, ν i j * L j)

/-- All of a finite family of phase tests are accurate for every sufficiently
separated positive frequency tuple.  Thus the gaps can be strengthened during
a geometric construction without invalidating earlier tests. -/
lemma finite_phase_test_bounds {κ ι : Type*} [Fintype κ] [Fintype ι] {n : ℕ}
    (c : κ → ι → UnitAddCircle → ℂ) (ν : κ → ι → Fin n → ℤ)
    (hc : ∀ k i, Integrable (c k i) phaseHaar) {ε : ℝ} (hε : 0 < ε) :
    ∃ R D : ℤ, 0 ≤ R ∧ 0 ≤ D ∧ ∀ L : Fin n → ℤ,
      (∀ i, 0 ≤ L i) →
      (∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) →
      ∀ k, ‖(∫ z, phaseTest (c k) (ν k) z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, phaseTest (c k) (ν k) z y ∂volume ∂phaseHaar)‖ < ε := by
  classical
  let η : ℝ := ε / (Fintype.card ι + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨R,hR,hbound⟩ := finite_fourierCoeff_bound
    (fun a : κ × ι => c a.1 a.2) hη
  obtain ⟨D,hD⟩ := (Set.finite_range
    (fun a : κ × ι × Fin n => |ν a.1 a.2.1 a.2.2|)).bddAbove
  have hd (k : κ) (i : ι) (j : Fin n) : |ν k i j| ≤ max 0 D :=
    (hD (Set.mem_range_self (k,i,j))).trans (le_max_right _ _)
  refine ⟨R,max 0 D,hR,le_max_left _ _,?_⟩
  intro L hL hgap k
  rw [integral_phaseTest_diagonal _ _ (hc k),
    integral_phaseTest_independent _ _ (hc k), ← Finset.sum_sub_distrib]
  have hi (i : ι) :
      ‖fourierCoeff (c k i) (-(∑ j, ν k i j * L j)) -
        (if ν k i = 0 then ∫ z, c k i z ∂phaseHaar else 0)‖ ≤ η := by
    by_cases hn : ν k i = 0
    · simpa [hn, fourierCoeff] using hη.le
    · rw [ite_eq_right hn,sub_zero]
      apply (hbound _ ?_ (k,i)).le
      rw [abs_neg]
      exact separated_frequency_large hL hn (hd k i) hgap
  calc
    _ ≤ ∑ i, ‖fourierCoeff (c k i) (-(∑ j, ν k i j * L j)) -
        (if ν k i = 0 then ∫ z, c k i z ∂phaseHaar else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, η := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card ι : ℝ) * η := by simp
    _ < ε := by
      dsimp [η]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).2
      nlinarith

/-- The recursive choices allow any finite lower bound depending on the
already selected frequencies. -/
def phaseFrequencies (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) : ℕ → ℤ :=
  Nat.strongRec fun j prev =>
    max 0 (max (B j (fun i => prev i i.isLt))
      (R + D * ∑ i : Fin j, prev i i.isLt)) + 1

lemma phaseFrequencies_eq (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) (j : ℕ) :
    phaseFrequencies R D B j = max 0
      (max (B j (fun i => phaseFrequencies R D B i))
        (R + D * ∑ i : Fin j, phaseFrequencies R D B i)) + 1 := by
  unfold phaseFrequencies
  rw [Nat.strongRec_eq]

lemma sum_fin_lt_eq_prefix {n : ℕ} (L : ℕ → ℤ) (j : Fin n) :
    (∑ i ∈ Finset.univ.filter (· < j), L (i : Fin n)) =
      ∑ i : Fin j, L i := by
  classical
  apply Finset.sum_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi i' hi' he
    exact Fin.ext (Fin.mk.inj he)
  · intro i _hi
    refine ⟨⟨i.val, i.isLt.trans j.isLt⟩,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩
    · rfl
  · intro i hi
    rfl

lemma phaseFrequencies_pos (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) (j : ℕ) :
    0 < phaseFrequencies R D B j := by
  rw [phaseFrequencies_eq]
  have := le_max_left (0 : ℤ)
    (max (B j (fun i => phaseFrequencies R D B i))
      (R + D * ∑ i : Fin j, phaseFrequencies R D B i))
  omega

lemma phaseFrequencies_lower (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) (j : ℕ) :
    B j (fun i => phaseFrequencies R D B i) < phaseFrequencies R D B j := by
  rw [phaseFrequencies_eq]
  have := (le_max_left (B j (fun i => phaseFrequencies R D B i))
    (R + D * ∑ i : Fin j, phaseFrequencies R D B i)).trans (le_max_right 0 _)
  omega

lemma phaseFrequencies_gap (R D : ℤ) (B : (j : ℕ) → (Fin j → ℤ) → ℤ)
    {n : ℕ} (j : Fin n) :
    R + D * ∑ i ∈ Finset.univ.filter (· < j), phaseFrequencies R D B (i : Fin n) <
      phaseFrequencies R D B j := by
  rw [sum_fin_lt_eq_prefix,phaseFrequencies_eq R D B j]
  have := (le_max_right (B j (fun i => phaseFrequencies R D B i))
    (R + D * ∑ i : Fin j, phaseFrequencies R D B i)).trans (le_max_right 0 _)
  omega

/-- Source Lemma `phase-tests`, including arbitrary lower bounds at each
successive frequency choice. -/
theorem finite_phase_tests {κ ι : Type*} [Fintype κ] [Fintype ι] {n : ℕ}
    (c : κ → ι → UnitAddCircle → ℂ) (ν : κ → ι → Fin n → ℤ)
    (hc : ∀ k i, Integrable (c k i) phaseHaar) {ε : ℝ} (hε : 0 < ε)
    (B : (j : ℕ) → (Fin j → ℤ) → ℤ) :
    ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
      (∀ j : Fin n, B j (fun i => L ⟨i.val, i.isLt.trans j.isLt⟩) < L j) ∧
      ∀ k, ‖(∫ z, phaseTest (c k) (ν k) z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, phaseTest (c k) (ν k) z y ∂volume ∂phaseHaar)‖ < ε := by
  obtain ⟨R,D,_hR,_hD,h⟩ := finite_phase_test_bounds c ν hc hε
  refine ⟨fun j => phaseFrequencies R D B j,?_,?_,?_⟩
  · exact fun j => phaseFrequencies_pos R D B j
  · exact fun j => phaseFrequencies_lower R D B j
  · exact h _ (fun j => (phaseFrequencies_pos R D B j).le)
      (fun j => phaseFrequencies_gap R D B j)

end ThreeTorus
end
end
end
end
end
end
end

section

/-! The two tests are actual finite Laurent expressions. Their expansions
do not assume phase independence. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- A bounded measurable coefficient on the temporal circle. -/
def CircleBounded (f : UnitAddCircle → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C

lemma CircleBounded.integrable {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    Integrable f phaseHaar := by
  obtain ⟨hm,C,_hC,hb⟩ := hf
  exact (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall hb)

lemma CircleBounded.const (c : ℂ) : CircleBounded (fun _ => c) :=
  ⟨measurable_const,‖c‖,norm_nonneg c,fun _ => le_rfl⟩

lemma CircleBounded.add {f g : UnitAddCircle → ℂ} (hf : CircleBounded f)
    (hg : CircleBounded g) : CircleBounded (fun z => f z+g z) := by
  obtain ⟨hf,C,hC,hfB⟩ := hf
  obtain ⟨hg,D,hD,hgB⟩ := hg
  exact ⟨hf.add hg,C+D,add_nonneg hC hD,fun z =>
    (norm_add_le _ _).trans (add_le_add (hfB z) (hgB z))⟩

lemma CircleBounded.mul {f g : UnitAddCircle → ℂ} (hf : CircleBounded f)
    (hg : CircleBounded g) : CircleBounded (fun z => f z*g z) := by
  obtain ⟨hf,C,hC,hfB⟩ := hf
  obtain ⟨hg,D,hD,hgB⟩ := hg
  refine ⟨hf.mul hg,C*D,mul_nonneg hC hD,fun z => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hfB z) (hgB z) (norm_nonneg _) hC

lemma CircleBounded.conj {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    CircleBounded (fun z => conj (f z)) := by
  obtain ⟨hf,C,hC,hB⟩ := hf
  exact ⟨Complex.continuous_conj.measurable.comp hf,C,hC,fun z => by simpa using hB z⟩

lemma CircleBounded.continuous {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    CircleBounded f := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨hf.measurable,max 0 C,le_max_left _ _,fun z =>
    (hC z (mem_univ z)).trans (le_max_right _ _)⟩

/-- An actual finite expansion; every coefficient is proved measurable and
bounded. The finite coefficient type can vary with the expression. -/
def PhaseLaurent {n : ℕ} (F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ) : Prop :=
  ∃ (ι : Type) (fi : Fintype ι), letI := fi
    ∃ (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ),
      (∀ i, CircleBounded (c i)) ∧ ∀ z y, F z y = phaseTest c ν z y

lemma PhaseLaurent.coeff {n : ℕ} {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    PhaseLaurent (fun z (_ : Fin n → UnitAddCircle) => f z) := by
  refine ⟨Unit,inferInstance,fun _ => f,fun _ => 0,fun _ => hf,?_⟩
  intro z y
  simp [phaseTest,UnitAddTorus.mFourier_zero]

lemma PhaseLaurent.character {n : ℕ} (ν : Fin n → ℤ) :
    PhaseLaurent (fun (_ : UnitAddCircle) y => UnitAddTorus.mFourier ν y) := by
  refine ⟨Unit,inferInstance,fun _ _ => 1,fun _ => ν,fun _ => CircleBounded.const 1,?_⟩
  intro z y
  simp [phaseTest]

lemma PhaseLaurent.add {n : ℕ} {F G : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (hG : PhaseLaurent G) : PhaseLaurent (fun z y => F z y+G z y) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  obtain ⟨κ,fk,d,μ,hd,hG⟩ := hG
  let _ := fi
  let _ := fk
  refine ⟨ι ⊕ κ,inferInstance,Sum.elim c d,Sum.elim ν μ,?_,?_⟩
  · intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hd i
  · intro z y
    dsimp only
    rw [hF,hG]
    simp [phaseTest,Fintype.sum_sum_type]

lemma PhaseLaurent.mul {n : ℕ} {F G : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (hG : PhaseLaurent G) : PhaseLaurent (fun z y => F z y*G z y) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  obtain ⟨κ,fk,d,μ,hd,hG⟩ := hG
  let _ := fi
  let _ := fk
  refine ⟨ι × κ,inferInstance,fun i z => c i.1 z*d i.2 z,
    fun i => ν i.1+μ i.2,fun i => (hc i.1).mul (hd i.2),?_⟩
  intro z y
  dsimp only
  rw [hF,hG]
  simp only [phaseTest,Fintype.sum_prod_type,UnitAddTorus.mFourier_add,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma PhaseLaurent.conj {n : ℕ} {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) : PhaseLaurent (fun z y => conj (F z y)) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  refine ⟨ι,inferInstance,fun i z => conj (c i z),fun i => -ν i,
    fun i => (hc i).conj,?_⟩
  intro z y
  dsimp only
  rw [hF]
  simp [phaseTest,UnitAddTorus.mFourier_neg]

lemma PhaseLaurent.neg {n : ℕ} {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) : PhaseLaurent (fun z y => -F z y) := by
  simpa only [neg_one_mul] using (PhaseLaurent.coeff (CircleBounded.const (-1))).mul hF

lemma PhaseLaurent.sub {n : ℕ} {F G : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (hG : PhaseLaurent G) : PhaseLaurent (fun z y => F z y-G z y) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma PhaseLaurent.sum {n : ℕ} {ι : Type*} (S : Finset ι)
    {F : ι → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ} (hF : ∀ i ∈ S, PhaseLaurent (F i)) :
    PhaseLaurent (fun z y => ∑ i ∈ S, F i z y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (PhaseLaurent.coeff (n := n) (CircleBounded.const 0))
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

lemma PhaseLaurent.prod {n : ℕ} {ι : Type*} (S : Finset ι)
    {F : ι → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ} (hF : ∀ i ∈ S, PhaseLaurent (F i)) :
    PhaseLaurent (fun z y => ∏ i ∈ S, F i z y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (PhaseLaurent.coeff (n := n) (CircleBounded.const 1))
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hF i (Finset.mem_insert_self i S)).mul
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

lemma PhaseLaurent.norm_sq {n : ℕ} {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) : PhaseLaurent (fun z y => (‖F z y‖^2:ℝ)) := by
  simpa only [Complex.mul_conj',Complex.ofReal_pow] using hF.mul hF.conj

local instance : MeasureSpace UnitAddCircle := ⟨phaseHaar⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure phaseHaar)

lemma PhaseLaurent.bounds {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ} (hF : PhaseLaurent F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R D : ℤ, 0 ≤ R ∧ 0 ≤ D ∧ ∀ L : Fin n → ℤ,
      (∀ i, 0 ≤ L i) →
      (∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) →
      ‖(∫ z, F z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, F z y ∂phaseProduct n ∂phaseHaar)‖ < ε := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  obtain ⟨R,D,hR,hD,h⟩ := finite_phase_test_bounds
    (κ := Unit) (fun _ => c) (fun _ => ν) (fun _ i => (hc i).integrable) hε
  refine ⟨R,D,hR,hD,fun L hL hgap => ?_⟩
  simpa only [hF] using! h L hL hgap ()

lemma PhaseLaurent.finite_bounds {κ : Type*} [Fintype κ] {n : ℕ}
    {F : κ → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : ∀ k, PhaseLaurent (F k)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R D : ℤ, 0 ≤ R ∧ 0 ≤ D ∧ ∀ L : Fin n → ℤ,
      (∀ i, 0 ≤ L i) →
      (∀ j, R + D * ∑ i ∈ Finset.univ.filter (· < j), L i < L j) →
      ∀ k, ‖(∫ z, F k z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, F k z y ∂phaseProduct n ∂phaseHaar)‖ < ε := by
  classical
  choose R D hR hD h using fun k => (hF k).bounds hε
  refine ⟨∑ k, R k,∑ k, D k,Finset.sum_nonneg (fun k _ => hR k),
    Finset.sum_nonneg (fun k _ => hD k),?_⟩
  intro L hL hgap k
  apply h k L hL
  intro j
  apply lt_of_le_of_lt _ (hgap j)
  apply add_le_add
  · exact Finset.single_le_sum (fun i _ => hR i) (Finset.mem_univ k)
  · apply mul_le_mul_of_nonneg_right
    · exact Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ k)
    · exact Finset.sum_nonneg (fun i _ => hL i)

/-- Compatible averaging for any finite collection of expressions assembled
from the actual fixed pre-block data, with all forward construction bounds. -/
theorem PhaseLaurent.finite_tests {κ : Type*} [Fintype κ] {n : ℕ}
    {F : κ → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : ∀ k, PhaseLaurent (F k)) {ε : ℝ} (hε : 0 < ε)
    (B : (j : ℕ) → (Fin j → ℤ) → ℤ) :
    ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
      (∀ j : Fin n, B j (fun i => L ⟨i.val, i.isLt.trans j.isLt⟩) < L j) ∧
      ∀ k, ‖(∫ z, F k z (fun i => L i • z) ∂phaseHaar) -
        (∫ z, ∫ y, F k z y ∂phaseProduct n ∂phaseHaar)‖ < ε := by
  obtain ⟨R,D,_hR,_hD,h⟩ := PhaseLaurent.finite_bounds hF hε
  refine ⟨fun j => phaseFrequencies R D B j,?_,?_,?_⟩
  · exact fun j => phaseFrequencies_pos R D B j
  · exact fun j => phaseFrequencies_lower R D B j
  · exact h _ (fun j => (phaseFrequencies_pos R D B j).le)
      (fun j => phaseFrequencies_gap R D B j)

end ThreeTorus
end
end

end OAI
