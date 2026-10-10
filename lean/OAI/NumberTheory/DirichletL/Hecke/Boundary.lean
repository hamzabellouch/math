import OAI.NumberTheory.DirichletL.IdealEuler
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

namespace OAI

namespace SevenEighths.HeckeBoundary

open ActualEisensteinCubic Complex
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)
open Asymptotics Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_log_cpow_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-x : ℂ))).re +
      4 * (-log (1 - z * (n : ℂ) ^ (-(x + I * y)))).re +
      (-log (1 - z ^ 2 * (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  have hn' : (n : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz' : ‖z * (n : ℂ) ^ (-(I * y))‖ = 1 := by
    rw [norm_mul, hz, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : (0 : ℕ) < n))]
    simp
  convert! re_log_comb_nonneg (by positivity) hn' hz' using 6
  · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  · congr 2
    rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, mul_left_comm]
  · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
      mul_left_comm]

theorem summable_neg_log_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun P : PrimeIdeal => -log (1 - weighted a s P.val)) :=
  (prime_summable_norm a ha s hs).of_norm.clog_one_sub.neg

theorem exp_log_euler_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val)) = series a s := by
  have hp : HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹)
      (exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val))) :=
    (summable_neg_log_euler a ha s hs).hasSum.cexp.congr
      (fun S => Finset.prod_congr rfl (fun P _ => by
        simp only [Function.comp_apply]
        rw [exp_neg, exp_log (local_factor_ne_zero a ha s (by linarith) P)]))
  exact hp.unique (euler_hasProd a ha s hs)

def PrimeTriple (a₀ a₁ a₂ : Ideal O →*₀ ℂ) : Prop :=
  ∀ P : PrimeIdeal,
    (a₀ P.val = 0 ∧ a₁ P.val = 0 ∧ a₂ P.val = 0) ∨
    (a₀ P.val = 1 ∧ ‖a₁ P.val‖ = 1 ∧ a₂ P.val = a₁ P.val ^ 2)

theorem re_log_weighted_comb_nonneg (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) (P : PrimeIdeal) :
    0 ≤ 3 * (-log (1 - weighted a₀ (x : ℂ) P.val)).re +
      4 * (-log (1 - weighted a₁ (x + I * y) P.val)).re +
      (-log (1 - weighted a₂ (x + 2 * I * y) P.val)).re := by
  change 0 ≤ 3 * (-log (1 - a₀ P.val * normWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * normWeight (x + I * y) P.val)).re +
      (-log (1 - a₂ P.val * normWeight (x + 2 * I * y) P.val)).re
  rcases h P with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  · simp only [h₀, h₁, h₂, zero_mul, sub_zero, log_one, neg_zero, zero_re,
      mul_zero, add_zero, le_refl]
  · simp only [h₀, h₂, one_mul]
    change 0 ≤ 3 * (-log (1 - CubicEisenstein.fullIdealWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * CubicEisenstein.fullIdealWeight (x + I * y) P.val)).re +
      (-log (1 - a₁ P.val ^ 2 * CubicEisenstein.fullIdealWeight (x + 2 * I * y) P.val)).re
    simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
    exact re_log_cpow_comb_nonneg (SmoothMobiusCorrection.prime_norm_two_le P) hx y h₁

theorem norm_series_product_ge_one (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series a₀ (x : ℂ) ^ 3 * series a₁ (x + I * y) ^ 4 *
      series a₂ (x + 2 * I * y)‖ := by
  have hs₀ : 1 < (x : ℂ).re := hx
  have hs₁ : 1 < (x + I * y : ℂ).re := by simpa using hx
  have hs₂ : 1 < (x + 2 * I * y : ℂ).re := by simpa using hx
  have H₀ := summable_neg_log_euler a₀ ha₀ _ hs₀
  have H₁ := summable_neg_log_euler a₁ ha₁ _ hs₁
  have H₂ := summable_neg_log_euler a₂ ha₂ _ hs₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← exp_log_euler_eq_series a₀ ha₀ _ hs₀,
    ← exp_log_euler_eq_series a₁ ha₁ _ hs₁, ← exp_log_euler_eq_series a₂ ha₂ _ hs₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  exact tsum_nonneg fun P => re_log_weighted_comb_nonneg a₀ a₁ a₂ h hx y P

theorem square_unitInvariant (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : UnitInvariant M (χ ^ 2) := by
  intro u
  rw [χ.pow_apply' two_ne_zero, hχ u, one_pow]

theorem ofResidue_primeTriple (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    PrimeTriple (ofResidue M 1 (one_unitInvariant M))
      (ofResidue M χ hχ) (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) := by
  intro P
  let q := Ideal.Quotient.mk M (Submodule.IsPrincipal.generator P.val)
  have hv (ψ : MulChar (O ⧸ M) ℂ) (hψ : UnitInvariant M ψ) :
      ofResidue M ψ hψ P.val = ψ q := by
    change value M ψ P.val = _
    have hP : P.val ≠ ⊥ := P.property.ne_zero
    simp only [value, hP, ite_false, q]
  rw [hv, hv, hv]
  by_cases hq : IsUnit q
  · right
    refine ⟨MulChar.one_apply hq, ?_, χ.pow_apply' two_ne_zero q⟩
    let : Fintype (O ⧸ M)ˣ := Fintype.ofFinite _
    obtain ⟨u, hu⟩ := hq
    rw [← hu]
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using hn
  · left
    exact ⟨MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq⟩

theorem norm_residue_series_product_ge_one (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series (ofResidue M 1 (one_unitInvariant M)) (x : ℂ) ^ 3 *
      series (ofResidue M χ hχ) (x + I * y) ^ 4 *
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) (x + 2 * I * y)‖ :=
  norm_series_product_ge_one _ _ _
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ) hx y

theorem horizontal_isBigO_of_zero (F : ℂ → ℂ) (t : ℝ)
    (hF : DifferentiableAt ℂ F (1 + I * t)) (hz : F (1 + I * t) = 0) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hF.hasDerivAt
  rw [← zero_add (1 + _)] at h
  simpa only [zero_add, hz, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (h.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

theorem horizontal_isBigO_one (F : ℂ → ℂ) (t : ℝ)
    (hF : ContinuousAt F (1 + I * t)) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  rw [← zero_add (1 + _)] at hF
  exact hF.comp (f := fun x : ℝ => x + (1 + I * t)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

theorem boundary_ne_zero_of_series_eq (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) (F₀ F₁ F₂ : ℂ → ℂ)
    (hEq₀ : ∀ s : ℂ, 1 < s.re → F₀ s = series a₀ s)
    (hEq₁ : ∀ s : ℂ, 1 < s.re → F₁ s = series a₁ s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → F₂ s = series a₂ s)
    (t : ℝ)
    (hPole : (fun x : ℝ => F₀ (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x)
    (hReg₁ : DifferentiableAt ℂ F₁ (1 + I * t))
    (hReg₂ : ContinuousAt F₂ (1 + 2 * I * t)) : F₁ (1 + I * t) ≠ 0 := by
  intro hz
  have hLower (x : ℝ) (hx : 0 < x) :
      1 ≤ ‖F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t)‖ := by
    have hs₀ : 1 < (1 + x : ℂ).re := by simp; exact hx
    have hs₁ : 1 < (1 + x + I * t : ℂ).re := by simpa using hs₀
    have hs₂ : 1 < (1 + x + 2 * I * t : ℂ).re := by simpa using hs₀
    rw [hEq₀ _ hs₀, hEq₁ _ hs₁, hEq₂ _ hs₂]
    simpa only [ofReal_add, ofReal_one] using
      norm_series_product_ge_one a₀ a₁ a₂ ha₀ ha₁ ha₂ h (by linarith : 1 < 1 + x) t
  have hReg₂' : ContinuousAt F₂ (1 + I * ((2 * t : ℝ) : ℂ)) := by
    convert hReg₂ using 1
    push_cast
    ring
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by decide), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr hx), one_mul, mul_one]
  have H₀ : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx => (norm_one (α := ℝ)).symm ▸ (hLower x hx)
  have H := (hPole.pow 3).mul ((horizontal_isBigO_of_zero F₁ t hReg₁ hz).pow 4)
    |>.mul (horizontal_isBigO_one F₂ (2 * t) hReg₂')
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

section Quadratic

open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open UniqueFactorizationMonoid
open scoped ComplexOrder

def zetaConvolutionCoeff (a : Ideal O →*₀ ℂ) (B : Ideal O) : ℂ :=
  if B = 0 then 0 else ∑ D ∈ idealDivisors B, a D

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

@[simp] theorem zetaConvolutionCoeff_one (a : Ideal O →*₀ ℂ) :
    zetaConvolutionCoeff a 1 = 1 := by
  rw [zetaConvolutionCoeff, ite_eq_right one_ne_zero, idealDivisors_one, Finset.sum_singleton]
  exact map_one a

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem zetaConvolutionCoeff_prime_pow (a : Ideal O →*₀ ℂ) (P : Ideal O)
    (hP : Prime P) (k : ℕ) :
    zetaConvolutionCoeff a (P ^ k) = ∑ j ∈ Finset.range (k + 1), a P ^ j := by
  rw [zetaConvolutionCoeff, ite_eq_right (pow_ne_zero k hP.ne_zero), idealDivisors_prime_pow P hP k,
    Finset.sum_image]
  · simp only [map_pow]
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem zetaConvolutionCoeff_mul (a : Ideal O →*₀ ℂ) (B C : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsRelPrime B C) :
    zetaConvolutionCoeff a (B * C) = zetaConvolutionCoeff a B * zetaConvolutionCoeff a C := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  simp only [zetaConvolutionCoeff, hB, hC, mul_ne_zero hB hC, ite_false]
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem zetaConvolutionCoeff_nonneg (a : Ideal O →*₀ ℂ)
    (ha : ∀ P : Ideal O, Prime P → a P = 0 ∨ a P = 1 ∨ a P = -1)
    (B : Ideal O) : 0 ≤ zetaConvolutionCoeff a B := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => simp [zetaConvolutionCoeff]
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, zetaConvolutionCoeff_one]
    exact zero_le_one
  | hpr k hP =>
    rw [zetaConvolutionCoeff_prime_pow a _ hP k]
    rcases ha _ hP with hz | ho | hm
    · exact Finset.sum_nonneg (fun j _ => by rw [hz]; exact pow_nonneg (le_refl 0) j)
    · exact Finset.sum_nonneg (fun j _ => by rw [ho, one_pow]; exact zero_le_one)
    · rw [hm, neg_one_geom_sum]
      split_ifs <;> first | exact le_refl 0 | exact zero_le_one
  | @hcp B C hBC hB hC =>
    by_cases hB0 : B = 0
    · simp [hB0, zetaConvolutionCoeff]
    by_cases hC0 : C = 0
    · simp [hC0, zetaConvolutionCoeff]
    rw [zetaConvolutionCoeff_mul a B C hB0 hC0 hBC]
    exact mul_nonneg hB hC

theorem quadratic_normFiber_nonneg (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ ShortDraftHeckeBridge.normFiberCoeff
      (zetaConvolutionCoeff (ofResidue M χ hχ)) n := by
  apply Finset.sum_nonneg
  intro B _
  apply zetaConvolutionCoeff_nonneg
  intro P hP
  change value M χ P = 0 ∨ value M χ P = 1 ∨ value M χ P = -1
  have hP0 : P ≠ ⊥ := hP.ne_zero
  simp only [value, hP0, ite_false]
  exact MulChar.isQuadratic_iff_sq_eq_one.mpr hquad _

theorem mulFiber_character_sum (a : Ideal O →*₀ ℂ) (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, a p.val.1) = zetaConvolutionCoeff a B := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  rw [zetaConvolutionCoeff, ite_eq_right hB]
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, a D.val :=
      e.tsum_eq (fun D => a D.val)
    _ = _ := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl) a).symm

theorem zetaConvolution_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => zetaConvolutionCoeff a B * normWeight s B)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  let F : Ideal O × Ideal O → ℂ := fun p => a p.1 * normWeight s (p.1 * p.2)
  have hprod := (weighted_summable_norm a ha s hs).mul_norm
    (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  have heq (p : Ideal O × Ideal O) :
      weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 = F p := by
    change (a p.1 * normWeight s p.1) * normWeight s p.2 = _
    simp only [F, map_mul, mul_assoc]
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      zetaConvolutionCoeff a B * normWeight s B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, a p.val.1) * normWeight s B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_character_sum a B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  convert hsum using 1
  calc
    _ = ∑' p : Ideal O × Ideal O,
        weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (weighted_summable_norm a ha s hs)
        (CubicEisenstein.fullIdealWeight_summable_norm s hs)
    _ = _ := tsum_congr heq

theorem zetaConvolution_normFiber_one (a : Ideal O →*₀ ℂ) :
    ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a) 1 = 1 := by
  have hsingle : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {1} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff.trans (by rw [Ideal.one_eq_top])
  unfold ShortDraftHeckeBridge.normFiberCoeff
  rw [hsingle, Finset.sum_singleton, zetaConvolutionCoeff_one]

theorem zetaConvolution_LSeries_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  have h := (zetaConvolution_hasSum a ha s hs).tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // Ideal.absNorm I = n},
    zetaConvolutionCoeff a I.val * CubicEisenstein.fullIdealWeight s I.val) _ at h
  simpa only [SmoothMobiusCorrection.idealDirichlet_fiber] using h

theorem zetaConvolution_LSeries_eq (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s =
      series a s * CubicEisenstein.fullIdealZeta s :=
  (zetaConvolution_LSeries_hasSum a ha s hs).tsum_eq

theorem quadratic_product_positive (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hEq : ∀ s : ℂ, 1 < s.re →
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s) (y : ℝ) :
    0 < F y := by
  refine LSeries.positive_of_differentiable_of_eqOn
    (quadratic_normFiber_nonneg M χ hχ hquad)
    (zetaConvolution_normFiber_one (ofResidue M χ hχ) ▸ zero_lt_one) hF
    (x := 1) ?_ ?_ y
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => (zetaConvolution_LSeries_hasSum (ofResidue M χ hχ)
        (norm_ofResidue_le_one M χ hχ) s hs).summable)
  · intro s hs
    rw [hEq s hs, zetaConvolution_LSeries_eq (ofResidue M χ hχ)
      (norm_ofResidue_le_one M χ hχ) s hs]

theorem fullIdealZeta_eq_dirichlet_product (s : ℂ) (hs : 1 < s.re) :
    CubicEisenstein.fullIdealZeta s = riemannZeta s *
      (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s := by
  let a := normWeight 0
  have ha (I : Ideal O) : ‖a I‖ ≤ 1 := by
    by_cases hI : I = ⊥ <;> simp [a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hseries : series a s = CubicEisenstein.fullIdealZeta s := by
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hinverse : inverseSeries a s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff (1 : DirichletCharacter ℂ 1)
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))) s := by
    rw [← ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
      (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff (1 : DirichletCharacter ℂ 1)) s]
    rw [← SmoothMobiusCorrection.idealDirichlet_eq_LSeries
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one (1 : DirichletCharacter ℂ 1)) s hs]
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight,
        ShortDraftHeckeBridge.baseChangeWeight, hI, hchar]
  have hi := inverseSeries_mul_series a ha s hs
  have hp := ShortDraftHeckeBridge.pair_inverse_euler_identity
    (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)) s hs
  rw [← hinverse, DirichletCharacter.LFunction_modOne_eq] at hp
  rw [← hseries]
  calc
    series a s = 1 * series a s := (one_mul _).symm
    _ = ((riemannZeta s *
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s) *
          inverseSeries a s) * series a s := by rw [hp]
    _ = _ := by rw [mul_assoc, hi, mul_one]

def regularizedIdealZeta (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1 s *
    (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s

theorem regularizedIdealZeta_differentiable : Differentiable ℂ regularizedIdealZeta :=
  (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).mul
    (DirichletCharacter.differentiable_LFunction
      (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one
        (1 : DirichletCharacter ℂ 1) rfl))

theorem regularizedIdealZeta_eq (s : ℂ) (hs : 1 < s.re) :
    regularizedIdealZeta s = (s - 1) * CubicEisenstein.fullIdealZeta s := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs1, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_modOne_eq, fullIdealZeta_eq_dirichlet_product s hs,
    mul_assoc]

theorem regularizedIdealZeta_neg_two : regularizedIdealZeta (-2 : ℝ) = 0 := by
  have hz := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at hz
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne (by norm_num : (-2 : ℝ) ≠ (1 : ℂ)),
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  simp only [ofReal_neg, ofReal_ofNat, hz, mul_zero, zero_mul]

theorem differentiable_dslope_of_entire (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 c)).mpr
    hF.differentiableOn

theorem quadratic_one_ne_zero_of_regularized_zeta (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L R : ℂ → ℂ) (hL : Differentiable ℂ L) (hR : Differentiable ℂ R)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hReq : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * CubicEisenstein.fullIdealZeta s)
    (y : ℝ) (hRy : R y = 0) : L 1 ≠ 0 := by
  intro hz
  let F : ℂ → ℂ := fun s => R s * dslope L 1 s
  have hF : Differentiable ℂ F := hR.mul (differentiable_dslope_of_entire L hL 1)
  have hEq (s : ℂ) (hs : 1 < s.re) :
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s := by
    have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
    dsimp only [F]
    rw [hReq s hs, dslope_of_ne L hs1, slope, smul_eq_mul, vsub_eq_sub, hz, sub_zero,
      hLeq s hs]
    field_simp
  have hpos := quadratic_product_positive M χ hχ hquad F hF hEq y
  have hzero : F y = 0 := by simp only [F, hRy, zero_mul]
  exact hzero.not_gt hpos

theorem quadratic_one_ne_zero_of_entire (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) : L 1 ≠ 0 :=
  quadratic_one_ne_zero_of_regularized_zeta M χ hχ hquad L regularizedIdealZeta hL
    regularizedIdealZeta_differentiable hLeq regularizedIdealZeta_eq (-2)
    regularizedIdealZeta_neg_two

theorem normWeight_real_nonneg (x : ℝ) (B : Ideal O) : 0 ≤ normWeight (x : ℂ) B := by
  change 0 ≤ CubicEisenstein.fullIdealWeight (x : ℂ) B
  unfold CubicEisenstein.fullIdealWeight
  split_ifs
  · exact le_rfl
  · rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg _)]
    exact_mod_cast Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm B)) (-x)

theorem norm_series_le_norm_fullIdealZeta (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (x : ℝ) (hx : 1 < x) : ‖series a (x : ℂ)‖ ≤ ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ := by
  have hs : 1 < (x : ℂ).re := hx
  have hweight (I : Ideal O) :
      CubicEisenstein.fullIdealWeight (x : ℂ) I = (‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ : ℂ) :=
    eq_coe_norm_of_nonneg (normWeight_real_nonneg x I)
  have hnorm : ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ =
      ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ := by
    unfold CubicEisenstein.fullIdealZeta
    rw [tsum_congr hweight, ← ofReal_tsum,
      Complex.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  rw [hnorm]
  refine (norm_tsum_le_tsum_norm (weighted_summable_norm a ha _ hs)).trans ?_
  apply Summable.tsum_le_tsum _ (weighted_summable_norm a ha _ hs)
    (CubicEisenstein.fullIdealWeight_summable_norm _ hs)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight (x : ℂ) I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem fullIdealZeta_isBigO_near_one_horizontal :
    (fun x : ℝ => CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun x => (1 : ℂ) / x := by
  have hR : (fun x : ℝ => regularizedIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := by
    simpa only [ofReal_zero, mul_zero, add_zero] using horizontal_isBigO_one
      regularizedIdealZeta 0 (by simpa using (regularizedIdealZeta_differentiable 1).continuousAt)
  have hB : (fun x : ℝ => (x : ℂ) * CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := hR.congr'
    (eventually_nhdsWithin_of_forall (fun x hx => by
      dsimp only
      rw [regularizedIdealZeta_eq _ (by simpa using hx), add_sub_cancel_left]))
    (Filter.EventuallyEq.refl _ _)
  exact (isBigO_mul_iff_isBigO_div (eventually_nhdsWithin_of_forall
    (fun x hx => ofReal_ne_zero.mpr (ne_of_gt hx)))).mp hB

theorem series_isBigO_near_one_horizontal (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have h : (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0]
      fun x => CubicEisenstein.fullIdealZeta (1 + x) := by
    apply IsBigO.of_bound'
    apply eventually_nhdsWithin_of_forall
    intro x hx
    change 0 < x at hx
    simpa only [ofReal_add, ofReal_one] using
      norm_series_le_norm_fullIdealZeta a ha (1 + x) (by linarith)
  exact h.trans fullIdealZeta_isBigO_near_one_horizontal

theorem residue_boundary_ne_zero_of_series_eq (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L L₂ : ℂ → ℂ)
    (hEq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → L₂ s =
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) s)
    (t : ℝ) (hL : DifferentiableAt ℂ L (1 + I * t))
    (hL₂ : ContinuousAt L₂ (1 + 2 * I * t)) : L (1 + I * t) ≠ 0 :=
  boundary_ne_zero_of_series_eq
    (ofResidue M 1 (one_unitInvariant M)) (ofResidue M χ hχ)
    (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ))
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ)
    (series (ofResidue M 1 (one_unitInvariant M))) L L₂ (fun _ _ => rfl)
    hEq hEq₂ t
    (series_isBigO_near_one_horizontal _ (norm_ofResidue_le_one M 1 (one_unitInvariant M)))
    hL hL₂

end Quadratic

end

end SevenEighths.HeckeBoundary

end OAI
