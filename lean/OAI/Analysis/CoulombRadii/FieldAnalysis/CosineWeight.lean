import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.OrbitalHilbertBasis

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

lemma evenOnSegment_intervalIntegrable {b : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b))) (c d : ℝ) :
    IntervalIntegrable (evenOnSegment b f) volume c d := by
  apply intervalIntegrable_iff.mpr
  let : IsFiniteMeasure (volume.restrict (uIoc c d)) := by
    unfold uIoc
    infer_instance
  exact ((evenOnSegment_memLp hf).restrict _).integrable (by norm_num)

lemma integral_evenOnSegment {b : ℝ} {f : ℝ → ℂ} (hb : 0 < b)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b)))
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x in (-b)..b, g x * evenOnSegment b f x) =
      ∫ x in (0 : ℝ)..b, (g x + g (-x)) * f x := by
  have hi (c d : ℝ) : IntervalIntegrable
      (fun x => g x * evenOnSegment b f x) volume c d :=
    (evenOnSegment_intervalIntegrable hf c d).continuousOn_mul hg.continuousOn
  have hn : IntervalIntegrable (fun x => g (-x) * evenOnSegment b f x) volume 0 b :=
    (evenOnSegment_intervalIntegrable hf 0 b).continuousOn_mul
      (hg.comp continuous_neg).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-b) 0) (hi 0 b)]
  have he : (∫ x in (-b)..(0 : ℝ), g x * evenOnSegment b f x) =
      ∫ x in (0 : ℝ)..b, g (-x) * evenOnSegment b f x := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := b)
      (fun x => g x * evenOnSegment b f x)
    simpa only [neg_zero, evenOnSegment_neg] using h.symm
  rw [he, ← intervalIntegral.integral_add hn (hi 0 b)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [uIoc_of_le hb.le] at hx
  rw [evenOnSegment_pos f hx]
  ring

lemma complex_exp_pair (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + Complex.exp ((-t : ℝ) * Complex.I) =
      2 * (Real.cos t : ℂ) := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

lemma cosine_natAbs (b x : ℝ) (n : ℤ) :
    (Real.cos ((n : ℝ) * Real.pi * x / b) : ℂ) = cosineMode b n.natAbs x := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp only [Int.cast_natCast, Int.natAbs_natCast, cosineMode]
  · simp only [Int.cast_neg, Int.cast_natCast, Int.natAbs_neg, Int.natAbs_natCast,
      neg_mul, neg_div, Real.cos_neg, cosineMode]

lemma fourier_pair_cosine {b : ℝ} (_hb : 0 < b) (n : ℤ) (x : ℝ) :
    fourier (-n) (x : AddCircle (b - -b)) +
      fourier (-n) ((-x : ℝ) : AddCircle (b - -b)) =
      2 * cosineMode b n.natAbs x := by
  rw [fourier_coe_apply, fourier_coe_apply]
  have h1 : (2 : ℂ) * Real.pi * Complex.I * (-n) * x / (b - -b) =
      ((-((n : ℝ) * Real.pi * x / b) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring
  have h2 : (2 : ℂ) * Real.pi * Complex.I * (-n) * (-x) / (b - -b) =
      (((n : ℝ) * Real.pi * x / b : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring
  simp only [Complex.ofReal_neg, Complex.ofReal_sub, Int.cast_neg] at h1 h2 ⊢
  rw [h1, h2, add_comm]
  simpa only [Complex.ofReal_neg, cosine_natAbs] using complex_exp_pair ((n : ℝ) * Real.pi * x / b)

lemma fourierOn_evenOnSegment {b : ℝ} {f : ℝ → ℂ} (hb : 0 < b)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b))) (n : ℤ) :
    fourierCoeffOn (by linarith : -b < b) (evenOnSegment b f) n =
      (1 / b : ℝ) • ∫ x in (0 : ℝ)..b, cosineMode b n.natAbs x * f x := by
  rw [fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul]
  rw [integral_evenOnSegment hb hf
    (fun x => fourier (-n) (x : AddCircle (b - -b))) (by fun_prop)]
  simp_rw [fourier_pair_cosine hb, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_sub, Complex.ofReal_neg]
  field_simp
  ring

theorem cosineModes_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (volume.restrict (Ioc 0 b)) (cosineMode b) := by
  intro f hf hz
  have he : evenOnSegment b f =ᵐ[volume.restrict (Ioc (-b) b)] 0 := by
    apply fourierOn_ae_zero (by linarith : -b < b) ((evenOnSegment_memLp hf).restrict _)
    intro n
    rw [fourierOn_evenOnSegment hb hf n]
    have hh := hz n.natAbs
    simp only [cosineMode, Complex.star_def, Complex.conj_ofReal] at hh
    have hh' : (∫ x in (0 : ℝ)..b, cosineMode b n.natAbs x * f x) = 0 := by
      simpa only [cosineMode, intervalIntegral.integral_of_le hb.le] using hh
    rw [hh', smul_zero]
  have hs : Ioc 0 b ⊆ Ioc (-b) b := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have he' := ae_restrict_of_ae_restrict_of_subset hs he
  filter_upwards [he', ae_restrict_mem measurableSet_Ioc] with x hx hxb
  simpa only [evenOnSegment_pos f hxb] using hx

lemma cosineMode_continuous (b : ℝ) (n : ℕ) : Continuous (cosineMode b n) := by
  unfold cosineMode
  fun_prop

lemma cosineMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (cosineMode b n) 2 (volume.restrict (Ioc 0 b)) := by
  apply MemLp.of_bound (cosineMode_continuous b n).aestronglyMeasurable 1
  filter_upwards with x
  simpa only [cosineMode, Complex.norm_real, Real.norm_eq_abs] using
    Real.abs_cos_le_one ((n : ℝ) * Real.pi * x / b)

lemma integral_cosine_product_pi (n m : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos (n * x) * Real.cos (m * x)) =
      if n = m then (if n = 0 then Real.pi else Real.pi / 2) else 0 := by
  classical
  have he := Polynomial.Chebyshev.integral_measureT_eq_integral_cos
    (f := fun x => (Polynomial.Chebyshev.T ℝ n).eval x *
      (Polynomial.Chebyshev.T ℝ m).eval x)
  simp only [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast] at he
  rw [← he]
  by_cases hnm : n = m
  · subst m
    simp only [ite_true]
    by_cases hn : n = 0
    · subst n
      simpa using Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    · simpa only [hn, ite_false] using
        Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn
  · simpa only [hnm, ite_false] using
      Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hnm

lemma integral_cosine_product {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in (0 : ℝ)..b,
      Real.cos ((n : ℝ) * Real.pi * x / b) *
      Real.cos ((m : ℝ) * Real.pi * x / b)) =
      if n = m then (if n = 0 then b else b / 2) else 0 := by
  classical
  have hc : Real.pi / b ≠ 0 := div_ne_zero Real.pi_ne_zero hb.ne'
  have he := intervalIntegral.integral_comp_mul_left
    (a := 0) (b := b) (c := Real.pi / b)
    (fun x : ℝ => Real.cos (n * x) * Real.cos (m * x)) hc
  have harg (k : ℕ) (x : ℝ) :
      (k : ℝ) * (Real.pi / b * x) = (k : ℝ) * Real.pi * x / b := by ring
  simp_rw [harg] at he
  rw [mul_zero, div_mul_cancel₀ _ hb.ne', integral_cosine_product_pi] at he
  rw [he, smul_eq_mul]
  split_ifs <;> field_simp
  simp

noncomputable def cosineWeight (b : ℝ) (n : ℕ) : ℝ := if n = 0 then b else b / 2

lemma cosineWeight_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < cosineWeight b n := by
  unfold cosineWeight
  split_ifs <;> positivity

lemma cosineMode_inner {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (cosineMode b n x) * cosineMode b m x) =
      if n = m then (cosineWeight b n : ℂ) else 0 := by
  calc
    _ = ((∫ x in Ioc 0 b, Real.cos ((n : ℝ) * Real.pi * x / b) *
       Real.cos ((m : ℝ) * Real.pi * x / b) : ℝ) : ℂ) := by
      trans ∫ x in Ioc 0 b, ((Real.cos ((n : ℝ) * Real.pi * x / b) *
        Real.cos ((m : ℝ) * Real.pi * x / b) : ℝ) : ℂ)
      · apply integral_congr_ae
        filter_upwards with x
        simp only [cosineMode, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
      · exact integral_ofReal
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hb.le, integral_cosine_product hb]
      by_cases hnm : n = m <;> simp only [hnm, ite_true, ite_false, cosineWeight, Complex.ofReal_zero]

noncomputable def neumannMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) * cosineMode b n x

lemma neumannMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (neumannMode b n) 2 (volume.restrict (Ioc 0 b)) :=
  (cosineMode_memLp b n).const_mul _

lemma neumannMode_star (b : ℝ) (n : ℕ) (x : ℝ) :
    star (neumannMode b n x) =
      ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) * star (cosineMode b n x) := by
  simp [neumannMode, star_mul, mul_comm]

lemma neumannMode_orthonormal {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (neumannMode b n x) * neumannMode b m x) =
      if n = m then 1 else 0 := by
  simp_rw [neumannMode_star, neumannMode]
  have he : ∀ x : ℝ,
      (((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) : ℂ) * star (cosineMode b n x) *
        ((((Real.sqrt (cosineWeight b m))⁻¹ : ℝ) : ℂ) * cosineMode b m x) =
      ((((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (cosineWeight b m))⁻¹ : ℝ) : ℂ)) *
        (star (cosineMode b n x) * cosineMode b m x) := by intro x; ring
  simp_rw [he]
  rw [integral_const_mul, cosineMode_inner hb]
  by_cases hnm : n = m
  · subst m
    simp only [ite_true]
    have hw := Real.sq_sqrt (cosineWeight_pos hb n).le
    have hn : Real.sqrt (cosineWeight b n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (cosineWeight_pos hb n))
    have hh : ((Real.sqrt (cosineWeight b n))⁻¹)^2 * cosineWeight b n = 1 := by
      calc
        _ = ((Real.sqrt (cosineWeight b n))⁻¹)^2 *
            (Real.sqrt (cosineWeight b n))^2 :=
          congrArg (fun t : ℝ => ((Real.sqrt (cosineWeight b n))⁻¹)^2 * t) hw.symm
        _ = 1 := by field_simp
    have hh' : ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) *
        ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) * cosineWeight b n = 1 := by
      simpa only [pow_two] using hh
    exact_mod_cast hh'
  · simp only [hnm, ite_false, mul_zero]

lemma neumannModes_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (volume.restrict (Ioc 0 b)) (neumannMode b) := by
  intro f hf hz
  apply cosineModes_complete hb f hf
  intro n
  have hh := hz n
  simp only [neumannMode_star, mul_assoc, integral_const_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply Complex.ofReal_ne_zero.mpr
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (cosineWeight_pos hb n))))

noncomputable def sineMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (Real.sin (((n : ℝ) + 1) * Real.pi * x / b) : ℂ)

lemma sineMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (sineMode b n) 2 (volume.restrict (Ioc 0 b)) := by
  apply MemLp.of_bound (show Continuous (sineMode b n) by unfold sineMode; fun_prop).aestronglyMeasurable 1
  filter_upwards with x
  simpa only [sineMode, Complex.norm_real, Real.norm_eq_abs] using
    Real.abs_sin_le_one (((n : ℝ) + 1) * Real.pi * x / b)

lemma integral_cosine_nonzero {b : ℝ} (hb : 0 < b) (n : ℕ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..b, Real.cos ((n : ℝ) * Real.pi * x / b)) = 0 := by
  simpa only [Nat.cast_zero, zero_mul, zero_div, Real.cos_zero, mul_one, hn, ite_false]
    using integral_cosine_product hb n 0

lemma integral_sine_product {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in (0 : ℝ)..b,
      Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
      Real.sin (((m : ℝ) + 1) * Real.pi * x / b)) =
      if n = m then b / 2 else 0 := by
  classical
  have he (x : ℝ) :
      Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
        Real.sin (((m : ℝ) + 1) * Real.pi * x / b) =
      Real.cos (((n : ℝ) + 1) * Real.pi * x / b) *
        Real.cos (((m : ℝ) + 1) * Real.pi * x / b) -
        Real.cos (((n : ℝ) + (m : ℝ) + 2) * Real.pi * x / b) := by
    have hh := Real.cos_add (((n : ℝ) + 1) * Real.pi * x / b)
      (((m : ℝ) + 1) * Real.pi * x / b)
    have ha : ((n : ℝ) + 1) * Real.pi * x / b +
        ((m : ℝ) + 1) * Real.pi * x / b =
        ((n : ℝ) + (m : ℝ) + 2) * Real.pi * x / b := by ring
    rw [ha] at hh
    linarith
  simp_rw [he]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hsum (x : ℝ) : ((n : ℝ) + (m : ℝ) + 2) * Real.pi * x / b =
      ((n + m + 2 : ℕ) : ℝ) * Real.pi * x / b := by push_cast; rfl
  simp_rw [hsum]
  rw [integral_cosine_nonzero hb (n + m + 2) (by omega), sub_zero]
  have hh := integral_cosine_product hb (n+1) (m+1)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_right_cancel_iff,
    Nat.add_one_ne_zero, ite_false] using hh

lemma sineMode_inner {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (sineMode b n x) * sineMode b m x) =
      if n = m then ((b / 2 : ℝ) : ℂ) else (0 : ℂ) := by
  calc
    _ = ((∫ x in Ioc 0 b,
      Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
      Real.sin (((m : ℝ) + 1) * Real.pi * x / b) : ℝ) : ℂ) := by
      trans ∫ x in Ioc 0 b, ((Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
        Real.sin (((m : ℝ) + 1) * Real.pi * x / b) : ℝ) : ℂ)
      · apply integral_congr_ae
        filter_upwards with x
        simp only [sineMode, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
      · exact integral_ofReal
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hb.le, integral_sine_product hb]
      by_cases hnm : n = m <;> simp only [hnm, ite_true, ite_false, Complex.ofReal_zero]

noncomputable def dirichletMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt (b / 2))⁻¹ : ℝ) * sineMode b n x

lemma dirichletMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (dirichletMode b n) 2 (volume.restrict (Ioc 0 b)) :=
  (sineMode_memLp b n).const_mul _

lemma dirichletMode_star (b : ℝ) (n : ℕ) (x : ℝ) :
    star (dirichletMode b n x) = dirichletMode b n x := by
  simp only [dirichletMode, sineMode, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma dirichletMode_orthonormal {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (dirichletMode b n x) * dirichletMode b m x) =
      if n = m then 1 else 0 := by
  change (∫ x in Ioc 0 b, star (((Real.sqrt (b / 2))⁻¹ : ℝ) * sineMode b n x) *
    (((Real.sqrt (b / 2))⁻¹ : ℝ) * sineMode b m x)) = _
  have he (x : ℝ) : star ((((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ) * sineMode b n x) *
      ((((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ) * sineMode b m x) =
      ((((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ))^2 * (star (sineMode b n x) * sineMode b m x) := by
    rw [star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  simp_rw [he]
  rw [integral_const_mul, sineMode_inner hb]
  by_cases hnm : n = m
  · simp only [hnm, ite_true]
    have hn : Real.sqrt (b / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have hh : ((Real.sqrt (b / 2))⁻¹)^2 * (b / 2) = 1 := by
      have hw := Real.sq_sqrt (show 0 ≤ b / 2 by positivity)
      calc
        _ = ((Real.sqrt (b / 2))⁻¹)^2 * (Real.sqrt (b / 2))^2 :=
          congrArg (fun t : ℝ => ((Real.sqrt (b / 2))⁻¹)^2 * t) hw.symm
        _ = 1 := by field_simp
    exact_mod_cast hh
  · simp only [hnm, ite_false, mul_zero]

lemma dirichletMode_hasDerivAt (b : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (dirichletMode b n)
      ((((n : ℝ) + 1) * Real.pi / b : ℝ) * neumannMode b (n+1) x) x := by
  have hlin : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1) * Real.pi * y / b)
      (((n : ℝ) + 1) * Real.pi / b) x := by
    simpa only [id, mul_one] using
      ((hasDerivAt_id x).const_mul (((n : ℝ) + 1) * Real.pi)).div_const b
  have hh := ((Real.hasDerivAt_sin _).comp x hlin).ofReal_comp.const_mul
    ((((Real.sqrt (b / 2))⁻¹ : ℝ)) : ℂ)
  have he : ((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) * neumannMode b (n+1) x =
      (((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ) *
        ((Real.cos (((n : ℝ) + 1) * Real.pi * x / b) *
          (((n : ℝ) + 1) * Real.pi / b) : ℝ) : ℂ) := by
    simp only [neumannMode, cosineWeight, Nat.add_one_ne_zero, ite_false,
      cosineMode, Nat.cast_add, Nat.cast_one, Complex.ofReal_mul]
    ring
  rw [he]
  exact hh

lemma dirichletMode_endpoints {b : ℝ} (hb : 0 < b) (n : ℕ) :
    dirichletMode b n 0 = 0 ∧ dirichletMode b n b = 0 := by
  constructor
  · simp [dirichletMode, sineMode]
  · have he : ((n : ℝ) + 1) * Real.pi * b / b = (n + 1 : ℕ) * Real.pi := by
      push_cast
      field_simp
    simp only [dirichletMode, sineMode, he, Real.sin_nat_mul_pi,
      Complex.ofReal_zero, mul_zero]

lemma dirichletMode_continuous (b : ℝ) (n : ℕ) :
    Continuous (dirichletMode b n) := by
  unfold dirichletMode sineMode
  fun_prop

lemma neumannMode_continuous (b : ℝ) (n : ℕ) :
    Continuous (neumannMode b n) :=
  continuous_const.mul (cosineMode_continuous b n)

lemma neumannMode_star_self (b : ℝ) (n : ℕ) (x : ℝ) :
    star (neumannMode b n x) = neumannMode b n x := by
  simp only [neumannMode, cosineMode, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma neumann_coefficient_derivative {b : ℝ} (hb : 0 < b) {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc 0 b, HasDerivAt f (g x) x)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 b))) (n : ℕ) :
    ((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) *
      (∫ x in Ioc 0 b, star (neumannMode b (n+1) x) * f x) =
      -(∫ x in Ioc 0 b, star (dirichletMode b n x) * g x) := by
  have hu : ∀ x ∈ uIcc 0 b, HasDerivAt (dirichletMode b n)
      (((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) * neumannMode b (n+1) x) x := by
    intro x _
    exact dirichletMode_hasDerivAt b n x
  have hv : ∀ x ∈ uIcc 0 b, HasDerivAt f (g x) x := by
    simpa only [uIcc_of_le hb.le] using hf
  have hu' : IntervalIntegrable (fun x =>
      (((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) * neumannMode b (n+1) x)) volume 0 b :=
    (continuous_const.mul (neumannMode_continuous b (n+1))).intervalIntegrable _ _
  have hv' : IntervalIntegrable g volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
    exact hg.integrable (by norm_num)
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [(dirichletMode_endpoints hb n).1, (dirichletMode_endpoints hb n).2,
    zero_mul, zero_mul, sub_self, zero_sub] at he
  simp_rw [mul_assoc] at he
  rw [intervalIntegral.integral_const_mul] at he
  simp_rw [neumannMode_star_self, dirichletMode_star]
  rw [← intervalIntegral.integral_of_le hb.le,
    ← intervalIntegral.integral_of_le hb.le, he]
  simp

theorem neumann_smooth_spectral_lower {b : ℝ} (hb : 0 < b) {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc 0 b, HasDerivAt f (g x) x)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 b))) (s : Finset ℕ) :
    ∑ n ∈ s, ((((n : ℝ) + 1) * Real.pi / b)^2 *
      ‖∫ x in Ioc 0 b, star (neumannMode b (n+1) x) * f x‖^2) ≤
      ∫ x in Ioc 0 b, ‖g x‖^2 := by
  let u : ℕ → Lp ℂ 2 (volume.restrict (Ioc 0 b)) :=
    fun n => (dirichletMode_memLp b n).toLp (dirichletMode b n)
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro n m
    rw [inner_toLp_complex]
    exact dirichletMode_orthonormal hb n m
  have hB := hu.sum_inner_products_le (hg.toLp g) (s := s)
  rw [norm_toLp_sq_complex hg] at hB
  convert hB using 1
  apply Finset.sum_congr rfl
  intro n _
  rw [inner_toLp_complex]
  have he := neumann_coefficient_derivative hb hf hg n
  have hnorm := congrArg (fun z : ℂ => ‖z‖^2) he
  simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs] using hnorm

section TensorNeumann
variable {A ι : Type*} [MeasurableSpace A] {ν : Measure A} [SigmaFinite ν]

end TensorNeumann
end Coulomb
end
end

end OAI
