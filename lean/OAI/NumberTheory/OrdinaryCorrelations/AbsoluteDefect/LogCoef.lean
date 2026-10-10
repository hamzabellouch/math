import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinaryPrimeSupply

variable {q : ℕ} [NeZero q] (a : ZMod q)

def logCoef (n : ℕ) : ℝ := vonMangoldt.residueClass a n / Real.log n

theorem logCoef_nonneg {q : ℕ} [NeZero q] (a : ZMod q) (n : ℕ) : 0 ≤ logCoef a n :=
  div_nonneg (vonMangoldt.residueClass_nonneg a n) (Real.log_natCast_nonneg n)

theorem logCoef_le_one {q : ℕ} [NeZero q] (a : ZMod q) (n : ℕ) : logCoef a n ≤ 1 := by
  by_cases hn : 1 < n
  · apply (div_le_one (Real.log_pos (by exact_mod_cast hn))).mpr
    exact (vonMangoldt.residueClass_le a n).trans vonMangoldt_le_log
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp [logCoef]

theorem logCoef_abscissa :
    LSeries.abscissaOfAbsConv (fun n => (logCoef a n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  refine ⟨1, fun n _ => ?_⟩
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (logCoef_nonneg a n)]
    using logCoef_le_one a n

theorem logMul_logCoef {q : ℕ} [NeZero q] (a : ZMod q) :
    LSeries.logMul (fun n => (logCoef a n : ℂ)) =
      fun n => (vonMangoldt.residueClass a n : ℂ) := by
  ext n
  by_cases hn : 1 < n
  · have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    change Complex.log (n : ℂ) * ((vonMangoldt.residueClass a n /
      Real.log n : ℝ) : ℂ) = _
    have hc : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
      (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [hc, ← Complex.ofReal_mul]
    congr 1
    exact mul_div_cancel₀ _ hlog
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · simp [LSeries.logMul, logCoef]
    · have hz : vonMangoldt.residueClass a 1 = 0 := le_antisymm
        (by simpa using vonMangoldt.residueClass_le a 1)
        (vonMangoldt.residueClass_nonneg a 1)
      simp [LSeries.logMul, logCoef, hz]

def smoothMass (s : ℝ) : ℝ :=
  (LSeries (fun n => (logCoef a n : ℂ)) (s : ℂ)).re

theorem hasDerivAt_smoothMass {s : ℝ} (hs : 1 < s) :
    HasDerivAt (smoothMass a)
      (-(LSeries (fun n => (vonMangoldt.residueClass a n : ℂ)) (s : ℂ)).re) s := by
  have hab : LSeries.abscissaOfAbsConv (fun n => (logCoef a n : ℂ)) <
      ((s : ℂ).re : EReal) := (logCoef_abscissa a).trans_lt (by exact_mod_cast hs)
  have h := (LSeries_hasDerivAt hab).real_of_complex
  change HasDerivAt (fun x : ℝ => (LSeries (fun n => (logCoef a n : ℂ)) x).re) _ s
  simpa only [logMul_logCoef, Complex.neg_re] using h

def regularPart (s : ℝ) : ℝ := (vonMangoldt.LFunctionResidueClassAux a s).re

theorem series_real_eq_regular (ha : IsUnit a) {s : ℝ} (hs : 1 < s) :
    (LSeries (fun n => (vonMangoldt.residueClass a n : ℂ)) s).re =
      regularPart a s + (q.totient : ℝ)⁻¹ / (s - 1) := by
  have hh := congrArg Complex.re (vonMangoldt.eqOn_LFunctionResidueClassAux ha (x := (s : ℂ))
    (by simpa using hs))
  have hc : (((q.totient : ℂ)⁻¹ / ((s : ℂ) - 1))).re =
      (q.totient : ℝ)⁻¹ / (s - 1) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_inv, ← Complex.ofReal_div, Complex.ofReal_re]
  change regularPart a s = _ at hh
  rw [Complex.sub_re, hc] at hh
  linarith

theorem hasDerivAt_adjusted (ha : IsUnit a) {s : ℝ} (hs : 1 < s) :
    HasDerivAt (fun x => smoothMass a x + (q.totient : ℝ)⁻¹ * Real.log (x - 1))
      (-regularPart a s) s := by
  have hl := ((Real.hasDerivAt_log (show s - 1 ≠ 0 by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)).const_mul (q.totient : ℝ)⁻¹
  convert! (hasDerivAt_smoothMass a hs).add hl using 1
  rw [series_real_eq_regular a ha hs]
  ring

theorem regularPart_continuousOn : ContinuousOn (regularPart a) (Set.Icc 1 2) := by
  exact Complex.continuous_re.continuousOn.comp (t := Set.univ)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux a) (fun _ _ => trivial)
      |>.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        simpa only [Set.mem_ofPred_eq, Complex.ofReal_re] using hx.1

theorem smoothMass_log_bound (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      |smoothMass a s + (q.totient : ℝ)⁻¹ * Real.log (s - 1)| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (regularPart_continuousOn a)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (by constructor <;> norm_num))
  refine ⟨C + |smoothMass a 2|, by positivity, ?_⟩
  intro s hs
  change 1 < s ∧ s ≤ 2 at hs
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => smoothMass a x + (q.totient : ℝ)⁻¹ * Real.log (x - 1))
    (f' := fun x => -regularPart a x) (s := Set.Icc s 2)
    (fun x hx => (hasDerivAt_adjusted a ha (hs.1.trans_le hx.1)).hasDerivWithinAt)
    (fun x hx => by simpa using hC x ⟨hs.1.le.trans hx.1, hx.2⟩)
    (convex_Icc s 2) (Set.mem_Icc.mpr ⟨hs.2, le_rfl⟩)
    (Set.mem_Icc.mpr ⟨le_rfl, hs.2⟩)
  have hdist : ‖s - 2‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, mul_zero,
    add_zero, Real.norm_eq_abs] at hh
  calc
    |smoothMass a s + (q.totient : ℝ)⁻¹ * Real.log (s - 1)|
      ≤ |(smoothMass a s + (q.totient : ℝ)⁻¹ * Real.log (s - 1)) -
           smoothMass a 2| + |smoothMass a 2| := by
        simpa only [sub_zero] using abs_sub_le
          (smoothMass a s + (q.totient : ℝ)⁻¹ * Real.log (s - 1))
            (smoothMass a 2) 0
    _ ≤ C + |smoothMass a 2| := by
      gcongr
      exact hh.trans (by simpa only [Real.norm_eq_abs] using mul_le_of_le_one_right hC0 hdist)

theorem real_LSeries_eq_tsum (f : ℕ → ℝ) (hf : f 0 = 0) (s : ℝ) :
    (LSeries (fun n => (f n : ℂ)) s).re = ∑' n, f n / (n : ℝ) ^ s := by
  have hc : LSeries (fun n => (f n : ℂ)) s =
      ((∑' n, f n / (n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    unfold LSeries
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp [hn, hf, LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hc, Complex.ofReal_re]

theorem smoothMass_eq_tsum {q : ℕ} [NeZero q] (a : ZMod q) (s : ℝ) :
    smoothMass a s = ∑' n, logCoef a n / (n : ℝ) ^ s :=
  real_LSeries_eq_tsum _ (by simp [logCoef]) s

theorem residueSeries_eq (ha : IsUnit a) {s : ℝ} (hs : 1 < s) :
    (∑' n, vonMangoldt.residueClass a n / (n : ℝ) ^ s) =
      regularPart a s + (q.totient : ℝ)⁻¹ / (s - 1) := by
  rw [← real_LSeries_eq_tsum _ (vonMangoldt.residueClass_apply_zero a)]
  exact series_real_eq_regular a ha hs

theorem logCoef_mul_log (n : ℕ) :
    logCoef a n * Real.log n = vonMangoldt.residueClass a n := by
  have hc := congrFun (logMul_logCoef a) n
  change Complex.log (n : ℂ) * (logCoef a n : ℂ) = _ at hc
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n),
    ← Complex.ofReal_mul] at hc
  have hr := Complex.ofReal_injective hc
  simpa [mul_comm] using hr

theorem residueSeries_summable {q : ℕ} [NeZero q] (a : ZMod q) {s : ℝ} (hs : 1 < s) :
    Summable (fun n => vonMangoldt.residueClass a n / (n : ℝ) ^ s) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hs))

theorem smoothSeries_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n => logCoef a n / (n : ℝ) ^ s) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((logCoef_abscissa a).trans_lt (by exact_mod_cast hs))

theorem scaled_residueSeries_bound (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      t * (∑' n, vonMangoldt.residueClass a n / (n : ℝ) ^ (1 + t)) ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (regularPart_continuousOn a)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (by constructor <;> norm_num))
  refine ⟨C + (q.totient : ℝ)⁻¹, by positivity, ?_⟩
  intro t ht
  change 0 < t ∧ t ≤ 1 at ht
  rw [residueSeries_eq a ha (by linarith), show 1 + t - 1 = t by ring, mul_add,
    mul_div_cancel₀ _ ht.1.ne']
  have hreg : regularPart a (1 + t) ≤ C := (le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs] using hC (1 + t) ⟨by linarith, by linarith⟩)
  gcongr
  exact (mul_le_mul_of_nonneg_left hreg ht.1.le).trans (mul_le_of_le_one_left hC0 ht.2)

theorem exp_sub_one_le_three_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u - 1 ≤ 3 * u := by
  have h := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg u)
    (Real.exp_pos u).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have he : Real.exp u ≤ 3 :=
    (Real.exp_le_exp.mpr hu1).trans Real.exp_one_lt_three.le
  nlinarith [mul_le_mul_of_nonneg_left he hu0]

theorem rpow_one_add {y t : ℝ} (hy : 0 < y) :
    y ^ (1 + t) = y * Real.exp (t * Real.log y) := by
  rw [Real.rpow_add hy, Real.rpow_one, Real.rpow_def_of_pos hy, mul_comm (Real.log y)]

theorem small_smoothing {y t c : ℝ} (hy : 0 < y) (hc : 0 ≤ c)
    (hu0 : 0 ≤ t * Real.log y) (hu1 : t * Real.log y ≤ 1) :
    c / y ≤ c / y ^ (1 + t) + 3 * t * (c * Real.log y) / y ^ (1 + t) := by
  have h := mul_le_mul_of_nonneg_left (exp_sub_one_le_three_mul hu0 hu1) hc
  have he : 0 < Real.exp (t * Real.log y) := Real.exp_pos _
  rw [rpow_one_add hy, ← add_div, le_div_iff₀ (mul_pos hy he)]
  field_simp
  nlinarith

theorem tail_smoothing {y t c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (hu : 1 ≤ t * Real.log y) :
    c / y ^ (1 + t) ≤ t * (c * Real.log y) / y ^ (1 + t) := by
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hy _)
  nlinarith [mul_le_mul_of_nonneg_left hu hc]

def cutoffTerm (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Finset.range (⌊x⌋₊ + 1) then logCoef a n / n else 0

def sharpMass (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), logCoef a n / n

theorem cutoffTerm_summable {q : ℕ} [NeZero q] (a : ZMod q) (x : ℝ) :
    Summable (cutoffTerm a x) := by
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet (Finset.range (⌊x⌋₊ + 1))).subset
  intro n hn
  by_contra h
  change n ∉ Finset.range (⌊x⌋₊ + 1) at h
  exact hn (by simp only [cutoffTerm, ite_eq_right h])

theorem tsum_cutoffTerm {q : ℕ} [NeZero q] (a : ZMod q) (x : ℝ) :
    ∑' n, cutoffTerm a x n = sharpMass a x := by
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊ + 1))
    (fun n hn => by simp [cutoffTerm, hn])]
  apply Finset.sum_congr rfl
  intro n hn
  simp [cutoffTerm, hn]

theorem smoothing_parameters {x : ℝ} (hx : Real.exp 1 ≤ x) :
    0 < (Real.log x)⁻¹ ∧ (Real.log x)⁻¹ ≤ 1 := by
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  constructor
  · positivity
  · exact inv_le_one_of_one_le₀ hlog

theorem cutoffTerm_upper {x : ℝ} (hx : Real.exp 1 ≤ x) (n : ℕ) :
    cutoffTerm a x n ≤ logCoef a n / (n : ℝ) ^ (1 + (Real.log x)⁻¹) +
      (3 * (Real.log x)⁻¹) *
        (vonMangoldt.residueClass a n / (n : ℝ) ^ (1 + (Real.log x)⁻¹)) := by
  have ht := (smoothing_parameters hx).1
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlog : 0 < Real.log x := inv_pos.mp ht
  by_cases hn0 : n = 0
  · simp [hn0, cutoffTerm, logCoef]
  have hn0R : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  by_cases hn : n ∈ Finset.range (⌊x⌋₊ + 1)
  · rw [cutoffTerm, ite_eq_left hn]
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp
      (by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hn)
    have hu0 : 0 ≤ (Real.log x)⁻¹ * Real.log (n : ℝ) :=
      mul_nonneg ht.le (Real.log_natCast_nonneg n)
    have hu1 : (Real.log x)⁻¹ * Real.log (n : ℝ) ≤ 1 := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (div_le_one hlog).mpr (Real.log_le_log hn0R hnx)
    simpa only [logCoef_mul_log, mul_div_assoc] using
      small_smoothing hn0R (logCoef_nonneg a n) hu0 hu1
  · rw [cutoffTerm, ite_eq_right hn]
    positivity [logCoef_nonneg a n, vonMangoldt.residueClass_nonneg a n]

theorem smoothTerm_upper {x : ℝ} (hx : Real.exp 1 ≤ x) (n : ℕ) :
    logCoef a n / (n : ℝ) ^ (1 + (Real.log x)⁻¹) ≤
      cutoffTerm a x n + (Real.log x)⁻¹ *
        (vonMangoldt.residueClass a n / (n : ℝ) ^ (1 + (Real.log x)⁻¹)) := by
  have ht := (smoothing_parameters hx).1
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlog : 0 < Real.log x := inv_pos.mp ht
  by_cases hn0 : n = 0
  · simp [hn0, cutoffTerm, logCoef]
  have hn0R : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  by_cases hn : n ∈ Finset.range (⌊x⌋₊ + 1)
  · rw [cutoffTerm, ite_eq_left hn]
    have hden : (n : ℝ) ≤ (n : ℝ) ^ (1 + (Real.log x)⁻¹) := by
      conv_lhs => rw [← Real.rpow_one (n : ℝ)]
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
      linarith
    have hle := div_le_div_of_nonneg_left (logCoef_nonneg a n) hn0R hden
    have hr : 0 ≤ (Real.log x)⁻¹ *
        (vonMangoldt.residueClass a n / (n : ℝ) ^ (1 + (Real.log x)⁻¹)) := by
      positivity [vonMangoldt.residueClass_nonneg a n]
    linarith
  · rw [cutoffTerm, ite_eq_right hn, zero_add]
    have hnx : x < (n : ℝ) := (Nat.floor_lt hx0.le).mp
      (by simpa only [Finset.mem_range, Nat.lt_add_one_iff, not_le] using hn)
    have hu : 1 ≤ (Real.log x)⁻¹ * Real.log (n : ℝ) := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (one_le_div hlog).mpr (Real.log_le_log hx0 hnx.le)
    simpa only [logCoef_mul_log, mul_div_assoc] using
      tail_smoothing hn0R.le (logCoef_nonneg a n) hu

theorem sharp_smooth_bound (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, Real.exp 1 ≤ x →
      |sharpMass a x - smoothMass a (1 + (Real.log x)⁻¹)| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := scaled_residueSeries_bound a ha
  refine ⟨3 * C, by positivity, ?_⟩
  intro x hx
  have ht := smoothing_parameters hx
  have hs : 1 < 1 + (Real.log x)⁻¹ := by linarith [ht.1]
  have hc := hC (Real.log x)⁻¹ ht
  have hres := residueSeries_summable a hs
  have hsm := smoothSeries_summable a hs
  have hu := Summable.tsum_le_tsum (cutoffTerm_upper a hx)
    (cutoffTerm_summable a x) (hsm.add (hres.mul_left (3 * (Real.log x)⁻¹)))
  rw [tsum_cutoffTerm, hsm.tsum_add (hres.mul_left (3 * (Real.log x)⁻¹)),
    tsum_mul_left, ← smoothMass_eq_tsum] at hu
  have hl := Summable.tsum_le_tsum (smoothTerm_upper a hx)
    hsm ((cutoffTerm_summable a x).add (hres.mul_left (Real.log x)⁻¹))
  rw [(cutoffTerm_summable a x).tsum_add (hres.mul_left (Real.log x)⁻¹),
    tsum_mul_left, tsum_cutoffTerm, ← smoothMass_eq_tsum] at hl
  rw [abs_le]
  constructor <;> nlinarith

theorem sharpMass_loglog_bound (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, Real.exp 1 ≤ x →
      |sharpMass a x - (q.totient : ℝ)⁻¹ * Real.log (Real.log x)| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := sharp_smooth_bound a ha
  obtain ⟨C₂, hC₂0, hC₂⟩ := smoothMass_log_bound a ha
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro x hx
  have ht := smoothing_parameters hx
  have hh := hC₂ (1 + (Real.log x)⁻¹) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [show 1 + (Real.log x)⁻¹ - 1 = (Real.log x)⁻¹ by ring,
    Real.log_inv, mul_neg, ← sub_eq_add_neg] at hh
  exact (abs_sub_le (sharpMass a x) (smoothMass a (1 + (Real.log x)⁻¹))
    ((q.totient : ℝ)⁻¹ * Real.log (Real.log x))).trans (add_le_add (hC₁ x hx) hh)

def primeMass (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun (p : ℕ) => p.Prime ∧ (p : ZMod q) = a),
    (p : ℝ)⁻¹

theorem logCoef_prime {q : ℕ} [NeZero q] (a : ZMod q) {p : ℕ} (hp : p.Prime) :
    logCoef a p = if (p : ZMod q) = a then 1 else 0 := by
  by_cases ha : (p : ZMod q) = a
  · simp [logCoef, vonMangoldt.residueClass, ha, vonMangoldt_apply_prime hp,
      hp.log_pos.ne']
  · simp [logCoef, vonMangoldt.residueClass, ha]

def nonprimeTerm (n : ℕ) : ℝ := (if n.Prime then 0 else logCoef a n) / n

theorem nonprimeTerm_nonneg (n : ℕ) : 0 ≤ nonprimeTerm a n := by
  unfold nonprimeTerm
  positivity [logCoef_nonneg a n]

theorem nonprimeTerm_summable : Summable (nonprimeTerm a) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Summable.of_nonneg_of_le (nonprimeTerm_nonneg a)
    (f := fun (n : ℕ) => (Real.log 2)⁻¹ *
      ((if n.Prime then 0 else vonMangoldt.residueClass a n) / n))
  · intro n
    by_cases hp : n.Prime
    · simp [nonprimeTerm, hp]
    by_cases hn : 1 < n
    · have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hcoef : logCoef a n ≤ (Real.log 2)⁻¹ * vonMangoldt.residueClass a n := by
        dsimp [logCoef]
        simpa only [div_eq_mul_inv, mul_comm] using div_le_div_of_nonneg_left
          (vonMangoldt.residueClass_nonneg a n) hlog hlogn
      simpa only [nonprimeTerm, ite_eq_right hp, mul_div_assoc] using
        div_le_div_of_nonneg_right hcoef (Nat.cast_nonneg n)
    · have hz : n = 0 ∨ n = 1 := by omega
      rcases hz with rfl | rfl
      · simp [nonprimeTerm, logCoef]
      · have hzero : vonMangoldt.residueClass a 1 = 0 := le_antisymm
          (by simpa using vonMangoldt.residueClass_le a 1)
          (vonMangoldt.residueClass_nonneg a 1)
        simp [nonprimeTerm, logCoef, hzero]
  · exact (vonMangoldt.summable_residueClass_non_primes_div a).mul_left _

theorem sharpMass_eq_primeMass_add (x : ℝ) :
    sharpMass a x = primeMass a x +
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), nonprimeTerm a n := by
  unfold sharpMass primeMass
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · rw [logCoef_prime a hp]
    by_cases ha : (n : ZMod q) = a <;> simp [hp, ha, nonprimeTerm]
  · simp [hp, nonprimeTerm]

theorem sharp_prime_bound (x : ℝ) :
    |sharpMass a x - primeMass a x| ≤ ∑' n, nonprimeTerm a n := by
  rw [sharpMass_eq_primeMass_add, add_sub_cancel_left,
    abs_of_nonneg (Finset.sum_nonneg (fun n _ => nonprimeTerm_nonneg a n))]
  exact Summable.sum_le_tsum _ (fun n _ => nonprimeTerm_nonneg a n)
    (nonprimeTerm_summable a)

theorem primeMass_loglog_bound (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, Real.exp 1 ≤ x →
      |primeMass a x - (q.totient : ℝ)⁻¹ * Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := sharpMass_loglog_bound a ha
  refine ⟨(∑' n, nonprimeTerm a n) + C, add_nonneg
    (tsum_nonneg (nonprimeTerm_nonneg a)) hC0, ?_⟩
  intro x hx
  have hm := sharp_prime_bound a x
  rw [abs_sub_comm] at hm
  exact (abs_sub_le (primeMass a x) (sharpMass a x)
    ((q.totient : ℝ)⁻¹ * Real.log (Real.log x))).trans (add_le_add hm (hC x hx))

def primeRange (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter (fun (p : ℕ) => p.Prime ∧ (p : ZMod q) = a)

theorem mem_primeRange {q : ℕ} [NeZero q] (a : ZMod q) {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primeRange a x ↔ p.Prime ∧ (p : ZMod q) = a ∧ (p : ℝ) ≤ x := by
  simp only [primeRange, Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff,
    Nat.le_floor_iff hx]
  tauto

def logPrimeWindow (u v : ℝ) : Finset ℕ :=
  (primeRange a (Real.exp v)).filter (fun p => u ≤ Real.log p ∧ Real.log p < v)

def logWindowMass (u v : ℝ) : ℝ := ∑ p ∈ logPrimeWindow a u v, (p : ℝ)⁻¹

theorem mem_logPrimeWindow {u v : ℝ} {p : ℕ} :
    p ∈ logPrimeWindow a u v ↔
      p.Prime ∧ (p : ZMod q) = a ∧ u ≤ Real.log p ∧ Real.log p < v := by
  rw [logPrimeWindow, Finset.mem_filter, mem_primeRange a (Real.exp_pos v).le]
  constructor
  · rintro ⟨⟨hp, ha, _⟩, hu, hv⟩
    exact ⟨hp, ha, hu, hv⟩
  · rintro ⟨hp, ha, hu, hv⟩
    exact ⟨⟨hp, ha, (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mp hv.le⟩,
      hu, hv⟩

theorem primeRange_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    primeRange a x ⊆ primeRange a y := by
  intro p hp
  rcases (mem_primeRange a hx).mp hp with ⟨hp, ha, hpx⟩
  exact (mem_primeRange a (hx.trans hxy)).mpr ⟨hp, ha, hpx.trans hxy⟩

theorem window_upper {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    primeMass a (Real.exp (u / 2)) + logWindowMass a u v ≤
      primeMass a (Real.exp v) := by
  have hd : Disjoint (primeRange a (Real.exp (u / 2))) (logPrimeWindow a u v) := by
    rw [Finset.disjoint_left]
    intro p hp hw
    rcases (mem_primeRange a (Real.exp_pos _).le).mp hp with ⟨hp, _, hpu⟩
    rcases (mem_logPrimeWindow a).mp hw with ⟨_, _, hlu, _⟩
    have hlog : Real.log (p : ℝ) ≤ u / 2 :=
      (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr hpu
    linarith
  have hsubset : primeRange a (Real.exp (u / 2)) ∪ logPrimeWindow a u v ⊆
      primeRange a (Real.exp v) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact primeRange_mono a (Real.exp_pos _).le
        (Real.exp_le_exp.mpr (by linarith)) hp
    · exact (Finset.mem_filter.mp hp).1
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (p : ℝ)⁻¹)
    hsubset (fun _ _ _ => by positivity)
  rw [Finset.sum_union hd] at hh
  exact hh

theorem window_lower {u v : ℝ} (hv : 0 < v) :
    primeMass a (Real.exp (v / 2)) ≤
      primeMass a (Real.exp u) + logWindowMass a u v := by
  have hsubset : primeRange a (Real.exp (v / 2)) ⊆
      primeRange a (Real.exp u) ∪ logPrimeWindow a u v := by
    intro p hp
    rcases (mem_primeRange a (Real.exp_pos _).le).mp hp with ⟨hp, ha, hpv⟩
    have hlog : Real.log (p : ℝ) ≤ v / 2 :=
      (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr hpv
    by_cases hpu : Real.log (p : ℝ) ≤ u
    · apply Finset.mem_union_left
      exact (mem_primeRange a (Real.exp_pos _).le).mpr ⟨hp, ha,
        (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mp hpu⟩
    · apply Finset.mem_union_right
      exact (mem_logPrimeWindow a).mpr ⟨hp, ha, le_of_not_ge hpu, by linarith⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (p : ℝ)⁻¹)
    hsubset (fun _ _ _ => by positivity)
  have hi := Finset.sum_union_inter (s₁ := primeRange a (Real.exp u))
    (s₂ := logPrimeWindow a u v) (f := fun p : ℕ => (p : ℝ)⁻¹)
  have hn : 0 ≤ ∑ p ∈ primeRange a (Real.exp u) ∩ logPrimeWindow a u v, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  change (∑ p ∈ primeRange a (Real.exp (v / 2)), (p : ℝ)⁻¹) ≤
    (∑ p ∈ primeRange a (Real.exp u), (p : ℝ)⁻¹) +
      ∑ p ∈ logPrimeWindow a u v, (p : ℝ)⁻¹
  linarith

theorem logWindowMass_bound (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, 2 ≤ u → u ≤ v →
      |logWindowMass a u v - (q.totient : ℝ)⁻¹ * Real.log (v / u)| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := primeMass_loglog_bound a ha
  refine ⟨2 * C + (q.totient : ℝ)⁻¹ * Real.log 2, by positivity, ?_⟩
  intro u v hu huv
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := hu0.trans_le huv
  have hb (y : ℝ) (hy : 1 ≤ y) :
      |primeMass a (Real.exp y) - (q.totient : ℝ)⁻¹ * Real.log y| ≤ C := by
    simpa only [Real.log_exp] using hC (Real.exp y) (Real.exp_le_exp.mpr hy)
  have h1 := (abs_le.mp (hb v (by linarith)))
  have h2 := (abs_le.mp (hb (u / 2) (by linarith)))
  have h3 := (abs_le.mp (hb (v / 2) (by linarith)))
  have h4 := (abs_le.mp (hb u (by linarith)))
  rw [Real.log_div hu0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h2
  rw [Real.log_div hv0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h3
  rw [Real.log_div hv0.ne' hu0.ne', abs_le]
  have hh := window_upper a hu0 huv
  have hl := window_lower a (u := u) hv0
  constructor <;> nlinarith

theorem mod_five_window_supplies :
    ∃ W₀ : ℝ, 10 ≤ W₀ ∧ ∀ W u : ℝ, W₀ ≤ W → 2 ≤ u →
      W ≤ logWindowMass (1 : ZMod 5) u (u * Real.exp (6 * W)) ∧
        logWindowMass (1 : ZMod 5) u (u * Real.exp (6 * W)) ≤ 2 * W := by
  obtain ⟨C, hC0, hC⟩ := logWindowMass_bound (1 : ZMod 5) isUnit_one
  refine ⟨max 10 (2 * C), le_max_left _ _, ?_⟩
  intro W u hW hu
  have hW10 : 10 ≤ W := (le_max_left _ _).trans hW
  have hCW : 2 * C ≤ W := (le_max_right _ _).trans hW
  have hu0 : 0 < u := by linarith
  have h_exp : 1 ≤ Real.exp (6 * W) := Real.one_le_exp_iff.mpr (by linarith)
  have hu' : u ≤ u * Real.exp (6 * W) := le_mul_of_one_le_right hu0.le h_exp
  have hh := hC u (u * Real.exp (6 * W)) hu hu'
  have hphi : (Nat.totient 5 : ℝ)⁻¹ = 1 / 4 := by
    rw [Nat.totient_prime (by decide : Nat.Prime 5)]
    norm_num
  rw [hphi, mul_div_cancel_left₀ _ hu0.ne', Real.log_exp] at hh
  rcases abs_le.mp hh with ⟨hl, hh⟩
  constructor <;> nlinarith

theorem logPrimeWindow_filter_not_dvd {m : ℕ} (hm : 0 < m) {u v : ℝ}
    (hu : Real.log m < u) :
    (logPrimeWindow a u v).filter (fun p => ¬ p ∣ m) = logPrimeWindow a u v := by
  apply Finset.filter_true_of_mem
  intro p hp hpm
  rcases (mem_logPrimeWindow a).mp hp with ⟨hp, _, hlu, _⟩
  have hpm' : (p : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd hm hpm
  have hl := Real.log_le_log (by exact_mod_cast hp.pos) hpm'
  linarith

end OrdinaryPrimeSupply

end

end OAI
