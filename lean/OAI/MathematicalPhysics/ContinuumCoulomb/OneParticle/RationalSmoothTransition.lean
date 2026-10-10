import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalExponential
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! Rational approximation of the explicit smooth transition. Exponents
near the flat junction are truncated before Taylor evaluation, keeping
both the magnitude parameter and the error polynomial in the precision. -/

namespace ContinuumCoulomb.RationalSmoothTransition

def clip (q : ℚ) : ℚ := max 0 (min 1 q)

theorem clip_bounds (q : ℚ) : 0 ≤ clip q ∧ clip q ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_error (q : ℚ) {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : |(q:ℝ)-a| ≤ ε) : |(clip q:ℝ)-a| ≤ ε := by
  have he := abs_le.mp hq
  by_cases hq0 : q ≤ 0
  · have hqR : (q:ℝ) ≤ 0 := by exact_mod_cast hq0
    simp only [clip, min_eq_right (hq0.trans (by norm_num : (0:ℚ) ≤ 1)),
      max_eq_left hq0, Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg ha0]
    linarith
  · by_cases hq1 : 1 ≤ q
    · have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq1
      simp only [clip, min_eq_left hq1, max_eq_right (by norm_num : (0:ℚ) ≤ 1),
        Rat.cast_one, abs_of_nonneg (sub_nonneg.mpr ha1)]
      linarith
    · simpa only [clip, min_eq_right (le_of_not_ge hq1),
        max_eq_right (le_of_not_ge hq0)] using hq

def flat (p : ℕ) (q : ℚ) : ℚ :=
  if (p+1 : ℚ)⁻¹ < q then
    clip (RationalExponential.approximate (p+1) (p+1) (-q⁻¹))
  else 0

theorem flat_bounds (p : ℕ) (q : ℚ) : 0 ≤ flat p q ∧ flat p q ≤ 1 := by
  unfold flat
  split_ifs
  · exact clip_bounds _
  · constructor <;> norm_num

private theorem two_pow_bound (p : ℕ) : p+1 ≤ 2^(p+1) := by
  induction p with
  | zero => norm_num
  | succ p ih =>
    rw [pow_succ]
    omega

theorem flat_error (p : ℕ) (q : ℚ) :
    |(flat p q:ℝ)-expNegInvGlue (q:ℝ)| ≤ ((p:ℝ)+1)⁻¹ := by
  have hp : (0:ℝ) < (p:ℝ)+1 := by positivity
  have hpQ : (0:ℚ) < (p+1:ℚ) := by positivity
  have hg0 : 0 ≤ expNegInvGlue (q:ℝ) := expNegInvGlue.nonneg _
  have hg1 : expNegInvGlue (q:ℝ) ≤ 1 := by
    by_cases hq : (q:ℝ) ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hq]; norm_num
    · rw [expNegInvGlue, ite_eq_right hq]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hq)))
  unfold flat
  split_ifs with hq
  · have hqR : ((p:ℝ)+1)⁻¹ < (q:ℝ) := by
      have hh := (Rat.cast_lt (K := ℝ)).mpr hq
      simpa only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using hh
    have hqp : (0:ℝ) < (q:ℝ) := (inv_pos.mpr hp).trans hqR
    have hinv : (q:ℝ)⁻¹ ≤ (p:ℝ)+1 := by
      exact (inv_le_comm₀ hqp hp).mpr hqR.le
    have he := RationalExponential.error (p+1) (p+1) (-q⁻¹) (by
      push_cast
      rw [abs_neg, abs_of_pos (inv_pos.mpr hqp)]
      simpa only [Nat.cast_add, Nat.cast_one] using hinv)
    have hprec : (2^(p+1):ℝ)⁻¹ ≤ ((p:ℝ)+1)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) hp).mpr
      exact_mod_cast two_pow_bound p
    have he' : |(RationalExponential.approximate (p+1) (p+1) (-q⁻¹):ℝ) -
        expNegInvGlue (q:ℝ)| ≤ ((p:ℝ)+1)⁻¹ := by
      rw [expNegInvGlue, ite_eq_right (not_le.mpr hqp)]
      simpa only [Rat.cast_neg, Rat.cast_inv, abs_sub_comm] using he.trans hprec
    exact clip_error _ hg0 hg1 he'
  · have hqR : (q:ℝ) ≤ ((p:ℝ)+1)⁻¹ := by
      have hh := (Rat.cast_le (K := ℝ)).mpr (le_of_not_gt hq)
      simpa only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using hh
    by_cases hqp : (q:ℝ) ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hqp]
      simpa using (inv_nonneg.mpr hp.le)
    · have hqp' : (0:ℝ) < (q:ℝ) := lt_of_not_ge hqp
      have hexp : (q:ℝ)⁻¹ ≤ Real.exp (q:ℝ)⁻¹ := by
        linarith [Real.add_one_le_exp ((q:ℝ)⁻¹)]
      have hinv : (Real.exp (q:ℝ)⁻¹)⁻¹ ≤ (q:ℝ) := by
        simpa only [inv_inv] using
          (inv_le_inv₀ (Real.exp_pos _) (inv_pos.mpr hqp')).mpr hexp
      rw [Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hg0, expNegInvGlue, ite_eq_right hqp,
        Real.exp_neg]
      exact hinv.trans hqR

theorem transition_denominator_lower (x : ℝ) :
    (1/9:ℝ) ≤ expNegInvGlue x + expNegInvGlue (1-x) := by
  have he : Real.exp 2 ≤ 9 := by
    rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hinv : (1/9:ℝ) ≤ expNegInvGlue (1/2) := by
    norm_num only [expNegInvGlue, show ¬ ((1/2:ℝ) ≤ 0) by norm_num, ite_false,
      one_div, inv_inv, inv_div, mul_one]
    rw [Real.exp_neg]
    exact (le_inv_comm₀ (by norm_num) (Real.exp_pos _)).mpr (by simpa using he)
  by_cases hx : (1/2:ℝ) ≤ x
  · exact hinv.trans ((expNegInvGlue.monotone hx).trans
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · have hy : (1/2:ℝ) ≤ 1-x := by linarith
    exact hinv.trans ((expNegInvGlue.monotone hy).trans
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

def precision (p : ℕ) : ℕ := 1000*(p+1)

def approximate (p : ℕ) (q : ℚ) : ℚ :=
  flat (precision p) q / (flat (precision p) q + flat (precision p) (1-q))

theorem quotient_error {a b a' b' ε : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 1/9 ≤ a+b)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/1000)
    (hea : |a'-a| ≤ ε) (heb : |b'-b| ≤ ε) :
    |a'/(a'+b')-a/(a+b)| ≤ 342*ε := by
  have hden : |(a'+b')-(a+b)| ≤ 2*ε := by
    have h := (abs_add_le (a'-a) (b'-b)).trans (add_le_add hea heb)
    convert h using 1 <;> ring_nf
  have hd : 0 < a+b := by linarith
  have hd' : 1/18 ≤ a'+b' := by linarith [(abs_le.mp hden).1]
  have hd'p : 0 < a'+b' := by linarith
  have hi : (a+b)⁻¹ ≤ 9 := (inv_le_iff_one_le_mul₀ hd).mpr (by linarith)
  have hi' : (a'+b')⁻¹ ≤ 18 := (inv_le_iff_one_le_mul₀ hd'p).mpr (by linarith)
  have hnum : |a'/(a'+b')-a/(a+b)| ≤
      ε*(a'+b')⁻¹ + 2*ε*(a'+b')⁻¹*(a+b)⁻¹ := by
    have heq : a'/(a'+b')-a/(a+b) =
        (a'-a)*(a'+b')⁻¹ + a*((a+b)-(a'+b'))*(a'+b')⁻¹*(a+b)⁻¹ := by
      field_simp [hd.ne',hd'p.ne']
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha,
      abs_of_pos (inv_pos.mpr hd), abs_of_pos (inv_pos.mpr hd'p),
      abs_sub_comm (a+b) (a'+b')]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hea (inv_nonneg.mpr hd'p.le)
    · apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hd.le)
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hd'p.le)
      calc
        _ ≤ 1*(2*ε) := mul_le_mul ha1 hden (abs_nonneg _) (by norm_num)
        _ = 2*ε := one_mul _
  apply hnum.trans
  calc
    _ ≤ ε*18 + 2*ε*18*9 := by gcongr
    _ = 342*ε := by ring

theorem approximation_error (p : ℕ) (q : ℚ) :
    |(approximate p q:ℝ)-Real.smoothTransition (q:ℝ)| ≤ ((p:ℝ)+1)⁻¹ := by
  let ε : ℝ := ((precision p:ℝ)+1)⁻¹
  have hp : (0:ℝ) < (p:ℝ)+1 := by positivity
  have he : 0 ≤ ε := by dsimp [ε]; positivity
  have hesmall : ε ≤ 1/1000 := by
    dsimp [ε,precision]
    push_cast
    apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) p]
  have ha1 : expNegInvGlue (q:ℝ) ≤ 1 := by
    by_cases hq : (q:ℝ) ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hq]; norm_num
    · rw [expNegInvGlue, ite_eq_right hq]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hq)))
  have heb : |(flat (precision p) (1-q):ℝ)-expNegInvGlue (1-(q:ℝ))| ≤ ε := by
    simpa only [Rat.cast_sub, Rat.cast_one] using flat_error (precision p) (1-q)
  have h := quotient_error (expNegInvGlue.nonneg _) ha1
    (transition_denominator_lower (q:ℝ)) he hesmall
    (flat_error (precision p) q) heb
  have hbound : 342*ε ≤ ((p:ℝ)+1)⁻¹ := by
    dsimp [ε,precision]
    push_cast
    apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) p]
  apply (le_trans ?_ hbound)
  simpa only [approximate, Real.smoothTransition, Rat.cast_div, Rat.cast_add,
    Rat.cast_sub, Rat.cast_one] using h

end ContinuumCoulomb.RationalSmoothTransition

end OAI
