import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.AlgebraicGeometry.PlaneCurves.Automorphic

namespace OAI

/-!
# Theta exponents, normalization, and individual terms
-/

section

/-!
# Arithmetic estimates for the normalized theta exponent
-/

noncomputable section

namespace Nagata.W07

/-- Exponent of the theta parameter, with `a = K - U`. -/
def thetaExponent (n a p : ℝ) : ℝ := p * a + n * p * (p - 1) / 2

/-- Distance of the selected exponent from the two endpoints. -/
def thetaMargin (n a : ℝ) : ℝ := min a (n - a)

theorem thetaMargin_pos {n a : ℝ} (ha : 0 < a) (han : a < n) :
    0 < thetaMargin n a := by
  exact lt_min ha (sub_pos.mpr han)

theorem thetaExponent_zero (n a : ℝ) : thetaExponent n a 0 = 0 := by
  simp [thetaExponent]

theorem thetaExponent_positive_index (n a t : ℝ) :
    thetaExponent n a t = t * a + n * t * (t - 1) / 2 := rfl

theorem thetaExponent_negative_index (n a t : ℝ) :
    thetaExponent n a (-t) = t * (n - a) + n * t * (t - 1) / 2 := by
  unfold thetaExponent
  ring

/-- The quadratic bound is valid for real indices, before using integrality. -/
theorem thetaExponent_quadratic_lower (n a p : ℝ) :
    thetaMargin n a * |p| + n * |p| * (|p| - 1) / 2 ≤
      thetaExponent n a p := by
  by_cases hp : 0 ≤ p
  · rw [abs_of_nonneg hp]
    have h := mul_le_mul_of_nonneg_right (min_le_left a (n - a)) hp
    unfold thetaMargin thetaExponent
    nlinarith
  · have hp' : p ≤ 0 := le_of_lt (lt_of_not_ge hp)
    rw [abs_of_nonpos hp']
    have h := mul_le_mul_of_nonneg_right (min_le_right a (n - a))
      (neg_nonneg.mpr hp')
    unfold thetaMargin thetaExponent
    nlinarith

/-- Both positive and negative integer indices have the manuscript's linear bound. -/
theorem thetaExponent_integer_lower {n a : ℝ} (hn : 0 ≤ n) (p : ℤ) :
    thetaMargin n a * |(p : ℝ)| ≤ thetaExponent n a (p : ℝ) := by
  by_cases hp : p = 0
  · subst p
    simp [thetaExponent]
  · have habs : 1 ≤ |(p : ℝ)| := by
      rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero (R := ℝ) hp with h | h
      · rw [abs_of_nonpos (by linarith : (p : ℝ) ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ (p : ℝ))]
        exact h
    have hquad : 0 ≤ n * |(p : ℝ)| * (|(p : ℝ)| - 1) / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hn (abs_nonneg _))
        (sub_nonneg.mpr habs)) (by norm_num)
    exact le_trans (by linarith) (thetaExponent_quadratic_lower n a (p : ℝ))

/-- The exponent is strictly positive away from the constant term. -/
theorem thetaExponent_integer_pos {n a : ℝ} (ha : 0 < a) (han : a < n)
    {p : ℤ} (hp : p ≠ 0) : 0 < thetaExponent n a (p : ℝ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hprod : 0 < thetaMargin n a * |(p : ℝ)| :=
    mul_pos (thetaMargin_pos ha han) (abs_pos.mpr hpR)
  exact lt_of_lt_of_le hprod (thetaExponent_integer_lower (by linarith) p)

/-- The central coefficient is the unique term of exponent zero. -/
theorem thetaExponent_integer_eq_zero_iff {n a : ℝ} (ha : 0 < a)
    (han : a < n) (p : ℤ) : thetaExponent n a (p : ℝ) = 0 ↔ p = 0 := by
  constructor
  · intro he
    by_contra hp
    exact (ne_of_gt (thetaExponent_integer_pos ha han hp)) he
  · intro hp
    subst p
    simp [thetaExponent]

/-- A uniform quadratic lower bound outside the two central indices. -/
theorem thetaExponent_quarter_square_lower {n a p : ℝ}
    (ha : 0 ≤ a) (han : a ≤ n) (hp : 2 ≤ |p|) :
    n / 4 * p ^ 2 ≤ thetaExponent n a p := by
  have hn : 0 ≤ n := le_trans ha han
  have hm : 0 ≤ thetaMargin n a := le_min ha (sub_nonneg.mpr han)
  have h1 := mul_nonneg hm (abs_nonneg p)
  have h2 := mul_nonneg hn
    (mul_nonneg (abs_nonneg p) (sub_nonneg.mpr hp))
  have h3 := thetaExponent_quadratic_lower n a p
  have habs : |p| ^ 2 = p ^ 2 := sq_abs p
  have hnabs : n * |p| ^ 2 = n * p ^ 2 := congrArg (n * ·) habs
  nlinarith

/-- Exact manuscript form, with an integer selected exponent `K`. -/
theorem normalized_theta_exponent_lower {n U : ℝ} {K p : ℤ}
    (hUK : U < (K : ℝ)) (hKU : (K : ℝ) < U + n) :
    min ((K : ℝ) - U) (n - ((K : ℝ) - U)) * |(p : ℝ)| ≤
      (p : ℝ) * ((K : ℝ) - U) + n * (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  exact thetaExponent_integer_lower (by linarith) p

theorem normalized_theta_exponent_pos {n U : ℝ} {K p : ℤ}
    (hUK : U < (K : ℝ)) (hKU : (K : ℝ) < U + n) (hp : p ≠ 0) :
    0 < (p : ℝ) * ((K : ℝ) - U) +
      n * (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  exact thetaExponent_integer_pos (by linarith) (by linarith) hp

end Nagata.W07

end
end

section

noncomputable section

namespace Nagata.W07

/-- Real cast of the exact integer-valued Laurent exponent. -/
theorem laurentExponent_cast_real (n K p : ℤ) :
    (Nagata.W08.laurentExponent n K p : ℝ) =
      (p : ℝ) * (K : ℝ) + (n : ℝ) * (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  have ht : (2 : ℝ) * (Nagata.W08.triangular p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    exact_mod_cast Nagata.W08.two_mul_triangular p
  have ht' : (Nagata.W08.triangular p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    linarith
  simp only [Nagata.W08.laurentExponent, Int.cast_add, Int.cast_mul, ht']
  ring

/-- Cancellation of the normalization and moving-center exponents is exact. -/
theorem normalized_exponent_identity (n K p : ℤ) (σ x₀ : ℝ) :
    -x₀ * (K : ℝ) + (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) +
      x₀ * ((K + n * p : ℤ) : ℝ) =
      thetaExponent (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) (p : ℝ) := by
  rw [laurentExponent_cast_real]
  simp only [Int.cast_add, Int.cast_mul, thetaExponent]
  ring

end Nagata.W07

end
end

section

/-!
# Actual normalized theta summands and their uniform majorant
-/

noncomputable section

namespace Nagata.W07

/-- The actual normalized Laurent summand in logarithmic local coordinates. -/
def normalizedThetaTerm (n a K : ℝ) (ε : ℂ) (τ : ℝ) (p : ℤ) (x : ℂ) : ℂ :=
  ε ^ (-p) * ((τ ^ thetaExponent n a (p : ℝ) : ℝ) : ℂ) *
    Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)

/-- The candidate order-`c` derivative summand, with its explicit frequency factor. -/
def normalizedThetaDerivativeTerm (n a K : ℝ) (ε : ℂ) (τ : ℝ)
    (c : ℕ) (p : ℤ) (x : ℂ) : ℂ :=
  (((K + n * (p : ℝ) : ℝ) : ℂ) ^ c) * normalizedThetaTerm n a K ε τ p x

@[simp] theorem normalizedThetaTerm_zero (n a K : ℝ) (ε : ℂ) (τ : ℝ) (x : ℂ) :
    normalizedThetaTerm n a K ε τ 0 x = Complex.exp ((K : ℂ) * x) := by
  simp [normalizedThetaTerm, thetaExponent]

@[simp] theorem normalizedThetaDerivativeTerm_zero_order
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (p : ℤ) (x : ℂ) :
    normalizedThetaDerivativeTerm n a K ε τ 0 p x =
      normalizedThetaTerm n a K ε τ p x := by
  simp [normalizedThetaDerivativeTerm]

@[simp] theorem normalizedThetaDerivativeTerm_zero_index
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (c : ℕ) (x : ℂ) :
    normalizedThetaDerivativeTerm n a K ε τ c 0 x =
      (K : ℂ) ^ c * Complex.exp ((K : ℂ) * x) := by
  simp [normalizedThetaDerivativeTerm]

theorem natAbs_real (p : ℤ) : (p.natAbs : ℝ) = |(p : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- The real power factor of a normalized summand is bounded by a geometric power. -/
theorem theta_power_le_geometric {n a τ : ℝ} (hn : 0 ≤ n)
    (hτ : 0 < τ) (hτone : τ ≤ 1) (p : ℤ) :
    τ ^ thetaExponent n a (p : ℝ) ≤ (τ ^ thetaMargin n a) ^ p.natAbs := by
  have h := Real.rpow_le_rpow_of_exponent_ge hτ hτone
    (thetaExponent_integer_lower (a := a) hn p)
  calc
    _ ≤ τ ^ (thetaMargin n a * |(p : ℝ)|) := h
    _ = (τ ^ thetaMargin n a) ^ p.natAbs := by
      rw [← natAbs_real p, Real.rpow_mul_natCast hτ.le]

/-- The frequency of either the positive or negative index has the same bound. -/
theorem theta_frequency_le {n : ℝ} (hn : 0 ≤ n) (K : ℝ) (p : ℤ) :
    |K + n * (p : ℝ)| ≤ |K| + n * (p.natAbs : ℝ) := by
  calc
    _ ≤ |K| + |n * (p : ℝ)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_of_nonneg hn, natAbs_real]

/-- Uniform majorant for every explicit derivative summand on the disk `‖x‖≤R`.

This statement includes `p=0`; the series tail uses its restriction to nonzero
indices. The hypotheses on `a` are needed to make `thetaMargin` positive when
taking a parameter limit, but are not needed for this norm inequality itself.
-/
theorem norm_normalizedThetaDerivativeTerm_le {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (c : ℕ) (p : ℤ) :
    ‖normalizedThetaDerivativeTerm n a K ε τ c p x‖ ≤
      Real.exp (|K| * R) * (|K| + n * (p.natAbs : ℝ)) ^ c *
        (Real.exp (n * R) * τ ^ thetaMargin n a) ^ p.natAbs := by
  let A : ℝ := |K| + n * (p.natAbs : ℝ)
  have hA : 0 ≤ A := add_nonneg (abs_nonneg K) (mul_nonneg hn (Nat.cast_nonneg _))
  have hfreq : |K + n * (p : ℝ)| ≤ A := theta_frequency_le hn K p
  have hfreqpow : |K + n * (p : ℝ)| ^ c ≤ A ^ c :=
    pow_le_pow_left₀ (abs_nonneg _) hfreq c
  have hpow := theta_power_le_geometric (a := a) hn hτ hτone p
  have hexp : ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ ≤
      Real.exp (A * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hfreq hR)
  have hexp_split : Real.exp (A * R) =
      Real.exp (|K| * R) * Real.exp (n * R) ^ p.natAbs := by
    have he : A * R = |K| * R + (p.natAbs : ℝ) * (n * R) := by
      dsimp [A]
      ring
    rw [he, Real.exp_add, Real.exp_nat_mul]
  have hnorm : ‖normalizedThetaDerivativeTerm n a K ε τ c p x‖ =
      |K + n * (p : ℝ)| ^ c * τ ^ thetaExponent n a (p : ℝ) *
        ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ := by
    simp only [normalizedThetaDerivativeTerm, normalizedThetaTerm, norm_mul, norm_pow,
      Complex.norm_zpow, hε, one_zpow, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hτ.le _), mul_assoc]
  rw [hnorm]
  calc
    _ ≤ (A ^ c * (τ ^ thetaMargin n a) ^ p.natAbs) * Real.exp (A * R) := by
      apply mul_le_mul
      · exact mul_le_mul hfreqpow hpow (Real.rpow_nonneg hτ.le _) (pow_nonneg hA _)
      · exact hexp
      · exact norm_nonneg _
      · exact mul_nonneg (pow_nonneg hA _) (pow_nonneg (Real.rpow_nonneg hτ.le _) _)
    _ = _ := by
      rw [hexp_split, mul_pow]
      dsimp [A]
      ring

/-- The order-zero bound used to establish convergence of the actual series. -/
theorem norm_normalizedThetaTerm_le {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (p : ℤ) :
    ‖normalizedThetaTerm n a K ε τ p x‖ ≤ Real.exp (|K| * R) *
      (Real.exp (n * R) * τ ^ thetaMargin n a) ^ p.natAbs := by
  simpa using norm_normalizedThetaDerivativeTerm_le
    (a := a) hn hτ hτone hε hR hx 0 p

end Nagata.W07

end
end

section

/-!
# Exact normalization of the Laurent coefficients
-/

noncomputable section

namespace Nagata.W07

/-- Integer powers of a positive real power, viewed in the complex field. -/
theorem complex_rpow_zpow {τ : ℝ} (hτ : 0 ≤ τ) (s : ℝ) (p : ℤ) :
    (((τ ^ s : ℝ) : ℂ) ^ p) = ((τ ^ (s * (p : ℝ)) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_zpow, ← Real.rpow_mul_intCast hτ]

/-- The coefficient chosen in the manuscript, before evaluating at the moving center. -/
def normalizedLaurentCoefficient (τ σ x₀ : ℝ) (ε : ℂ) (n K p : ℤ) : ℂ :=
  ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) * ε ^ (-p) *
    ((τ ^ (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) : ℝ) : ℂ)

@[simp] theorem normalizedLaurentCoefficient_zero
    (τ σ x₀ : ℝ) (ε : ℂ) (n K : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K 0 =
      ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) := by
  simp [normalizedLaurentCoefficient]

/-- The printed real-quadratic form of the chosen coefficient. -/
theorem normalizedLaurentCoefficient_source_formula
    (τ σ x₀ : ℝ) (ε : ℂ) (n K p : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K p =
      ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) * ε ^ (-p) *
        ((τ ^ (-σ * (p : ℝ) + (p : ℝ) * (K : ℝ) +
          (n : ℝ) * (p : ℝ) * ((p : ℝ) - 1) / 2) : ℝ) : ℂ) := by
  unfold normalizedLaurentCoefficient
  rw [laurentExponent_cast_real]
  congr 3
  ring

theorem normalizedLaurentCoefficient_eq_orbitValue {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) (ε : ℂ) (n K p : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K p =
      Nagata.W08.orbitValue (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) p := by
  unfold Nagata.W08.orbitValue
  rw [mul_zpow, complex_rpow_zpow hτ.le, ← Complex.ofReal_zpow, ← Real.rpow_intCast]
  simp only [normalizedLaurentCoefficient, Real.rpow_add hτ, Complex.ofReal_mul,
    Int.cast_neg, mul_neg, neg_mul]
  ring

/-- The explicitly defined chosen coefficients themselves obey the Laurent recurrence. -/
theorem normalizedLaurentCoefficient_add_one {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ε ≠ 0) (n K p : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K (p + 1) =
      ((ε * ((τ ^ σ : ℝ) : ℂ))⁻¹ * (τ : ℂ) ^ (K + n * p)) *
        normalizedLaurentCoefficient τ σ x₀ ε n K p := by
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hτσ : ((τ ^ σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hτ σ).ne'
  simp only [normalizedLaurentCoefficient_eq_orbitValue hτ]
  exact Nagata.W08.orbitValue_add_one (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ))
    hτC (mul_ne_zero hε hτσ) n K _ p

/-- The coefficient is exactly the nonzero starting coefficient propagated
through the Laurent recurrence, with `γ = ε * τ^σ`. -/
theorem normalizedLaurentCoefficient_of_recurrence {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ε ≠ 0) (n K : ℤ) (c : ℤ → ℂ)
    (hc : ∀ L : ℤ, c (L + n) =
      (ε * ((τ ^ σ : ℝ) : ℂ))⁻¹ * (τ : ℂ) ^ L * c L)
    (hstart : c K = ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ)) (p : ℤ) :
    c (K + n * p) = normalizedLaurentCoefficient τ σ x₀ ε n K p := by
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hτσ : ((τ ^ σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hτ σ).ne'
  have hγ : ε * ((τ ^ σ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hε hτσ
  have h := Nagata.W08.laurent_recurrence_all_int (τ : ℂ)
    (ε * ((τ ^ σ : ℝ) : ℂ)) hτC hγ n c hc K p
  change c (K + n * p) = c K * (ε * ((τ ^ σ : ℝ) : ℂ)) ^ (-p) *
    (τ : ℂ) ^ Nagata.W08.laurentExponent n K p at h
  rw [hstart, mul_zpow, complex_rpow_zpow hτ.le] at h
  rw [← Complex.ofReal_zpow, ← Real.rpow_intCast] at h
  rw [h]
  simp only [normalizedLaurentCoefficient, Real.rpow_add hτ, Complex.ofReal_mul,
    Int.cast_neg, mul_neg, neg_mul]
  ring

/-- Evaluating the propagated coefficient at `z₀*exp x`, with `z₀=τ^x₀`,
gives exactly the normalized summand used in the analytic estimates. -/
theorem normalizedLaurentCoefficient_eval {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) (ε x : ℂ) (n K p : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K p *
        (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) ^ (K + n * p) =
      normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x := by
  have hscalar : τ ^ (-x₀ * (K : ℝ)) *
      τ ^ (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) *
        τ ^ (x₀ * ((K + n * p : ℤ) : ℝ)) =
      τ ^ thetaExponent (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) (p : ℝ) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ, normalized_exponent_identity]
  calc
    _ = ε ^ (-p) *
        ((τ ^ (-x₀ * (K : ℝ)) *
          τ ^ (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) *
            τ ^ (x₀ * ((K + n * p : ℤ) : ℝ)) : ℝ) : ℂ) *
          Complex.exp (((K + n * p : ℤ) : ℂ) * x) := by
      simp only [normalizedLaurentCoefficient, mul_zpow, complex_rpow_zpow hτ.le,
        ← Complex.exp_int_mul, Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [hscalar]
      simp only [normalizedThetaTerm, Int.cast_add, Int.cast_mul, Complex.ofReal_add,
        Complex.ofReal_mul, Complex.ofReal_intCast]

/-- Combined recurrence-to-local-summand bridge, without an intermediate model. -/
theorem normalized_recurrence_eval {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ε ≠ 0) (n K : ℤ) (c : ℤ → ℂ)
    (hc : ∀ L : ℤ, c (L + n) =
      (ε * ((τ ^ σ : ℝ) : ℂ))⁻¹ * (τ : ℂ) ^ L * c L)
    (hstart : c K = ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ)) (p : ℤ) (x : ℂ) :
    c (K + n * p) * (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) ^ (K + n * p) =
      normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x := by
  rw [normalizedLaurentCoefficient_of_recurrence hτ σ x₀ hε n K c hc hstart p]
  exact normalizedLaurentCoefficient_eval hτ σ x₀ ε x n K p

/--
The equivalent termwise normalization in logarithmic coordinates.
-/
theorem normalizedThetaTerm_shift {τ : ℝ} (hτ : 0 < τ)
    (n a K x₀ : ℝ) (ε x : ℂ) (p : ℤ) :
    ((τ ^ (-x₀ * K) : ℝ) : ℂ) *
        normalizedThetaTerm n a K ε τ p (((x₀ * Real.log τ : ℝ) : ℂ) + x) =
      normalizedThetaTerm n (a + x₀ * n) K ε τ p x := by
  have hexp : Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) *
      (((x₀ * Real.log τ : ℝ) : ℂ) + x)) =
      ((τ ^ (x₀ * (K + n * (p : ℝ))) : ℝ) : ℂ) *
        Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x) := by
    rw [mul_add, Complex.exp_add, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have hpowers : τ ^ (-x₀ * K) * τ ^ thetaExponent n a (p : ℝ) *
      τ ^ (x₀ * (K + n * (p : ℝ))) =
      τ ^ thetaExponent n (a + x₀ * n) (p : ℝ) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]
    congr 1
    unfold thetaExponent
    ring
  calc
    _ = ε ^ (-p) *
        ((τ ^ (-x₀ * K) * τ ^ thetaExponent n a (p : ℝ) *
          τ ^ (x₀ * (K + n * (p : ℝ))) : ℝ) : ℂ) *
          Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x) := by
      unfold normalizedThetaTerm
      rw [hexp]
      simp only [Complex.ofReal_mul]
      ring
    _ = _ := by rw [hpowers]; rfl

/-- Real rescaling used for the selected starting coefficient is strictly positive. -/
theorem normalization_scalar_pos {τ : ℝ} (hτ : 0 < τ) (x₀ : ℝ) (K : ℤ) :
    0 < τ ^ (-x₀ * (K : ℝ)) := Real.rpow_pos_of_pos hτ _

/-- In particular, the normalized starting coefficient is nonzero in the complex field. -/
theorem normalization_scalar_ne_zero {τ : ℝ} (hτ : 0 < τ) (x₀ : ℝ) (K : ℤ) :
    ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (normalization_scalar_pos hτ x₀ K).ne'

/-- No propagated coefficient in the selected residue class vanishes. -/
theorem normalizedLaurentCoefficient_ne_zero {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ε ≠ 0) (n K p : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K p ≠ 0 := by
  unfold normalizedLaurentCoefficient
  apply mul_ne_zero (mul_ne_zero (normalization_scalar_ne_zero hτ x₀ K)
    (zpow_ne_zero _ hε))
  exact_mod_cast (Real.rpow_pos_of_pos hτ
    (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ))).ne'

end Nagata.W07

end
end

end OAI
