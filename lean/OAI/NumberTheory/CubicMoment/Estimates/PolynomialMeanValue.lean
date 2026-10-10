import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights
import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra

namespace OAI

/-!
# Ordinary mean values after collecting Eisenstein norms

The input `MontgomeryVaughanBound` is the ordinary Dirichlet-polynomial
mean-square theorem of Montgomery--Vaughan, *Hilbert's inequality*,
J. London Math. Soc. (2) 8 (1974), Corollary 3, p. 75, equation (1.11),
in the form explicitly recorded
in the manuscript as `eq:ordinary-mean-value`.

The deductions below collect the actual Eisenstein norms, record their
multiplicity cost, and preserve an arbitrary fixed angular weight and
an arbitrary translated height. These are the ordinary mean-value steps
in `eq:dispersion-height-small` and `eq:angular-completed-height`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Ordinary Dirichlet polynomial, with positive integer frequencies. -/
def integerNormPolynomial (Z : ℕ) (v : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Z, v n * mellinPhase t (n : ℝ)

/-- Precise published input: the constant is independent of the interval,
length, coefficients, and any later translation of the height. -/
def MontgomeryVaughanBound (C : ℝ) : Prop :=
  ∀ (Z : ℕ) (v : ℕ → ℂ) (a b : ℝ), a ≤ b →
    (∫ t in a..b, ‖integerNormPolynomial Z v t‖ ^ 2) ≤
      C * (b - a + Z) * ∑ n ∈ Finset.Icc 1 Z, ‖v n‖ ^ 2

/-- Collection by rational norm, with no change to the coefficients. -/
def normCollectedCoeff (s : Finset Eisenstein) (v : Eisenstein → ℂ) (n : ℕ) : ℂ :=
  ∑ b ∈ s with normNat b = n, v b

/-- Finite polynomial before collecting the equal rational norms. -/
def eisensteinNormPolynomial (s : Finset Eisenstein) (v : Eisenstein → ℂ) (t : ℝ) : ℂ :=
  ∑ b ∈ s, v b * mellinPhase t (norm b)

lemma mellinPhase_add (t u x : ℝ) :
    mellinPhase (t + u) x = mellinPhase t x * mellinPhase u x := by
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma normPolynomial_collected (s : Finset Eisenstein) (v : Eisenstein → ℂ)
    (Z : ℕ) (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z) (t : ℝ) :
    eisensteinNormPolynomial s v t = integerNormPolynomial Z (normCollectedCoeff s v) t := by
  unfold eisensteinNormPolynomial integerNormPolynomial normCollectedCoeff
  rw [← Finset.sum_fiberwise_of_maps_to hs]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  have he := (Finset.mem_filter.mp hb).2
  rw [← normNat_cast b, he]

lemma norm_sum_sq_le_card_mul (s : Finset Eisenstein) (v : Eisenstein → ℂ) :
    ‖∑ b ∈ s, v b‖ ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  have hnorm := norm_sum_le s v
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun b => ‖v b‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcauchy
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))).mpr
    hnorm |>.trans hcauchy

lemma normCollectedCoeff_energy (s : Finset Eisenstein) (v : Eisenstein → ℂ)
    (Z : ℕ) (M : ℝ) (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M) :
    (∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff s v n‖ ^ 2) ≤
      M * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Z, M * ∑ b ∈ s with normNat b = n, ‖v b‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact (norm_sum_sq_le_card_mul _ v).trans
        (mul_le_mul_of_nonneg_right (hM n hn) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hs]

/-- The mean-square bound with the exact multiplicity loss from collecting
Eisenstein norms. -/
theorem eisensteinNormPolynomial_meanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖eisensteinNormPolynomial s v t‖ ^ 2) ≤
      C * (b - a + Z) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  simp_rw [normPolynomial_collected s v Z hs]
  have h := hMV Z (normCollectedCoeff s v) a b hab
  have hfactor : 0 ≤ C * (b - a + Z) := mul_nonneg hC (by positivity)
  calc
    _ ≤ C * (b - a + Z) * (M * ∑ c ∈ s, ‖v c‖ ^ 2) :=
      h.trans (mul_le_mul_of_nonneg_left (normCollectedCoeff_energy s v Z M hs hM) hfactor)
    _ = _ := by ring

/-- A fixed angular character and translated height are coefficient phases;
they do not change the original coefficient energy. -/
theorem fixedAngular_translated_meanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2) ≤
      C * (b - a + Z) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  let w := fun c => v c * theta ℓ c * mellinPhase u (norm c)
  have heq : ∀ t, (∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)) =
      eisensteinNormPolynomial s w t := by
    intro t
    unfold eisensteinNormPolynomial
    apply Finset.sum_congr rfl
    intro c hc
    rw [mellinPhase_add]
    dsimp [w]
    ring
  simp_rw [heq]
  have henergy : (∑ c ∈ s, ‖w c‖ ^ 2) = ∑ c ∈ s, ‖v c‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [w, norm_mul, norm_theta (hzero c hc), mellinPhase_norm, mul_one]
  simpa only [henergy] using eisensteinNormPolynomial_meanSquare hMV hC s w Z M hs hM hab

/-- The normalized two-sided height mean used for the small-conductor
noncube contribution. Both positive and negative height intervals occur. -/
theorem fixedAngular_translated_dyadicMeanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ t in T..2 * T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2) +
     (∫ t in -2 * T..-T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2)) / T ≤
      2 * C * (1 + (Z : ℝ) / T) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have hpos := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := T) (b := 2 * T) (by linarith)
  have hneg := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := -2 * T) (b := -T) (by linarith)
  have hsum := div_le_div_of_nonneg_right (add_le_add hpos hneg) hT.le
  convert hsum using 1
  field_simp
  ring

private lemma continuous_angularNormPolynomial (s : Finset Eisenstein)
    (v : Eisenstein → ℂ) (ℓ : ℤ) (u : ℝ) :
    Continuous (fun t : ℝ => ∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)) := by
  apply continuous_finsetSum
  intro c hc
  apply continuous_const.mul
  unfold mellinPhase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      ((continuous_id.add continuous_const).mul continuous_const)).mul continuous_const)

private lemma interval_integral_sq_le (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  let L := b - a
  let I := ∫ t in a..b, f t
  have hL : 0 < L := sub_pos.mpr hab
  have hfint : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  have hsqint : IntervalIntegrable (fun t => (f t) ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have hlinint := (hfint.const_mul (2 * L * I))
  have hvar : (∫ t in a..b, (L * f t - I) ^ 2) =
      L ^ 2 * (∫ t in a..b, (f t) ^ 2) - L * I ^ 2 := by
    calc
      _ = ∫ t in a..b, (L ^ 2 * (f t) ^ 2 - (2 * L * I) * f t) + I ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = L ^ 2 * (∫ t in a..b, (f t) ^ 2) - (2 * L * I) * I + L * I ^ 2 := by
        rw [intervalIntegral.integral_add ((hsqint.const_mul _).sub hlinint)
          intervalIntegrable_const, intervalIntegral.integral_sub (hsqint.const_mul _) hlinint,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        rfl
      _ = _ := by ring
  have hnonneg : 0 ≤ L ^ 2 * (∫ t in a..b, (f t) ^ 2) - L * I ^ 2 := by
    rw [← hvar]
    exact intervalIntegral.integral_nonneg_of_forall hab.le (fun t => sq_nonneg _)
  change I ^ 2 ≤ L * (∫ t in a..b, (f t) ^ 2)
  nlinarith

/-- Mean absolute size on a height interval, derived from the mean square.
This form retains the exact coefficient energy instead of hiding it in a
big-O constant. -/
theorem fixedAngular_translated_meanAbsolute_sq {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ t in T..2 * T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖) / T) ^ 2 ≤
      C * (1 + (Z : ℝ) / T) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have hcont := (continuous_angularNormPolynomial s v ℓ u).norm
  have hcs := interval_integral_sq_le _ hcont (a := T) (b := 2 * T) (by linarith)
  have hms := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := T) (b := 2 * T) (by linarith)
  have h := hcs.trans (mul_le_mul_of_nonneg_left hms (by linarith))
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg T)
  convert hdiv using 1
  · field_simp
  · field_simp
    ring

/-- The short-polynomial branch of the completed angular height estimate:
length at most `sqrt R * T²` and coefficient energy at most `V` give mean
absolute size at most `sqrt (2 C M V sqrt R T)`. The square-root form is
`O(sqrt V * R^(1/4) * sqrt T)` after the divisor loss is included in `M`. -/
theorem fixedAngular_translated_short_meanAbsolute {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (hM₀ : 0 ≤ M) (ℓ : ℤ) (u : ℝ) {T R V : ℝ}
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hV : 0 ≤ V)
    (henergy : (∑ c ∈ s, ‖v c‖ ^ 2) ≤ V)
    (hlength : (Z : ℝ) ≤ Real.sqrt R * T ^ 2) :
    (∫ t in T..2 * T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖) / T ≤
      Real.sqrt (2 * C * M * V * Real.sqrt R * T) := by
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRroot : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hfactor : 1 + (Z : ℝ) / T ≤ 2 * Real.sqrt R * T := by
    have hz : (Z : ℝ) / T ≤ Real.sqrt R * T := by
      apply (div_le_iff₀ hT₀).mpr
      nlinarith [hlength]
    have hrt : 1 ≤ Real.sqrt R * T := by
      simpa only [one_mul] using mul_le_mul hRroot hT zero_le_one (Real.sqrt_nonneg R)
    linarith
  have hsq := fixedAngular_translated_meanAbsolute_sq hMV hC s v Z M hs hzero hM ℓ u hT₀
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ C * (1 + (Z : ℝ) / T) * M * V := by
      exact hsq.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
    _ = (C * M * V) * (1 + (Z : ℝ) / T) := by ring
    _ ≤ (C * M * V) * (2 * Real.sqrt R * T) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
