import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights
import OAI.NumberTheory.CubicMoment.Estimates.ModelPartialSummation
import OAI.NumberTheory.CubicGram.IntegerBasis

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

/-- The conductor-dependent error in the published prime number theorem. -/
def heckeExponentialError (c x Q : ℝ) : ℝ :=
  x * (Real.log (x * Q)) ^ 4 *
    Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x)))

private lemma eventually_loglog_small (a b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      a + b * Real.log (Real.log x) ≤ ε * Real.sqrt (Real.log x) := by
  have hlim : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hc : (fun _ : ℝ => a) =o[atTop] (fun x => Real.sqrt (Real.log x)) := by
    apply isLittleO_const_left.mpr
    right
    simpa only [Function.comp_def, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hlim
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    Real.tendsto_log_atTop
  have hl' : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x => Real.sqrt (Real.log x)) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hl
  have h := (hc.add (hl'.const_mul_left b)).def hε
  filter_upwards [h] with x hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx)

/-- Logarithmic conductor growth makes the published exponential error
smaller than any prescribed logarithmic saving, uniformly in the conductor. -/
lemma heckeExponentialError_logSaving {c K A D : ℝ}
    (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ K * (Real.log x) ^ A →
      heckeExponentialError c x Q ≤ 16 * x / (Real.log x) ^ D := by
  have hcond := eventually_loglog_small (Real.log K) A 1 zero_lt_one
  have hdecay := eventually_loglog_small 0 (D + 4) (c / 2) (by positivity)
  filter_upwards [hcond, hdecay, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hcond hdecay hL hx Q hQ hQmax
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL₀ : 0 < Real.log x := Real.log_pos hx
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hlogQ₀ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQ : Real.log Q ≤ Real.sqrt (Real.log x) := by
    have h := Real.log_le_log hQ₀ hQmax
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hL₀ A).ne', Real.log_rpow hL₀] at h
    exact h.trans (by simpa only [one_mul] using hcond)
  have hroot : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hL₀
  have hd : 0 < Real.log Q + Real.sqrt (Real.log x) := by positivity
  have hratio : Real.sqrt (Real.log x) / 2 ≤
      Real.log x / (Real.log Q + Real.sqrt (Real.log x)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Real.sq_sqrt hL₀.le]
  have he₁ : Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x))) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -c * (Real.log x / (Real.log Q + Real.sqrt (Real.log x))) := by ring
      _ ≤ _ := by nlinarith
  have he₂ : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      (Real.log x) ^ (-(D + 4)) := by
    rw [Real.rpow_def_of_pos hL₀]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlogprod : Real.log (x * Q) ≤ 2 * Real.log x := by
    rw [Real.log_mul hx₀.ne' hQ₀.ne']
    have hq := hlogQ.trans (Real.sqrt_le_self_iff.mpr (Or.inr hL))
    linarith
  have hpoly : (Real.log (x * Q)) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
    calc
      _ ≤ (2 * Real.log x) ^ 4 := by
        gcongr
        exact Real.log_nonneg (by nlinarith)
      _ = _ := by ring
  have hpow : (Real.log x) ^ 4 * (Real.log x) ^ (-(D + 4)) =
      1 / (Real.log x) ^ D := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL₀]
    norm_num
    rw [Real.rpow_neg hL₀.le]
  calc
    heckeExponentialError c x Q ≤
        x * (16 * (Real.log x) ^ 4) * (Real.log x) ^ (-(D + 4)) := by
      unfold heckeExponentialError
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly hx₀.le)
        (he₁.trans he₂) (Real.exp_nonneg _) (by positivity)
    _ = 16 * x / (Real.log x) ^ D := by rw [mul_assoc, mul_assoc, hpow]; ring

/-- The prime-power deletion error is also negligible at every fixed
logarithmic scale. -/
lemma sqrt_logSq_logSaving (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * (Real.log x) ^ 2 ≤ x / (Real.log x) ^ D := by
  have h := (isLittleO_log_rpow_rpow_atTop (D + 2)
    (by norm_num : (0 : ℝ) < 1 / 2)).def zero_lt_one
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  have hx₀ : 0 < x := zero_lt_one.trans hx₁
  have hL₀ : 0 < Real.log x := Real.log_pos hx₁
  have hsmall : (Real.log x) ^ (D + 2) ≤ Real.sqrt x := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hL₀.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), one_mul, Real.sqrt_eq_rpow] using hx
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL₀ D)).mpr
  calc
    _ = Real.sqrt x * (Real.log x) ^ (D + 2) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hL₀]
      congr 2
      ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx₀.le

/-- The actual fixed-angular character on the primary generators used by
this development. A nonzero angular index makes it nonprincipal. -/
def angularMixedCubic (ℓ : ℤ) (q₁ q₂ a : Eisenstein) : ℂ :=
  theta ℓ a * mixedCubic q₁ q₂ a

/-- Upper bound for the degree-two analytic conductor: finite conductor
at most `9 N(q₁q₂)`, field discriminant `3`, and gamma shifts `k,k+1`. -/
def angularConductorFactor (ℓ : ℤ) : ℝ :=
  27 * (|(ℓ : ℝ)| / 2 + 3) * (|(ℓ : ℝ)| / 2 + 4)

def angularAnalyticConductor (ℓ : ℤ) (q₁ q₂ : Eisenstein) : ℝ :=
  angularConductorFactor ℓ * norm (q₁ * q₂)

lemma angularConductorFactor_ge_one (ℓ : ℤ) : 1 ≤ angularConductorFactor ℓ := by
  unfold angularConductorFactor
  nlinarith [abs_nonneg (ℓ : ℝ)]

lemma angularAnalyticConductor_ge_one (ℓ : ℤ) {q₁ q₂ : Eisenstein}
    (h₁ : Squarefree q₁) (h₂ : Squarefree q₂) :
    1 ≤ angularAnalyticConductor ℓ q₁ q₂ := by
  have hn : 1 ≤ norm (q₁ * q₂) := by
    rw [← normNat_cast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (mul_ne_zero h₁.ne_zero h₂.ne_zero))
  unfold angularAnalyticConductor
  simpa only [one_mul] using mul_le_mul (angularConductorFactor_ge_one ℓ) hn zero_le_one
    (le_trans zero_le_one (angularConductorFactor_ge_one ℓ))

/-- The logarithmically weighted sum over the actual primary prime elements. -/
def primeChebyshev (ψ : Eisenstein → ℂ) (x : ℝ) : ℂ :=
  primeCutoffSum (fun p => ψ p * (Real.log (norm p) : ℂ)) x

/-- Published fixed-type explicit prime estimate, before any logarithmic
saving is deduced. This is the degree-two, nonexceptional case of
Kaneko--Thorner Theorem 1.2 with Rajan's fixed-type zero-free region.
The displayed second term retains the cost of higher prime powers and
the omitted prime above three. It is an explicit input, not an axiom. -/
def FixedAngularPrimeExplicitEstimate : Prop :=
  ∀ ℓ : ℤ, ℓ ≠ 0 → ∃ B c : ℝ, 0 < B ∧ 0 < c ∧
    ∀ q₁ q₂ : Eisenstein,
      primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ → IsCoprime q₁ q₂ →
      ∀ x : ℝ, 3 ≤ x →
        ‖primeChebyshev (angularMixedCubic ℓ q₁ q₂) x‖ ≤
          B * (heckeExponentialError c x (angularAnalyticConductor ℓ q₁ q₂) +
            Real.sqrt x * (Real.log x) ^ 2)

/-- The logarithmic saving is a deduction from the conductor-dependent
published error, uniform in the small-conductor family. -/
theorem fixedAngular_chebyshev_logSaving (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (_hA : 0 < A) (_hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → ∀ q₁ q₂ : Eisenstein,
        primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ → IsCoprime q₁ q₂ →
        norm (q₁ * q₂) ≤ (Real.log x) ^ A →
        ‖primeChebyshev (angularMixedCubic ℓ q₁ q₂) x‖ ≤ C * x / (Real.log x) ^ D := by
  obtain ⟨B, c, hB, hc, hbound⟩ := hEF ℓ hℓ
  have hK : 0 < angularConductorFactor ℓ := zero_lt_one.trans_le (angularConductorFactor_ge_one ℓ)
  have herr := heckeExponentialError_logSaving (K := angularConductorFactor ℓ)
    (A := A) (D := D) hc hK
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (herr.and (sqrt_logSq_logSaving D))
  refine ⟨17 * B, max X₁ 3, by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hcon
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₃ : 3 ≤ x := (le_max_right _ _).trans hx
  have he := (hX₁ x hx₁).1 (angularAnalyticConductor ℓ q₁ q₂)
    (angularAnalyticConductor_ge_one ℓ hs₁ hs₂)
    (mul_le_mul_of_nonneg_left hcon hK.le)
  calc
    _ ≤ B * (16 * x / (Real.log x) ^ D + x / (Real.log x) ^ D) :=
      (hbound q₁ q₂ h₁ h₂ hs₁ hs₂ hcop x hx₃).trans
        (mul_le_mul_of_nonneg_left (add_le_add he (hX₁ x hx₁).2) hB.le)
    _ = _ := by ring

/-- Partial summation removes the logarithmic prime weight, permitting
smooth weights and norm phases. The derivative cost is retained exactly. -/
theorem weighted_fixedAngular_prime_bound (hEF : FixedAngularPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ a b : ℝ, X₀ ≤ a → a ≤ b → ∀ q₁ q₂ : Eisenstein,
        primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ → IsCoprime q₁ q₂ →
        norm (q₁ * q₂) ≤ (Real.log a) ^ A → ∀ f : ℝ → ℂ,
          (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t => f t / (Real.log t : ℂ)) t) →
          IntegrableOn (deriv (fun t => f t / (Real.log t : ℂ))) (Set.Icc a b) →
          ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
            f (norm p) * angularMixedCubic ℓ q₁ q₂ p‖ ≤
          (C * b / (Real.log a) ^ D) *
            (‖f a / (Real.log a : ℂ)‖ + ‖f b / (Real.log b : ℂ)‖ +
              ∫ t in Set.Ioc a b, ‖deriv (fun t => f t / (Real.log t : ℂ)) t‖) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := fixedAngular_chebyshev_logSaving hEF ℓ hℓ A D hA hD
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro a b ha hab q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hcon f hdiff hderiv
  have ha₁ : 1 < a := hX₀.trans_le ha
  have ha₀ : 0 < a := zero_lt_one.trans ha₁
  have hprefix : ∀ t ∈ Set.Icc a b,
      ‖primeCutoffSum (fun p => angularMixedCubic ℓ q₁ q₂ p * (Real.log (norm p) : ℂ)) t‖ ≤
        C * b / (Real.log a) ^ D := by
    intro t ht
    have ht₀ : 0 < t := ha₀.trans_le ht.1
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha₀ ht.1
    have hcon' : norm (q₁ * q₂) ≤ (Real.log t) ^ A :=
      hcon.trans (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hA.le)
    apply (hbound t (ha.trans ht.1) q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hcon').trans
    exact div_le_div₀ (mul_nonneg hC.le (ht₀.le.trans ht.2))
      (mul_le_mul_of_nonneg_left ht.2 hC.le)
      (Real.rpow_pos_of_pos (Real.log_pos ha₁) D)
      (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hD.le)
  have h := weighted_prime_bound
    (fun p => angularMixedCubic ℓ q₁ q₂ p * (Real.log (norm p) : ℂ))
    (fun t => f t / (Real.log t : ℂ)) ha₀.le hab hdiff hderiv hprefix
  convert h using 2
  apply Finset.sum_congr rfl
  intro p hp
  have hp₁ : 1 < norm p := ha₁.trans (Finset.mem_filter.mp hp).2
  have hlog : (Real.log (norm p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp₁).ne'
  field_simp

/-- Removing any finite set of Euler factors has this exact error; no
implicit identification of ramified or omitted prime values is used. -/
theorem finite_prime_deletion_bound (ψ : Eisenstein → ℂ) (f : ℝ → ℂ)
    (E : Finset Eisenstein) (x : ℝ) :
    ‖(∑ p ∈ (primeCutoff x).filter (fun p => p ∉ E), f (norm p) * ψ p) -
      primeCutoffSum (fun p => f (norm p) * ψ p) x‖ ≤
      ∑ p ∈ (primeCutoff x).filter (fun p => p ∈ E), ‖f (norm p)‖ * ‖ψ p‖ := by
  rw [primeCutoffSum_eq_sum]
  have hsum := Finset.sum_filter_add_sum_filter_not (primeCutoff x)
    (fun p => p ∈ E) (fun p => f (norm p) * ψ p)
  have heq : (∑ p ∈ (primeCutoff x).filter (fun p => p ∉ E), f (norm p) * ψ p) -
      (∑ p ∈ primeCutoff x, f (norm p) * ψ p) =
        -(∑ p ∈ (primeCutoff x).filter (fun p => p ∈ E), f (norm p) * ψ p) := by
    linear_combination hsum
  rw [heq, norm_neg]
  simpa only [norm_mul] using norm_sum_le ((primeCutoff x).filter (fun p => p ∈ E))
    (fun p => f (norm p) * ψ p)

lemma angularMixedCubic_mul {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (ℓ : ℤ) (a b : Eisenstein) :
    angularMixedCubic ℓ q₁ q₂ (a * b) =
      angularMixedCubic ℓ q₁ q₂ a * angularMixedCubic ℓ q₁ q₂ b := by
  simp only [angularMixedCubic, theta_mul, mixedCubic_mul h₁ h₂]
  ring

lemma angularMixedCubic_one {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (ℓ : ℤ) :
    angularMixedCubic ℓ q₁ q₂ 1 = 1 := by
  simp only [angularMixedCubic, theta_one, mixedCubic_one h₁ h₂, one_mul]

lemma angularMixedCubic_prod {ι : Type*} (s : Finset ι) (f : ι → Eisenstein)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) (ℓ : ℤ) :
    angularMixedCubic ℓ q₁ q₂ (∏ i ∈ s, f i) =
      ∏ i ∈ s, angularMixedCubic ℓ q₁ q₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [angularMixedCubic_one h₁ h₂]
  | @insert i s hi ih => simp [hi, angularMixedCubic_mul h₁ h₂, ih]

/-- Independent prime-convolution constituents factor with the same fixed
angular character; all smooth weights remain in the separate factors. -/
theorem independent_angular_prime_tuple_character_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (supports : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) (ℓ : ℤ) :
    (∑ f ∈ Fintype.piFinset supports,
      (∏ i, w i (f i)) * angularMixedCubic ℓ q₁ q₂ (∏ i, f i)) =
      ∏ i, ∑ p ∈ supports i, w i p * angularMixedCubic ℓ q₁ q₂ p := by
  classical
  simp_rw [angularMixedCubic_prod _ _ h₁ h₂, ← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum supports
    (fun i p => w i p * angularMixedCubic ℓ q₁ q₂ p)).symm

/-- Cancellation bounds for the individual prime sums propagate to the
actual independent convolution, with no condition coupling the factors. -/
theorem independent_angular_prime_tuple_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (supports : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) (ℓ : ℤ)
    (H : ι → ℝ)
    (hH : ∀ i, ‖∑ p ∈ supports i, w i p * angularMixedCubic ℓ q₁ q₂ p‖ ≤ H i) :
    ‖∑ f ∈ Fintype.piFinset supports,
      (∏ i, w i (f i)) * angularMixedCubic ℓ q₁ q₂ (∏ i, f i)‖ ≤ ∏ i, H i := by
  rw [independent_angular_prime_tuple_character_sum supports w h₁ h₂ ℓ, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => _root_.norm_nonneg _) (fun i _ => hH i)

/-- Independently prescribed interval of primary primes. -/
def normPrimeInterval (a b : ℝ) : Finset Eisenstein :=
  (primeCutoff b).filter (fun p => a < norm p)

/-- The exact partial-summation cost after removing the logarithmic weight. -/
def primeLogVariation (f : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ‖f a / (Real.log a : ℂ)‖ + ‖f b / (Real.log b : ℂ)‖ +
    ∫ t in Set.Ioc a b, ‖deriv (fun t => f t / (Real.log t : ℂ)) t‖

/-- Actual weighted independent prime convolution, before collecting products. -/
def independentNormPrimeSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (f : ι → ℝ → ℂ) (ψ : Eisenstein → ℂ) : ℂ :=
  ∑ p ∈ Fintype.piFinset (fun i => normPrimeInterval (a i) (b i)),
    (∏ i, f i (norm (p i))) * ψ (∏ i, p i)

/-- Small-conductor cancellation for the actual independently weighted
prime convolution, deduced from the quantitative published input. -/
theorem fixedAngular_prime_convolution_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hEF : FixedAngularPrimeExplicitEstimate) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ q₁ q₂ : Eisenstein,
        primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ → IsCoprime q₁ q₂ →
        ∀ (a b : ι → ℝ) (f : ι → ℝ → ℂ),
          (∀ i, X₀ ≤ a i) → (∀ i, a i ≤ b i) →
          (∀ i, norm (q₁ * q₂) ≤ (Real.log (a i)) ^ A) →
          (∀ i t, t ∈ Set.Icc (a i) (b i) →
            DifferentiableAt ℝ (fun t => f i t / (Real.log t : ℂ)) t) →
          (∀ i, IntegrableOn (deriv (fun t => f i t / (Real.log t : ℂ)))
            (Set.Icc (a i) (b i))) →
          ‖independentNormPrimeSum a b f (angularMixedCubic ℓ q₁ q₂)‖ ≤
            ∏ i, (C * b i / (Real.log (a i)) ^ D) * primeLogVariation (f i) (a i) (b i) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := weighted_fixedAngular_prime_bound hEF ℓ hℓ A D hA hD
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro q₁ q₂ h₁ h₂ hs₁ hs₂ hcop a b f ha hab hcon hdiff hderiv
  let H : ι → ℝ := fun i => (C * b i / (Real.log (a i)) ^ D) * primeLogVariation (f i) (a i) (b i)
  have hH : ∀ i, ‖∑ p ∈ normPrimeInterval (a i) (b i),
      f i (norm p) * angularMixedCubic ℓ q₁ q₂ p‖ ≤ H i := by
    intro i
    exact hbound (a i) (b i) (ha i) (hab i) q₁ q₂ h₁ h₂ hs₁ hs₂ hcop (hcon i)
      (f i) (hdiff i) (hderiv i)
  exact independent_angular_prime_tuple_bound
    (fun i => normPrimeInterval (a i) (b i)) (fun i p => f i (norm p)) h₁ h₂ ℓ H hH

end CubicFirstMoment

end

end OAI
