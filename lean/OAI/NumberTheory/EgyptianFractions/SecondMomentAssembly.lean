import OAI.NumberTheory.EgyptianFractions.HammingException

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Finite weighted pair correlation, with no probability-library dependency. -/
def weightedCorrelation {Ω I : Type*} [Fintype Ω]
    (w : Ω → ℝ) (z : Ω → I → ℂ) (i j : I) : ℂ :=
  ∑ ω, (w ω : ℂ) * (z ω i * star (z ω j))

theorem norm_sum_sq_eq_sum_pair {I : Type*} [Fintype I] (z : I → ℂ) :
    ‖∑ i, z i‖ ^ 2 = ∑ ij : I × I, (z ij.1 * star (z ij.2)).re := by
  rw [Fintype.sum_prod_type]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

theorem weighted_second_moment_identity {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (z : Ω → I → ℂ) :
    (∑ ω, w ω * ‖∑ i, z ω i‖ ^ 2) =
      ∑ ij : I × I, (weightedCorrelation w z ij.1 ij.2).re := by
  have hreal (a : ℝ) (b : ℂ) : ((a : ℂ) * b).re = a * b.re := by simp
  simp only [weightedCorrelation, Complex.re_sum, hreal]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← norm_sum_sq_eq_sum_pair]

/-- Exceptional pairs cost their cardinality; all other pairs cost the common
correlation bound. The assumptions deliberately expose the exact analytic interface. -/
theorem second_moment_exceptional_bound {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (z : Ω → I → ℂ) (E : Finset (I × I)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hall : ∀ i j, ‖weightedCorrelation w z i j‖ ≤ 1)
    (hgood : ∀ i j, (i, j) ∉ E → ‖weightedCorrelation w z i j‖ ≤ δ) :
    (∑ ω, w ω * ‖∑ i, z ω i‖ ^ 2) ≤
      (E.card : ℝ) + (Fintype.card I : ℝ) ^ 2 * δ := by
  classical
  rw [weighted_second_moment_identity]
  calc
    (∑ ij : I × I, (weightedCorrelation w z ij.1 ij.2).re) ≤
        ∑ ij : I × I, ((if ij ∈ E then 1 else 0) + δ : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      by_cases h : ij ∈ E
      · simp only [ite_eq_left h]
        exact (Complex.re_le_norm _).trans ((hall _ _).trans (by linarith))
      · simp only [ite_eq_right h, zero_add]
        exact (Complex.re_le_norm _).trans (hgood _ _ h)
    _ = (E.card : ℝ) + (Fintype.card I : ℝ) ^ 2 * δ := by
      simp [Finset.sum_add_distrib, Fintype.card_prod, pow_two]

/-- Correlations of unit-bounded variables under nonnegative weights of mass one
are themselves bounded by one. -/
theorem weightedCorrelation_norm_le_one {Ω I : Type*} [Fintype Ω]
    (w : Ω → ℝ) (z : Ω → I → ℂ) (hw : ∀ ω, 0 ≤ w ω)
    (hmass : ∑ ω, w ω = 1) (hz : ∀ ω i, ‖z ω i‖ ≤ 1) (i j : I) :
    ‖weightedCorrelation w z i j‖ ≤ 1 := by
  calc
    ‖weightedCorrelation w z i j‖ ≤
        ∑ ω, ‖(w ω : ℂ) * (z ω i * star (z ω j))‖ := norm_sum_le _ _
    _ ≤ ∑ ω, w ω := by
      apply Finset.sum_le_sum
      intro ω hω
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw ω)]
      have hprod : ‖z ω i‖ * ‖z ω j‖ ≤ 1 := by
        nlinarith [norm_nonneg (z ω i), norm_nonneg (z ω j), hz ω i, hz ω j]
      nlinarith [hw ω]
    _ = 1 := hmass

/-- The random-products second-moment reduction: after the separated-pair
correlation estimate, the only loss is the exponentially small Hamming exception. -/
theorem boolean_second_moment_bound {Ω : Type*} [Fintype Ω] (m : ℕ)
    (w : Ω → ℝ) (z : Ω → (Fin m → Bool) → ℂ)
    (hw : ∀ ω, 0 ≤ w ω) (hmass : ∑ ω, w ω = 1)
    (hz : ∀ ω i, ‖z ω i‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ i j, (m : ℝ) / 4 ≤ (hammingDist i j : ℝ) →
      ‖weightedCorrelation w z i j‖ ≤ δ) :
    (∑ ω, w ω * ‖∑ i, z ω i‖ ^ 2) / (4 : ℝ) ^ m ≤
      Real.exp (-(m : ℝ) / 16) + δ := by
  classical
  let E := Finset.univ.filter (fun ij : (Fin m → Bool) × (Fin m → Bool) =>
    (hammingDist ij.1 ij.2 : ℝ) < (m : ℝ) / 4)
  have hexc : (E.card : ℝ) ≤ (4 : ℝ) ^ m * Real.exp (-(m : ℝ) / 16) :=
    hamming_exception_count m
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) ^ 2 = (4 : ℝ) ^ m := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, pow_two]
    rw [← mul_pow]
    norm_num
  have hbound := second_moment_exceptional_bound w z E δ hδ
    (weightedCorrelation_norm_le_one w z hw hmass hz)
    (fun i j hij => hgood i j (by
      simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hij))
  rw [hcard] at hbound
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ m)).2
  nlinarith

/-- Averaging over exposed variables costs at most the mass of bad exposures
plus the bound that holds uniformly on the good exposures. -/
theorem weighted_exposure_bound {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (f : Ω → ℂ) (B : Finset Ω) (a b : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hmass : ∑ ω, w ω = 1)
    (ha : 0 ≤ a) (hbad : ∑ ω ∈ B, w ω ≤ b)
    (hall : ∀ ω, ‖f ω‖ ≤ 1) (hgood : ∀ ω, ω ∉ B → ‖f ω‖ ≤ a) :
    ‖∑ ω, (w ω : ℂ) * f ω‖ ≤ a + b := by
  classical
  calc
    ‖∑ ω, (w ω : ℂ) * f ω‖ ≤ ∑ ω, ‖(w ω : ℂ) * f ω‖ := norm_sum_le _ _
    _ ≤ ∑ ω, (w ω * a + if ω ∈ B then w ω else 0) := by
      apply Finset.sum_le_sum
      intro ω hω
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw ω)]
      by_cases hb : ω ∈ B
      · simp only [ite_eq_left hb]
        nlinarith [hall ω, hw ω]
      · simp only [ite_eq_right hb, add_zero]
        exact mul_le_mul_of_nonneg_left (hgood ω hb) (hw ω)
    _ = a + ∑ ω ∈ B, w ω := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul]
      simp
    _ ≤ a + b := by linarith

/-- The numerical absorption at the end of the random-products argument. -/
theorem random_second_moment_absorption (m V : ℝ) (hlarge : 50 ≤ min m V) :
    Real.exp (-m / 16) + Real.exp (-V / 20) + Real.exp (-V / 5) ≤
      Real.exp (-min m V / 100) := by
  let w := min m V
  have hwm : w ≤ m := min_le_left _ _
  have hwV : w ≤ V := min_le_right _ _
  have hw : 50 ≤ w := hlarge
  have h1 : Real.exp (-m / 16) ≤ Real.exp (-w / 20) := by
    apply Real.exp_le_exp.mpr
    dsimp [w] at *
    nlinarith
  have h2 : Real.exp (-V / 20) ≤ Real.exp (-w / 20) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h3 : Real.exp (-V / 5) ≤ Real.exp (-w / 20) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlog3 : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have habsorb : 3 * Real.exp (-w / 20) ≤ Real.exp (-w / 100) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  exact (by linarith : Real.exp (-m / 16) + Real.exp (-V / 20) +
    Real.exp (-V / 5) ≤ 3 * Real.exp (-w / 20)).trans habsorb

/-- Final second-moment estimate once the good/bad pair-exposure estimates
are supplied. All constants agree with the random-products lemma. -/
theorem boolean_random_second_moment_bound {Ω : Type*} [Fintype Ω] (m : ℕ) (V : ℝ)
    (w : Ω → ℝ) (z : Ω → (Fin m → Bool) → ℂ)
    (hw : ∀ ω, 0 ≤ w ω) (hmass : ∑ ω, w ω = 1)
    (hz : ∀ ω i, ‖z ω i‖ ≤ 1) (hlarge : 50 ≤ min (m : ℝ) V)
    (hgood : ∀ i j, (m : ℝ) / 4 ≤ (hammingDist i j : ℝ) →
      ‖weightedCorrelation w z i j‖ ≤ Real.exp (-V / 20) + Real.exp (-V / 5)) :
    (∑ ω, w ω * ‖∑ i, z ω i‖ ^ 2) / (4 : ℝ) ^ m ≤
      Real.exp (-min (m : ℝ) V / 100) := by
  have h := boolean_second_moment_bound m w z hw hmass hz
    (Real.exp (-V / 20) + Real.exp (-V / 5)) (by positivity) hgood
  have hfinal := random_second_moment_absorption (m : ℝ) V hlarge
  exact h.trans (by simpa only [add_assoc] using hfinal)

end Problem337

end

end OAI
