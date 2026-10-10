import PrimeNumberTheoremAnd.Erdos970.MertensClassical
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open Real Finset MeasureTheory
open scoped BigOperators

noncomputable def primeLogWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / n else 0

lemma primeLogWeight_nonneg (n : ℕ) : 0 ≤ primeLogWeight n := by
  unfold primeLogWeight
  split_ifs with hn
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn.one_le)) (Nat.cast_nonneg _)
  · rfl

lemma sum_primeLogWeight (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n) =
      ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp only [primeLogWeight, Nat.not_prime_zero, ↓reduceIte, zero_add]
  rw [← Finset.sum_filter]

lemma sum_primeLogWeight_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n) ≤
      Real.log x + (Real.log 4 + 4) := by
  have h := (abs_le.mp (Erdos970.Mertens.sum_log_prime_div_eq_log hx)).2
  rw [sum_primeLogWeight]
  linarith

noncomputable def primeLogReciprocalConstant : ℝ :=
  1 + (Real.log 4 + 4) / Real.log 2

lemma primeLogReciprocalConstant_pos : 0 < primeLogReciprocalConstant := by
  unfold primeLogReciprocalConstant
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

lemma sum_primeLogWeight_le_mul_log {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n) ≤
      primeLogReciprocalConstant * Real.log x := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 + 4 := by positivity
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h := mul_le_mul_of_nonneg_left hl (div_nonneg h4 h2.le)
  have he : (Real.log 4 + 4) / Real.log 2 * Real.log 2 = Real.log 4 + 4 :=
    div_mul_cancel₀ _ h2.ne'
  rw [he] at h
  have hs := sum_primeLogWeight_le (by linarith : 1 ≤ x)
  unfold primeLogReciprocalConstant
  nlinarith

noncomputable def inverseLogSquare (x : ℝ) : ℝ := (Real.log x)⁻¹ ^ 2

lemma inverseLogSquare_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt inverseLogSquare (-2 / (x * Real.log x ^ 3)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have h := ((Real.hasDerivAt_log hx0).inv hl).pow 2
  norm_num only [Pi.inv_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one] at h
  convert h using 1 <;> first | rfl | field_simp [hx0, hl]

lemma inverseLogSquare_deriv {x : ℝ} (hx : 1 < x) :
    deriv inverseLogSquare x = -2 / (x * Real.log x ^ 3) :=
  (inverseLogSquare_hasDerivAt hx).deriv

lemma inverseLogSquare_deriv_integrable {x : ℝ} :
    IntegrableOn (deriv inverseLogSquare) (Set.Icc 2 x) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.congr (f := fun t : ℝ => -2 / (t * Real.log t ^ 3))
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have htl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    exact (continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log ht0).pow 3))
        (mul_ne_zero ht0 (pow_ne_zero 3 htl))).continuousWithinAt
  · intro t ht
    exact inverseLogSquare_deriv (by linarith [ht.1])

lemma sum_primeLog_inverseLogSquare (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, inverseLogSquare n * primeLogWeight n) =
      ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
        1 / ((p : ℝ) * Real.log p) := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp only [primeLogWeight, Nat.not_prime_zero, ↓reduceIte, mul_zero, zero_add]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with hprime
  · have hl : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hprime.one_lt)).ne'
    unfold inverseLogSquare
    field_simp
  · exact mul_zero _

noncomputable def primeLogReciprocalMajorant (t : ℝ) : ℝ :=
  (2 * primeLogReciprocalConstant) / (t * Real.log t ^ 2)

lemma primeLogReciprocalMajorant_nonneg {t : ℝ} (ht : 2 < t) :
    0 ≤ primeLogReciprocalMajorant t := by
  unfold primeLogReciprocalMajorant
  have hK := primeLogReciprocalConstant_pos
  exact div_nonneg (by positivity)
    (mul_nonneg (by linarith) (sq_nonneg _))

lemma primeLogReciprocalMajorant_integrable :
    IntegrableOn primeLogReciprocalMajorant (Set.Ioi 2) := by
  unfold primeLogReciprocalMajorant
  simpa only [IntegrableOn, div_eq_mul_inv, mul_inv, mul_assoc] using
    (integrableOn_inv_div_log_sq_Ioi (c := 2) (by norm_num)).const_mul
      (2 * primeLogReciprocalConstant)

lemma primeLogReciprocal_abel_bound {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
      1 / ((p : ℝ) * Real.log p)) ≤
      primeLogReciprocalConstant / Real.log 2 +
        ∫ t in Set.Ioi 2, primeLogReciprocalMajorant t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : x ≠ 0 := by linarith
  have hK := primeLogReciprocalConstant_pos
  have habel := sum_mul_eq_sub_integral_mul₁ primeLogWeight
    (by simp [primeLogWeight]) (by simp [primeLogWeight]) x
    (fun t ht => (inverseLogSquare_hasDerivAt (by linarith [ht.1])).differentiableAt)
    (inverseLogSquare_deriv_integrable (x := x))
  rw [sum_primeLog_inverseLogSquare] at habel
  have hboundary : inverseLogSquare x * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n) ≤
      primeLogReciprocalConstant / Real.log 2 := by
    calc
      _ ≤ inverseLogSquare x * (primeLogReciprocalConstant * Real.log x) :=
        mul_le_mul_of_nonneg_left (sum_primeLogWeight_le_mul_log hx) (sq_nonneg _)
      _ = primeLogReciprocalConstant / Real.log x := by
        unfold inverseLogSquare
        field_simp [hlogx.ne']
      _ ≤ _ := div_le_div_of_nonneg_left hK.le hlog2
        (Real.log_le_log (by norm_num) hx)
  have hpoint : ∀ t ∈ Set.Ioc (2 : ℝ) x,
      -(deriv inverseLogSquare t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeLogWeight n) ≤
        primeLogReciprocalMajorant t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    rw [inverseLogSquare_deriv (by linarith [ht.1])]
    calc
      _ = (2 / (t * Real.log t ^ 3)) *
          (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeLogWeight n) := by ring
      _ ≤ (2 / (t * Real.log t ^ 3)) *
          (primeLogReciprocalConstant * Real.log t) :=
        mul_le_mul_of_nonneg_left (sum_primeLogWeight_le_mul_log ht.1.le) (by positivity)
      _ = primeLogReciprocalMajorant t := by
        unfold primeLogReciprocalMajorant
        field_simp [ht0.ne', hlt.ne']
  have hlocal := (integrableOn_mul_sum_Icc primeLogWeight (m := 0) (by norm_num : (0 : ℝ) ≤ 2)
    (inverseLogSquare_deriv_integrable (x := x))).mono_set Set.Ioc_subset_Icc_self
  have hmono := setIntegral_mono_on hlocal.neg
    (primeLogReciprocalMajorant_integrable.mono_set Set.Ioc_subset_Ioi_self)
    measurableSet_Ioc hpoint
  have hinc : (∫ t in Set.Ioc (2 : ℝ) x, primeLogReciprocalMajorant t) ≤
      ∫ t in Set.Ioi 2, primeLogReciprocalMajorant t := by
    apply setIntegral_mono_set primeLogReciprocalMajorant_integrable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact primeLogReciprocalMajorant_nonneg ht
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  simp only [Pi.neg_apply] at hmono
  rw [integral_neg] at hmono
  rw [habel]
  linarith

theorem prime_log_reciprocal_sum_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      (∑ p ∈ (Finset.Ioc 0 Q).filter Nat.Prime,
        1 / ((p : ℝ) * Real.log p)) ≤ C := by
  let C : ℝ := primeLogReciprocalConstant / Real.log 2 +
    ∫ t in Set.Ioi 2, primeLogReciprocalMajorant t
  have hI : 0 ≤ ∫ t in Set.Ioi 2, primeLogReciprocalMajorant t :=
    setIntegral_nonneg measurableSet_Ioi (fun t ht => primeLogReciprocalMajorant_nonneg ht)
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg
      (div_pos primeLogReciprocalConstant_pos (Real.log_pos (by norm_num))) hI
  refine ⟨C, hC, fun Q => ?_⟩
  by_cases hQ : 2 ≤ Q
  · simpa only [Nat.floor_natCast] using
      (primeLogReciprocal_abel_bound (by exact_mod_cast hQ : (2 : ℝ) ≤ Q))
  · have he : (Finset.Ioc 0 Q).filter Nat.Prime = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hm := Finset.mem_filter.mp hp
      have hple := (Finset.mem_Ioc.mp hm.1).2
      have hp2 := hm.2.two_le
      omega
    rw [he, Finset.sum_empty]
    exact hC.le

end Ostmann.Preliminaries

end OAI
