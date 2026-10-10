import OAI.NumberTheory.CubicMoment.Estimates.SharpCutoff
import OAI.NumberTheory.CubicGram.Reciprocity
import OAI.NumberTheory.CubicGram.LatticeCounts

namespace OAI

/-!
# Sharp Fourier cutoff for actual prime sums

A fixed integer norm contains at most a conjugate pair of primary primes.
Thus collecting prime coefficients by norm supplies the coefficient bound
needed in the endpoint-kernel argument, without a norm-counting hypothesis.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_eq_or_conjugate_of_norm_eq {p q : Eisenstein}
    (hp : primaryPrime p) (hq : primaryPrime q) (hn : norm p = norm q) :
    p = q ∨ p = conjugate q := by
  have hnat : normNat p = normNat q := by
    exact_mod_cast (show (normNat p : ℝ) = normNat q from by
      rw [normNat_cast,normNat_cast,hn])
  have hd : p ∣ q*conjugate q := by
    rw [← normNat_cast_eq_mul_conjugate, ← hnat, normNat_cast_eq_mul_conjugate]
    exact dvd_mul_right p (conjugate p)
  rcases hp.2.dvd_or_dvd hd with hd | hd
  · exact Or.inl (primary_associated_eq hp.1 hq.1 (hp.2.associated_of_dvd hq.2 hd))
  · exact Or.inr (primary_associated_eq hp.1 (primary_conjugate hq.1)
      (hp.2.associated_of_dvd (primaryPrime_conjugate hq).2 hd))

lemma prime_norm_fiber_card_le_two (P : Finset Eisenstein)
    (hP : ∀ p ∈ P, primaryPrime p) (n : ℤ) :
    (P.filter (fun p => (normNat p : ℤ) = n)).card ≤ 2 := by
  let Q := P.filter (fun p => (normNat p : ℤ) = n)
  by_cases he : Q.Nonempty
  · obtain ⟨q,hq⟩ := he
    have hsub : Q ⊆ {q,conjugate q} := by
      intro p hp
      have hnp : normNat p = normNat q := by
        exact_mod_cast ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
      have hn : norm p = norm q := by rw [← normNat_cast,← normNat_cast,hnp]
      rcases primaryPrime_eq_or_conjugate_of_norm_eq
        (hP p (Finset.mem_filter.mp hp).1) (hP q (Finset.mem_filter.mp hq).1) hn with h | h
      · simp [h]
      · simp [h]
    calc
      Q.card ≤ ({q,conjugate q} : Finset Eisenstein).card := Finset.card_le_card hsub
      _ ≤ ({conjugate q} : Finset Eisenstein).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  · have hQ : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change Q.card ≤ 2
    rw [hQ]
    decide

def collectedPrimeCoefficient (P : Finset Eisenstein) (c : Eisenstein → ℂ) (n : ℤ) : ℂ :=
  ∑ p ∈ P.filter (fun p => (normNat p : ℤ) = n), c p

lemma collectedPrimeCoefficient_bound (P : Finset Eisenstein)
    (hP : ∀ p ∈ P, primaryPrime p) (c : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (n : ℤ) :
    ‖collectedPrimeCoefficient P c n‖ ≤ 2*M := by
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => (normNat p : ℤ) = n), ‖c p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ P.filter (fun p => (normNat p : ℤ) = n), M :=
      Finset.sum_le_sum (fun p hp => hc p (Finset.mem_filter.mp hp).1)
    _ = ((P.filter (fun p => (normNat p : ℤ) = n)).card : ℝ)*M := by simp
    _ ≤ 2*M := mul_le_mul_of_nonneg_right (by
      exact_mod_cast prime_norm_fiber_card_le_two P hP n) hM

/-- An actual prime sum has the claimed endpoint cost after collecting
both conjugates at each integer norm. -/
theorem prime_sharp_interval_sum_error (P : Finset Eisenstein)
    (hP : ∀ p ∈ P, primaryPrime p) (c : Eisenstein → ℂ)
    {X T M : ℝ} (hX : 0 < X) (hT : 0 < T) (hM : 0 ≤ M)
    (hPX : ∀ p ∈ P, norm p ≤ 4*X) (hc : ∀ p ∈ P, ‖c p‖ ≤ M) :
    ‖∑ p ∈ P, c p*sharpIntervalError X T (norm p)‖ ≤
      128*kernelMoment truncationKernel 1*M*(1+X/T) := by
  let S : Finset ℤ := P.image (fun p => (normNat p : ℤ))
  have hf := Finset.sum_fiberwise_of_maps_to (s := P) (t := S)
    (g := fun p => (normNat p : ℤ))
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    (fun p => c p*sharpIntervalError X T (norm p))
  have he : (∑ p ∈ P, c p*sharpIntervalError X T (norm p)) =
      ∑ n ∈ S, collectedPrimeCoefficient P c n*sharpIntervalError X T n := by
    rw [← hf]
    apply Finset.sum_congr rfl
    intro n hn
    rw [collectedPrimeCoefficient,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hn : norm p = (n : ℝ) := by
      rw [← normNat_cast]
      exact_mod_cast (Finset.mem_filter.mp hp).2
    rw [hn]
  have hs : ∀ n ∈ S, 0 < (n : ℝ) ∧ (n : ℝ) ≤ 4*X := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    simp only [Int.cast_natCast,normNat_cast]
    exact ⟨norm_pos_of_ne_zero (hP p hp).2.ne_zero,hPX p hp⟩
  rw [he]
  convert sharp_interval_sum_error hX hT (mul_nonneg (by norm_num) hM) S
    (collectedPrimeCoefficient P c) hs (fun n _ => collectedPrimeCoefficient_bound P hP c hM hc n)
    using 1; ring

/-- The endpoint error for uniformly bounded prime coefficients is
negligible at the Patterson scale for every positive extra height. -/
theorem prime_sharp_interval_error_isLittleO {ρ M : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 5/6)
    (hM : 0 ≤ M) (P : ℝ → Finset Eisenstein) (c : ℝ → Eisenstein → ℂ)
    (hP : ∀ X, 1 ≤ X → ∀ p ∈ P X, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ X, 1 ≤ X → ∀ p ∈ P X, ‖c X p‖ ≤ M) :
    (fun X : ℝ => ∑ p ∈ P X, c X p*
      sharpIntervalError X (X^(1/6+ρ : ℝ)) (norm p)) =o[Filter.atTop] firstMomentScale := by
  apply isLittleO_of_powerSaving hρ
  apply Asymptotics.IsBigO.of_bound (256*kernelMoment truncationKernel 1*M)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have h := prime_sharp_interval_sum_error (P X) (fun p hp => (hP X hX p hp).1)
    (c X) hX0 (Real.rpow_pos_of_pos hX0 (1/6+ρ)) hM (fun p hp => (hP X hX p hp).2)
    (hc X hX)
  have ht := truncationError_le (ε := 0) hX hρ₁
  simp only [Real.rpow_zero,one_mul,sub_zero] at ht
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)]
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ 128*kernelMoment truncationKernel 1*M from by
      exact mul_nonneg (mul_nonneg (by norm_num) (kernelMoment_nonneg _ _)) hM)
  exact h.trans (by convert hm using 1; ring)

end CubicFirstMoment

end

end OAI
