import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMomentMean

namespace OAI

/-! # The finite second-moment step in the positive witness probability -/

namespace Ostmann

open scoped BigOperators

theorem finite_second_mean_le_of_even_moment {ι : Type*} (S : Finset ι)
    (f : ι → ℝ) (B : ℝ) (l : ℕ) (hl : 0 < l)
    (hm : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ (2 * l)) ≤ B ^ (2 * l)) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤ B ^ 2 := by
  apply finite_mean_le_of_moment S (fun i => f i ^ 2) (B ^ 2) l (sq_nonneg B) hl
    (fun i _ => sq_nonneg (f i))
  simpa only [pow_mul] using hm

theorem finite_event_second_moment {ι : Type*} (S E : Finset ι) (hES : E ⊆ S)
    (f : ι → ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (hfirst : A ≤ (S.card : ℝ)⁻¹ * (∑ i ∈ E, f i))
    (hsecond : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤ B ^ 2) :
    A ^ 2 ≤ ((S.card : ℝ)⁻¹ * E.card) * B ^ 2 := by
  have hμ : 0 ≤ (S.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcs : (∑ i ∈ E, f i) ^ 2 ≤ (E.card : ℝ) * (∑ i ∈ E, f i ^ 2) := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq E (fun _ => (1 : ℝ)) f)
  have hsums : (∑ i ∈ E, f i ^ 2) ≤ ∑ i ∈ S, f i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hES (fun i _ _ => sq_nonneg (f i))
  calc
    A ^ 2 ≤ ((S.card : ℝ)⁻¹ * (∑ i ∈ E, f i)) ^ 2 := pow_le_pow_left₀ hA hfirst 2
    _ = ((S.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ E, f i) ^ 2 := mul_pow _ _ _
    _ ≤ ((S.card : ℝ)⁻¹) ^ 2 * ((E.card : ℝ) * (∑ i ∈ E, f i ^ 2)) := by gcongr
    _ ≤ ((S.card : ℝ)⁻¹) ^ 2 * ((E.card : ℝ) * (∑ i ∈ S, f i ^ 2)) := by gcongr
    _ = ((S.card : ℝ)⁻¹ * E.card) * ((S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsecond (by positivity)

theorem finite_witness_probability {ι : Type*} (S E : Finset ι) (hES : E ⊆ S)
    (f : ι → ℝ) (K : ℝ) (hK : 1000 ≤ K)
    (hfirst : Real.exp ((3 / 200 : ℝ) * K) / 2 ≤
      (S.card : ℝ)⁻¹ * (∑ i ∈ E, f i))
    (hsecond : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤
      (2 * Real.exp ((103 / 1000 : ℝ) * K)) ^ 2) :
    Real.exp (-K / 5) ≤ (S.card : ℝ)⁻¹ * E.card := by
  have hh := finite_event_second_moment S E hES f
    (Real.exp ((3 / 200 : ℝ) * K) / 2) (2 * Real.exp ((103 / 1000 : ℝ) * K))
    (by positivity) hfirst hsecond
  have hr : Real.exp ((3 / 100 : ℝ) * K) / 16 ≤
      ((S.card : ℝ)⁻¹ * E.card) * Real.exp ((103 / 500 : ℝ) * K) := by
    rw [div_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at hh
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    have h₁ : 2 * ((3 / 200 : ℝ) * K) = (3 / 100 : ℝ) * K := by ring
    have h₂ : 2 * ((103 / 1000 : ℝ) * K) = (103 / 500 : ℝ) * K := by ring
    rw [h₁, h₂] at hh
    nlinarith only [hh]
  have hbound : Real.exp ((-22 / 125 : ℝ) * K) / 16 ≤ (S.card : ℝ)⁻¹ * E.card := by
    have hd := (div_le_iff₀ (Real.exp_pos ((103 / 500 : ℝ) * K))).mpr hr
    have heq : (Real.exp ((3 / 100 : ℝ) * K) / 16) / Real.exp ((103 / 500 : ℝ) * K) =
        Real.exp ((-22 / 125 : ℝ) * K) / 16 := by
      rw [div_right_comm, ← Real.exp_sub]
      congr 2
      ring
    simpa only [heq] using hd
  have h16 : (16 : ℝ) ≤ Real.exp ((3 / 125 : ℝ) * K) := by
    have ht := Real.add_one_le_exp ((3 / 125 : ℝ) * K)
    linarith
  apply le_trans _ hbound
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  calc
    Real.exp (-K / 5) * 16 ≤ Real.exp (-K / 5) * Real.exp ((3 / 125 : ℝ) * K) := by gcongr
    _ = Real.exp ((-22 / 125 : ℝ) * K) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
