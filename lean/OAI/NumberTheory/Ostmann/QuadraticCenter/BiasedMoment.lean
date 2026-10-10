import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctQuadraticMoment

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem finite_even_jensen {α : Type*} (A : Finset α) (hA : 0 < A.card)
    (H : α → ℝ) {k : ℕ} (hk : Even k) :
    ((∑ a ∈ A, H a) / A.card) ^ k ≤ (∑ a ∈ A, H a ^ k) / A.card := by
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hw : (∑ a ∈ A, (1 / (A.card : ℝ))) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hj := (hk.convexOn_pow (𝕜 := ℝ)).map_sum_le
    (t := A) (w := fun _ => 1 / (A.card : ℝ)) (p := H)
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hj
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hj

theorem biased_family_even_moment {α ι : Type*}
    (A : Finset α) (P : Finset ι) (hA : 0 < A.card) (hP : 0 < P.card)
    (y : α → ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbias : ∀ p ∈ P, δ ≤ (∑ a ∈ A, y a p) / A.card)
    {k : ℕ} (hk : Even k) :
    (A.card : ℝ) * δ ^ k ≤ ∑ a ∈ A, ((∑ p ∈ P, y a p) / P.card) ^ k := by
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hp : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hmean : δ ≤ (∑ a ∈ A, (∑ p ∈ P, y a p) / P.card) / A.card := by
    rw [le_div_iff₀ ha, ← Finset.sum_div, le_div_iff₀ hp]
    have hs := Finset.sum_le_sum (fun p hp' => (le_div_iff₀ ha).mp (hbias p hp'))
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    rw [Finset.sum_comm]
    nlinarith
  have hpow := pow_le_pow_left₀ hδ hmean k
  have hj := finite_even_jensen A hA (fun a => (∑ p ∈ P, y a p) / P.card) hk
  have h := (le_div_iff₀ ha).mp (hpow.trans hj)
  simpa only [mul_comm] using h

theorem translated_jacobi_biased_moment (A : Finset ℤ) (P : Finset ℕ)
    (hA : 0 < A.card) (hP : 0 < P.card) (ε t : ℕ → ℤ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbias : ∀ p ∈ P,
      δ ≤ (∑ a ∈ A, ((ε p * jacobiSym (a - t p) p : ℤ) : ℝ)) / A.card)
    {k : ℕ} (hk : Even k) :
    (A.card : ℝ) * δ ^ k ≤ ∑ a ∈ A,
      ((∑ p ∈ P, ((ε p * jacobiSym (a - t p) p : ℤ) : ℝ)) / P.card) ^ k :=
  biased_family_even_moment A P hA hP
    (fun a p => ((ε p * jacobiSym (a - t p) p : ℤ) : ℝ)) hδ hbias hk

end Ostmann.QuadraticCenter

end OAI
