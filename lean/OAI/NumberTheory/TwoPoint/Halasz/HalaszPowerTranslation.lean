import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovTranslation

namespace OAI

/-! Translation of the complete system on a finite set of coordinates.
The natural-number version uses an integer translation for the reverse
implication, so no truncated subtraction is hidden in the statement. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_finite_power_translate {ι R : Type*} [Fintype ι] [CommSemiring R]
    {k : ℕ} (x y : ι → R)
    (hpower : ∀ j : ℕ, 1≤j → j≤k → ∑ i, x i^j=∑ i, y i^j)
    (c : R) : ∀ j : ℕ, 1≤j → j≤k → ∑ i, (x i+c)^j=∑ i, (y i+c)^j := by
  intro j _ hjk
  have he (z : ι → R) : (∑ i, (z i+c)^j) =
      ∑ m∈range (j+1), (∑ i, z i^m)*c^(j-m)*(Nat.choose j m:R) := by
    simp only [add_pow]
    rw [sum_comm]
    apply sum_congr rfl
    intro m _
    rw [← sum_mul,← sum_mul]
  rw [he,he]
  apply sum_congr rfl
  intro m hm
  have hmj : m≤j := by have := mem_range.mp hm; omega
  have hp : (∑ i, x i^m)=∑ i, y i^m := by
    by_cases hz : m=0
    · simp [hz]
    · exact hpower m (by omega) (hmj.trans hjk)
  rw [hp]

lemma halasz_nat_power_translate_iff {ι : Type*} [Fintype ι] {k : ℕ}
    (x y : ι → ℕ) (a : ℕ) :
    (∀ j : ℕ, 1≤j → j≤k → ∑ i, x i^j=∑ i, y i^j) ↔
      (∀ j : ℕ, 1≤j → j≤k → ∑ i, (x i+a)^j=∑ i, (y i+a)^j) := by
  constructor
  · exact fun h => halasz_finite_power_translate x y h a
  · intro h j hj hjk
    have hz : ∀ j : ℕ, 1≤j → j≤k →
        (∑ i, ((x i:ℤ)+a)^j)=∑ i, ((y i:ℤ)+a)^j := by
      intro j hj hjk
      exact_mod_cast h j hj hjk
    have ht := halasz_finite_power_translate _ _ hz (-(a:ℤ)) j hj hjk
    simp only [add_neg_cancel_right] at ht
    exact_mod_cast ht

lemma halasz_power_vector_eq_iff {ι : Type*} [Fintype ι] {k : ℕ}
    (x y : ι → ℕ) :
    (fun j : Fin k => ∑ i, x i^(j.val+1)) = (fun j : Fin k => ∑ i, y i^(j.val+1)) ↔
      ∀ j : ℕ, 1≤j → j≤k → ∑ i, x i^j=∑ i, y i^j := by
  constructor
  · intro h j hj hjk
    have he := congrFun h (⟨j-1,by omega⟩ : Fin k)
    simpa only [Nat.sub_add_cancel hj] using he
  · intro h
    funext j
    exact h (j.val+1) (by omega) (by omega)

lemma halasz_power_vector_translate_iff {ι : Type*} [Fintype ι] {k : ℕ}
    (x y : ι → ℕ) (a : ℕ) :
    (fun j : Fin k => ∑ i, x i^(j.val+1)) = (fun j : Fin k => ∑ i, y i^(j.val+1)) ↔
      (fun j : Fin k => ∑ i, (x i+a)^(j.val+1)) =
        (fun j : Fin k => ∑ i, (y i+a)^(j.val+1)) := by
  rw [halasz_power_vector_eq_iff,halasz_power_vector_eq_iff]
  exact halasz_nat_power_translate_iff x y a

end TwoPointCorrelations

end OAI
