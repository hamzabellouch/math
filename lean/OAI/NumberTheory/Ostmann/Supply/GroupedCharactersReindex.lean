import OAI.NumberTheory.Ostmann.Supply.GroupedCharacters

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset
open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def groupedCoefficient (s : Finset α) (e : α → β) (c : α → ℂ) (χ : β) : ℂ :=
  ∑ i ∈ s, if e i = χ then c i else 0

omit [DecidableEq α] in
theorem groupedCoefficient_image (s : Finset α) (e : α → β) (c : α → ℂ)
    (he : Set.InjOn e (s : Set α)) {i : α} (hi : i ∈ s) :
    groupedCoefficient s e c (e i) = c i := by
  unfold groupedCoefficient
  rw [sum_eq_single i]
  · simp
  · intro j hj hji
    exact ite_eq_right (fun h => hji (he hj hi h))
  · exact fun hn => (hn hi).elim

omit [DecidableEq α] in
theorem groupedCoefficient_not_mem (s : Finset α) (e : α → β) (c : α → ℂ)
    {χ : β} (hχ : χ ∉ s.image e) : groupedCoefficient s e c χ = 0 := by
  apply sum_eq_zero
  intro i hi
  exact ite_eq_right (fun he => hχ (mem_image.mpr ⟨i, hi, he⟩))

omit [DecidableEq α] in
theorem norm_groupedCoefficient_le (s : Finset α) (e : α → β) (c : α → ℂ)
    (he : Set.InjOn e (s : Set α)) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ i ∈ s, ‖c i‖ ≤ M) (χ : β) : ‖groupedCoefficient s e c χ‖ ≤ M := by
  by_cases hχ : χ ∈ s.image e
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hχ
    rw [groupedCoefficient_image s e c he hi]
    exact hc i hi
  · rw [groupedCoefficient_not_mem s e c hχ, norm_zero]
    exact hM

omit [DecidableEq α] in
theorem grouped_sum (s : Finset α) (e : α → β) (c : α → ℂ)
    (he : Set.InjOn e (s : Set α)) (f : β → ℂ) :
    (∑ χ ∈ s.image e, groupedCoefficient s e c χ * f χ) =
      ∑ i ∈ s, c i * f (e i) := by
  rw [sum_image he]
  apply sum_congr rfl
  intro i hi
  rw [groupedCoefficient_image s e c he hi]

theorem prime_not_dvd_coordinateProduct {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ s, (p i).Prime) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hne : ∀ i ∈ s, p i ≠ ℓ) : ¬ℓ ∣ ∏ i ∈ s, p i := by
  intro hd
  obtain ⟨i, hi, hdiv⟩ := ((Nat.prime_iff.mp hℓ).dvd_finsetProd_iff p).mp hd
  exact hne i hi ((Nat.prime_dvd_prime_iff_eq hℓ (hp i hi)).mp hdiv).symm

end Ostmann.Supply.GroupedCharacters

end

end OAI
